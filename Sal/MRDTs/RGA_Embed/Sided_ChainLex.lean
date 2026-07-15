import Sal.MRDTs.RGA_Embed.RGA_Embed_ChainLex

/-!
# The sided chain-lex kernel — two-sidedness as a parameter (task #83)

Design: `whiteboard/sided-embed-design-note.md`; Python validation:
`whiteboard/litmus/embed_sided.py` (battery clean, L19 flips under the
Fugue policy, all-R fragment lockstep-exact with the one-sided embed).

Chains become sequences of `(side, delta)` entries and the display rule
generalizes from the prefix rule to the in-order rule: L-extensions,
then the node, then R-extensions. The **marker formalization** makes
this plain lexicographic comparison again — a node's sort key is its
coordinate followed by the terminator `3`, with symbol bands

    R-block symbols {1,2}  <  marker 3  <  L-block symbols {4,5}

and the L band written in the **complemented** code (order-reversing
prefix-free at identical lengths), realizing the mirrored L-sibling
order. The one-sided design is the L-uninhabited fragment: its existing
`key = map sym ++ [3]` is literally this construction, which is why the
`keyLt` machinery below is reused unchanged.

This file is the sided analogue of the chain-lex core: the display
relation `schainBefore` (in-order rule), its totality, and the **sided
marker theorem** `sdisplay_iff_schainBefore` — display comparison of
sided coordinates is exactly the in-order rule.
-/

namespace Sal.EmbedRGA

/-! ## Sided chains -/

inductive Side : Type where
  | R
  | L
deriving DecidableEq

/-- A chain entry: side and (positive) timestamp delta. -/
abbrev SEntry : Type := Side × ℕ

abbrev SChain : Type := List SEntry

@[simp] def PosSChain (ch : SChain) : Prop := ∀ e ∈ ch, 1 ≤ e.2

/-! ## The sided symbol alphabet -/

/-- R-band symbols. -/
def symR (b : Bool) : ℕ := if b then 2 else 1

/-- L-band symbols. -/
def symL (b : Bool) : ℕ := if b then 5 else 4

/-- Bitwise complement: the order-reversing twin of a code, at identical
lengths, prefix-freedom preserved. -/
def compl (w : List Bool) : List Bool := w.map (!·)

/-- The symbol block of one chain entry: R-entries carry the code in the
R band; L-entries carry the *complemented* code in the L band (the
mirror). -/
def sBlock (Γ : OrderedPrefixCode) : SEntry → List ℕ
  | (Side.R, d) => (Γ.enc d).map symR
  | (Side.L, d) => (compl (Γ.enc d)).map symL

/-- The sided coordinate: concatenated blocks along the chain. -/
def sidedCoordOf (Γ : OrderedPrefixCode) : SChain → List ℕ
  | [] => []
  | e :: ch => sBlock Γ e ++ sidedCoordOf Γ ch

theorem sidedCoordOf_append (Γ : OrderedPrefixCode) (c1 c2 : SChain) :
    sidedCoordOf Γ (c1 ++ c2) =
      sidedCoordOf Γ c1 ++ sidedCoordOf Γ c2 := by
  induction c1 with
  | nil => simp [sidedCoordOf]
  | cons e es ih => simp [sidedCoordOf, ih]

/-- The sort key: coordinate plus the marker. -/
def sKey (c : List ℕ) : List ℕ := c ++ [3]

/-! ## Band arithmetic -/

theorem symR_lt_three (b : Bool) : symR b < 3 := by
  cases b <;> simp [symR]

theorem three_lt_symL (b : Bool) : 3 < symL b := by
  cases b <;> simp [symL]

theorem symR_lt_symL (b b' : Bool) : symR b < symL b' := by
  cases b <;> cases b' <;> simp [symR, symL]

theorem sBlock_ne_nil (Γ : OrderedPrefixCode) {e : SEntry}
    (he : 1 ≤ e.2) : sBlock Γ e ≠ [] := by
  obtain ⟨sd, d⟩ := e
  have hne := enc_ne_nil Γ (show 1 ≤ d from he)
  cases sd <;> simp [sBlock, compl, hne]

/-! ## The in-order display rule -/

/-- Divergence order between two distinct entries at a shared anchor:
among R-siblings the newer displays first (adjacent to the node from
below), among L-siblings the older displays first (the newer sits
adjacent to the node from above), and every L-entry displays before
every R-entry (L-subtrees precede the node precede R-subtrees). -/
def sEntryBefore : SEntry → SEntry → Prop
  | (Side.R, d), (Side.R, e) => e < d
  | (Side.L, d), (Side.L, e) => d < e
  | (Side.L, _), (Side.R, _) => True
  | (Side.R, _), (Side.L, _) => False

/-- The in-order rule: L-extensions before the node, the node before its
R-extensions, divergences by `sEntryBefore`. -/
inductive schainBefore : SChain → SChain → Prop where
  | extL (ch : SChain) (d : ℕ) (rest : SChain) :
      schainBefore (ch ++ (Side.L, d) :: rest) ch
  | extR (ch : SChain) (d : ℕ) (rest : SChain) :
      schainBefore ch (ch ++ (Side.R, d) :: rest)
  | diverge (q : SChain) (e1 e2 : SEntry) (c1 c2 : SChain) :
      sEntryBefore e1 e2 →
      schainBefore (q ++ e1 :: c1) (q ++ e2 :: c2)

theorem schainBefore_cons (x : SEntry) {c1 c2 : SChain}
    (h : schainBefore c1 c2) :
    schainBefore (x :: c1) (x :: c2) := by
  cases h with
  | extL ch d rest => exact schainBefore.extL (x :: c2) d rest
  | extR ch d rest => exact schainBefore.extR (x :: c1) d rest
  | diverge q e1 e2 t1 t2 hlt =>
      exact schainBefore.diverge (x :: q) e1 e2 t1 t2 hlt

theorem sEntryBefore_total {e1 e2 : SEntry} (hne : e1 ≠ e2) :
    sEntryBefore e1 e2 ∨ sEntryBefore e2 e1 := by
  obtain ⟨s1, d1⟩ := e1
  obtain ⟨s2, d2⟩ := e2
  cases s1 <;> cases s2
  · -- R R
    rcases Nat.lt_trichotomy d1 d2 with h | rfl | h
    · exact Or.inr h
    · exact absurd rfl hne
    · exact Or.inl h
  · -- R L
    exact Or.inr trivial
  · -- L R
    exact Or.inl trivial
  · -- L L
    rcases Nat.lt_trichotomy d1 d2 with h | rfl | h
    · exact Or.inl h
    · exact absurd rfl hne
    · exact Or.inr h

/-- Distinct sided chains are always comparable. -/
theorem schainBefore_total : ∀ {c1 c2 : SChain}, c1 ≠ c2 →
    schainBefore c1 c2 ∨ schainBefore c2 c1
  | [], [], hne => absurd rfl hne
  | [], e :: es, _ => by
      obtain ⟨sd, d⟩ := e
      cases sd with
      | R => exact Or.inl (schainBefore.extR [] d es)
      | L => exact Or.inr (schainBefore.extL [] d es)
  | e :: es, [], _ => by
      obtain ⟨sd, d⟩ := e
      cases sd with
      | R => exact Or.inr (schainBefore.extR [] d es)
      | L => exact Or.inl (schainBefore.extL [] d es)
  | e1 :: t1, e2 :: t2, hne => by
      by_cases he : e1 = e2
      · subst he
        have hne' : t1 ≠ t2 := fun h => hne (by rw [h])
        rcases schainBefore_total hne' with h | h
        · exact Or.inl (schainBefore_cons e1 h)
        · exact Or.inr (schainBefore_cons e1 h)
      · rcases sEntryBefore_total he with h | h
        · exact Or.inl (schainBefore.diverge [] e1 e2 t1 t2 h)
        · exact Or.inr (schainBefore.diverge [] e2 e1 t2 t1 h)

/-! ## The sided marker theorem -/

/-- First-symbol comparison under a shared prefix. -/
theorem keyLt_append_cons_lt (p : List ℕ) {x y : ℕ} (h : x < y)
    (u v : List ℕ) :
    keyLt (p ++ x :: u) (p ++ y :: v) = true := by
  rw [keyLt_append_left]
  simp [keyLt, h]

/-- **In-order ⟹ key order**: the sided coordinate comparison realizes
the in-order rule. -/
theorem schainBefore_display (Γ : OrderedPrefixCode) {c1 c2 : SChain}
    (h1 : PosSChain c1) (h2 : PosSChain c2) (hb : schainBefore c1 c2) :
    keyLt (sKey (sidedCoordOf Γ c2)) (sKey (sidedCoordOf Γ c1)) = true := by
  cases hb with
  | extL ch d rest =>
      -- c1 = c2 ++ (L,d) :: rest: at the divergence, marker 3 (c2)
      -- meets an L-band symbol {4,5} (c1)
      have hd : 1 ≤ d :=
        h1 (Side.L, d) (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨b, bs, hbs⟩ : ∃ b bs, Γ.enc d = b :: bs := by
        cases henc : Γ.enc d with
        | nil => exact absurd henc (enc_ne_nil Γ hd)
        | cons b bs => exact ⟨b, bs, rfl⟩
      show keyLt (sidedCoordOf Γ c2 ++ [3])
        (sidedCoordOf Γ (c2 ++ (Side.L, d) :: rest) ++ [3]) = true
      rw [sidedCoordOf_append, List.append_assoc,
        show sidedCoordOf Γ ((Side.L, d) :: rest) ++ [3] =
          symL (!b) :: ((compl bs).map symL ++
            (sidedCoordOf Γ rest ++ [3])) from by
          simp [sidedCoordOf, sBlock, compl, hbs],
        show (sidedCoordOf Γ c2 ++ [3] : List ℕ) =
          sidedCoordOf Γ c2 ++ 3 :: [] from rfl]
      exact keyLt_append_cons_lt _ (three_lt_symL (!b)) _ _
  | extR ch d rest =>
      -- c2 = c1 ++ (R,d) :: rest: an R-band symbol {1,2} (c2) meets
      -- marker 3 (c1)
      have hd : 1 ≤ d :=
        h2 (Side.R, d) (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨b, bs, hbs⟩ : ∃ b bs, Γ.enc d = b :: bs := by
        cases henc : Γ.enc d with
        | nil => exact absurd henc (enc_ne_nil Γ hd)
        | cons b bs => exact ⟨b, bs, rfl⟩
      show keyLt (sidedCoordOf Γ (c1 ++ (Side.R, d) :: rest) ++ [3])
        (sidedCoordOf Γ c1 ++ [3]) = true
      rw [sidedCoordOf_append, List.append_assoc,
        show sidedCoordOf Γ ((Side.R, d) :: rest) ++ [3] =
          symR b :: (bs.map symR ++
            (sidedCoordOf Γ rest ++ [3])) from by
          simp [sidedCoordOf, sBlock, hbs],
        show (sidedCoordOf Γ c1 ++ [3] : List ℕ) =
          sidedCoordOf Γ c1 ++ 3 :: [] from rfl]
      exact keyLt_append_cons_lt _ (symR_lt_three b) _ _
  | diverge q e1 e2 t1 t2 hlt =>
      show keyLt (sidedCoordOf Γ (q ++ e2 :: t2) ++ [3])
        (sidedCoordOf Γ (q ++ e1 :: t1) ++ [3]) = true
      rw [sidedCoordOf_append, sidedCoordOf_append,
        List.append_assoc, List.append_assoc]
      obtain ⟨s1, d1⟩ := e1
      obtain ⟨s2, d2⟩ := e2
      have hd1 : 1 ≤ d1 :=
        h1 (s1, d1) (List.mem_append_right _ List.mem_cons_self)
      have hd2 : 1 ≤ d2 :=
        h2 (s2, d2) (List.mem_append_right _ List.mem_cons_self)
      cases s1 <;> cases s2
      · -- R vs R: newer (larger delta) first
        have hlt' : d2 < d1 := hlt
        obtain ⟨p, u1, u2, hE2, hE1⟩ := enc_first_diff Γ hd2 hd1 hlt'
        rw [show sidedCoordOf Γ ((Side.R, d2) :: t2) ++ [3] =
            p.map symR ++ 1 :: (u1.map symR ++
              (sidedCoordOf Γ t2 ++ [3])) from by
            simp [sidedCoordOf, sBlock, hE2, symR],
          show sidedCoordOf Γ ((Side.R, d1) :: t1) ++ [3] =
            p.map symR ++ 2 :: (u2.map symR ++
              (sidedCoordOf Γ t1 ++ [3])) from by
            simp [sidedCoordOf, sBlock, hE1, symR]]
        rw [keyLt_append_left, keyLt_append_left]
        simp [keyLt]
      · -- R vs L: impossible divergence
        exact absurd hlt (by simp [sEntryBefore])
      · -- L vs R: the bands decide
        obtain ⟨b1, bs1, hb1⟩ : ∃ b bs, Γ.enc d1 = b :: bs := by
          cases henc : Γ.enc d1 with
          | nil => exact absurd henc (enc_ne_nil Γ hd1)
          | cons b bs => exact ⟨b, bs, rfl⟩
        obtain ⟨b2, bs2, hb2⟩ : ∃ b bs, Γ.enc d2 = b :: bs := by
          cases henc : Γ.enc d2 with
          | nil => exact absurd henc (enc_ne_nil Γ hd2)
          | cons b bs => exact ⟨b, bs, rfl⟩
        rw [show sidedCoordOf Γ ((Side.R, d2) :: t2) ++ [3] =
            symR b2 :: (bs2.map symR ++
              (sidedCoordOf Γ t2 ++ [3])) from by
            simp [sidedCoordOf, sBlock, hb2],
          show sidedCoordOf Γ ((Side.L, d1) :: t1) ++ [3] =
            symL (!b1) :: ((compl bs1).map symL ++
              (sidedCoordOf Γ t1 ++ [3])) from by
            simp [sidedCoordOf, sBlock, compl, hb1]]
        exact keyLt_append_cons_lt _ (symR_lt_symL b2 (!b1)) _ _
      · -- L vs L: mirrored — the complement flips the differing bit
        have hlt' : d1 < d2 := hlt
        obtain ⟨p, u1, u2, hE1, hE2⟩ := enc_first_diff Γ hd1 hd2 hlt'
        rw [show sidedCoordOf Γ ((Side.L, d2) :: t2) ++ [3] =
            (compl p).map symL ++ 4 :: ((compl u2).map symL ++
              (sidedCoordOf Γ t2 ++ [3])) from by
            simp [sidedCoordOf, sBlock, compl, hE2, symL],
          show sidedCoordOf Γ ((Side.L, d1) :: t1) ++ [3] =
            (compl p).map symL ++ 5 :: ((compl u1).map symL ++
              (sidedCoordOf Γ t1 ++ [3])) from by
            simp [sidedCoordOf, sBlock, compl, hE1, symL]]
        rw [keyLt_append_left, keyLt_append_left]
        simp [keyLt]

theorem schainBefore_ne {c1 c2 : SChain} (h : schainBefore c1 c2) :
    c1 ≠ c2 := by
  cases h with
  | extL ch d rest =>
      intro h
      have := congrArg List.length h
      simp at this
  | extR ch d rest =>
      intro h
      have := congrArg List.length h
      simp at this
  | diverge q e1 e2 c1 c2 hlt =>
      intro h
      have h2 := List.append_cancel_left h
      injection h2 with h3 h4
      subst h3
      obtain ⟨s1, d1⟩ := e1
      cases s1 <;> simp [sEntryBefore] at hlt

/-- **The sided marker theorem**: for distinct positive sided chains,
the display comparison of the sided coordinates is exactly the in-order
rule. Two-sidedness is plain lexicographic order over the marker
alphabet — no bespoke three-way prefix clause. -/
theorem sdisplay_iff_schainBefore (Γ : OrderedPrefixCode)
    {c1 c2 : SChain} (h1 : PosSChain c1) (h2 : PosSChain c2)
    (hne : c1 ≠ c2) :
    keyLt (sKey (sidedCoordOf Γ c2)) (sKey (sidedCoordOf Γ c1)) = true ↔
      schainBefore c1 c2 := by
  constructor
  · intro h
    rcases schainBefore_total hne with hb | hb
    · exact hb
    · have h' := schainBefore_display Γ h2 h1 hb
      rw [keyLt_asymm h'] at h
      exact Bool.noConfusion h
  · exact schainBefore_display Γ h1 h2

/-! ## Cross-validation against the Python model

`embed_sided.py`'s symbol strings, at the unary code: an R-entry of
delta 1 is `[2,1]` (code `10` in the R band), its L twin `[4,5]`
(complement `01` in the L band); the marker sits between the bands. -/

example : sidedCoordOf unaryCode [(Side.R, 1)] = [2, 1] := by decide
example : sidedCoordOf unaryCode [(Side.L, 1)] = [4, 5] := by decide
example : sidedCoordOf unaryCode [(Side.R, 2), (Side.L, 1)] =
    [2, 2, 1, 4, 5] := by decide

/-- The node displays before its R-child and after its L-child. -/
example : keyLt (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.R, 2)]))
    (sKey (sidedCoordOf unaryCode [(Side.R, 1)])) = true := by decide
example : keyLt (sKey (sidedCoordOf unaryCode [(Side.R, 1)]))
    (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.L, 2)])) = true := by
  decide

end Sal.EmbedRGA
