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

/-! ## Unique decodability over the sided alphabet -/

/-- Uniform view of a block: the code mapped through the side's symbol
function (the L side pre-composes the complement). -/
def sideSym : Side → Bool → ℕ
  | Side.R => symR
  | Side.L => fun b => symL (!b)

theorem sBlock_eq (Γ : OrderedPrefixCode) (sd : Side) (d : ℕ) :
    sBlock Γ (sd, d) = (Γ.enc d).map (sideSym sd) := by
  cases sd with
  | R => rfl
  | L => simp [sBlock, sideSym, compl, List.map_map, Function.comp]

theorem sideSym_inj (sd : Side) : Function.Injective (sideSym sd) := by
  cases sd <;> intro a b h <;> cases a <;> cases b <;>
    simp [sideSym, symR, symL] at h ⊢

theorem sideSym_band_ne (b b' : Bool) :
    sideSym Side.R b ≠ sideSym Side.L b' := by
  cases b <;> cases b' <;> simp [sideSym, symR, symL]

/-- Injective per-symbol maps reflect prefixes. -/
theorem map_prefix_reflect {f : Bool → ℕ} (hf : Function.Injective f) :
    ∀ {u v : List Bool}, u.map f <+: v.map f → u <+: v
  | [], _, _ => List.nil_prefix
  | a :: u, [], h => by simp at h
  | a :: u, b :: v, h => by
      simp only [List.map_cons, List.cons_prefix_cons] at h
      obtain ⟨hab, ht⟩ := h
      have hab' := hf hab
      subst hab'
      exact List.cons_prefix_cons.mpr ⟨rfl, map_prefix_reflect hf ht⟩

/-- **Unique decodability**: distinct positive sided chains mint distinct
coordinates — the side is recoverable from the first symbol's band, the
delta by prefix-freedom within the band. -/
theorem sidedCoordOf_inj (Γ : OrderedPrefixCode) :
    ∀ {c1 c2 : SChain}, PosSChain c1 → PosSChain c2 →
      sidedCoordOf Γ c1 = sidedCoordOf Γ c2 → c1 = c2
  | [], [], _, _, _ => rfl
  | [], (sd, d) :: es, _, h2, h => by
      exfalso
      have hd : 1 ≤ d := h2 (sd, d) List.mem_cons_self
      have hne := sBlock_ne_nil Γ (e := (sd, d)) hd
      cases hb : sBlock Γ (sd, d) with
      | nil => exact hne hb
      | cons x xs =>
          simp only [sidedCoordOf, hb] at h
          simp at h
  | (sd, d) :: es, [], h1, _, h => by
      exfalso
      have hd : 1 ≤ d := h1 (sd, d) List.mem_cons_self
      have hne := sBlock_ne_nil Γ (e := (sd, d)) hd
      cases hb : sBlock Γ (sd, d) with
      | nil => exact hne hb
      | cons x xs =>
          simp only [sidedCoordOf, hb] at h
          simp at h
  | (s1, d1) :: t1, (s2, d2) :: t2, h1, h2, h => by
      have hd1 : 1 ≤ d1 := h1 (s1, d1) List.mem_cons_self
      have hd2 : 1 ≤ d2 := h2 (s2, d2) List.mem_cons_self
      simp only [sidedCoordOf, sBlock_eq] at h
      obtain ⟨b1, bs1, hb1⟩ : ∃ b bs, Γ.enc d1 = b :: bs := by
        cases henc : Γ.enc d1 with
        | nil => exact absurd henc (enc_ne_nil Γ hd1)
        | cons b bs => exact ⟨b, bs, rfl⟩
      obtain ⟨b2, bs2, hb2⟩ : ∃ b bs, Γ.enc d2 = b :: bs := by
        cases henc : Γ.enc d2 with
        | nil => exact absurd henc (enc_ne_nil Γ hd2)
        | cons b bs => exact ⟨b, bs, rfl⟩
      have hs : s1 = s2 := by
        by_contra hns
        rw [hb1, hb2] at h
        simp only [List.map_cons, List.cons_append,
          List.cons.injEq] at h
        cases s1 <;> cases s2
        · exact hns rfl
        · exact sideSym_band_ne b1 b2 h.1
        · exact sideSym_band_ne b2 b1 h.1.symm
        · exact hns rfl
      subst hs
      have hdd : d1 = d2 := by
        by_contra hnd
        have p1 : (Γ.enc d1).map (sideSym s1) <+:
            (Γ.enc d1).map (sideSym s1) ++ sidedCoordOf Γ t1 :=
          List.prefix_append _ _
        have p2 : (Γ.enc d2).map (sideSym s1) <+:
            (Γ.enc d1).map (sideSym s1) ++ sidedCoordOf Γ t1 := by
          rw [h]
          exact List.prefix_append _ _
        rcases Nat.le_total ((Γ.enc d1).map (sideSym s1)).length
          ((Γ.enc d2).map (sideSym s1)).length with hle | hle
        · exact Γ.prefixFree hd1 hd2 hnd
            (map_prefix_reflect (sideSym_inj s1)
              (List.prefix_of_prefix_length_le p1 p2 hle))
        · exact Γ.prefixFree hd2 hd1 (Ne.symm hnd)
            (map_prefix_reflect (sideSym_inj s1)
              (List.prefix_of_prefix_length_le p2 p1 hle))
      subst hdd
      have htail := List.append_cancel_left h
      rw [sidedCoordOf_inj Γ
        (fun e he => h1 e (List.mem_cons_of_mem _ he))
        (fun e he => h2 e (List.mem_cons_of_mem _ he)) htail]

/-! ## The all-R fragment: the one-sided design, verbatim

The erasure theorem, derived through the two marker theorems: lifting a
one-sided chain to all-R sided form changes neither the coordinate's key
nor the display verdict — the current datatype IS the L-uninhabited
fragment. This is the Lean form of the Python all-R lockstep. -/

/-- Lift a one-sided (delta) chain to the all-R sided form. -/
def liftR (c : List ℕ) : SChain := c.map (fun d => (Side.R, d))

theorem liftR_inj {c1 c2 : List ℕ} (h : liftR c1 = liftR c2) : c1 = c2 := by
  have := congrArg (List.map Prod.snd) h
  simpa [liftR, List.map_map, Function.comp] using this

theorem posSChain_liftR {c : List ℕ} (h : PosChain c) :
    PosSChain (liftR c) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  exact h d hd

/-- All-R blocks are the one-sided codewords under the one-sided symbol
map. -/
theorem sidedCoordOf_liftR (Γ : OrderedPrefixCode) (c : List ℕ) :
    sidedCoordOf Γ (liftR c) = (coordOf Γ c).map sym := by
  induction c with
  | nil => rfl
  | cons d ds ih =>
      show sBlock Γ (Side.R, d) ++ sidedCoordOf Γ (liftR ds) = _
      rw [ih]
      simp only [coordOf, List.map_append]
      congr 1

/-- The lifted key IS the one-sided key. -/
theorem sKey_liftR (Γ : OrderedPrefixCode) (c : List ℕ) :
    sKey (sidedCoordOf Γ (liftR c)) = key (coordOf Γ c) := by
  rw [sidedCoordOf_liftR]
  rfl

/-- **The fragment theorem**: on all-R chains, the in-order rule IS the
one-sided chain order. The current embed is the L-uninhabited fragment,
as a theorem. -/
theorem schainBefore_liftR {c1 c2 : List ℕ}
    (h1 : PosChain c1) (h2 : PosChain c2) (hne : c1 ≠ c2) :
    schainBefore (liftR c1) (liftR c2) ↔ chainBefore c1 c2 := by
  have hlne : liftR c1 ≠ liftR c2 := fun h => hne (liftR_inj h)
  rw [← sdisplay_iff_schainBefore unaryCode (posSChain_liftR h1)
      (posSChain_liftR h2) hlne, sKey_liftR, sKey_liftR]
  exact display_iff_chainBefore unaryCode h1 h2 hne

/-! ## In-order-interval convexity: a subtree is a display interval

The Fugue intent target: everything the display places between two
members of a subtree is itself in the subtree — with the node included
(the empty extension), since the subtree's interval straddles it:
L-descendants, the node, R-descendants. -/

theorem sEntryBefore_irrefl (e : SEntry) : ¬ sEntryBefore e e := by
  obtain ⟨sd, d⟩ := e
  cases sd <;> simp [sEntryBefore]

theorem sEntryBefore_asymm {e1 e2 : SEntry} (h : sEntryBefore e1 e2) :
    ¬ sEntryBefore e2 e1 := by
  obtain ⟨s1, d1⟩ := e1
  obtain ⟨s2, d2⟩ := e2
  cases s1 <;> cases s2 <;> simp [sEntryBefore] at h ⊢ <;> omega

/-- Inversion of the in-order rule into its three verdict shapes. -/
theorem schainBefore_inv {c1 c2 : SChain} (h : schainBefore c1 c2) :
    (∃ d rest, c1 = c2 ++ (Side.L, d) :: rest) ∨
    (∃ d rest, c2 = c1 ++ (Side.R, d) :: rest) ∨
    (∃ q e1 e2 t1 t2, sEntryBefore e1 e2 ∧
      c1 = q ++ e1 :: t1 ∧ c2 = q ++ e2 :: t2) := by
  cases h with
  | extL ch d rest => exact Or.inl ⟨d, rest, rfl⟩
  | extR ch d rest => exact Or.inr (Or.inl ⟨d, rest, rfl⟩)
  | diverge q e1 e2 t1 t2 hlt =>
      exact Or.inr (Or.inr ⟨q, e1, e2, t1, t2, hlt, rfl, rfl⟩)

/-- A shared head strips off the in-order rule. -/
theorem schainBefore_cons_strip {x : SEntry} {a b : SChain}
    (h : schainBefore (x :: a) (x :: b)) : schainBefore a b := by
  rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, ha, hb⟩
  · rw [List.cons_append] at heq
    injection heq with h1x h2
    rw [h2]
    exact schainBefore.extL b d rest
  · rw [List.cons_append] at heq
    injection heq with h1x h2
    rw [h2]
    exact schainBefore.extR a d rest
  · cases q with
    | nil =>
        simp only [List.nil_append] at ha hb
        injection ha with h3 h4
        injection hb with h5 h6
        rw [← h3, ← h5] at hlt
        exact absurd hlt (sEntryBefore_irrefl x)
    | cons y q' =>
        rw [List.cons_append] at ha hb
        injection ha with hax h4
        injection hb with hbx h6
        rw [h4, h6]
        exact schainBefore.diverge q' e1 e2 t1 t2 hlt

/-- Only L-headed chains display before the root. -/
theorem schainBefore_nil_right {c : SChain} (h : schainBefore c []) :
    ∃ d rest, c = (Side.L, d) :: rest := by
  rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · exact ⟨d, rest, by simpa using heq⟩
  · simp at heq
  · simp at h2

/-- Only R-headed chains display after the root. -/
theorem schainBefore_nil_left {c : SChain} (h : schainBefore [] c) :
    ∃ d rest, c = (Side.R, d) :: rest := by
  rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · simp at heq
  · exact ⟨d, rest, by simpa using heq⟩
  · simp at h1

/-- **In-order-interval convexity**: whatever the display places between
two members of `p`'s subtree is itself in `p`'s subtree. With the empty
extension allowed, the node itself is a member — the subtree interval is
L-descendants, then the node, then R-descendants, with nothing foreign
in between. -/
theorem schain_subtree_convex :
    ∀ (p : SChain) {cx cy cz : SChain},
      (∃ ex, cx = p ++ ex) → (∃ ey, cy = p ++ ey) →
      schainBefore cx cz → schainBefore cz cy →
      ∃ ez, cz = p ++ ez
  | [], _, _, cz, _, _, _, _ => ⟨cz, rfl⟩
  | e :: p', cx, cy, cz, hex, hey, h1, h2 => by
      obtain ⟨ex, hx⟩ := hex
      obtain ⟨ey, hy⟩ := hey
      subst hx
      subst hy
      cases cz with
      | nil =>
          obtain ⟨d1, r1, hc1⟩ := schainBefore_nil_right h1
          obtain ⟨d2, r2, hc2⟩ := schainBefore_nil_left h2
          rw [List.cons_append] at hc1 hc2
          injection hc1 with h3 h3t
          injection hc2 with h4 h4t
          rw [h3] at h4
          exact absurd (congrArg Prod.fst h4) (by simp)
      | cons f cz' =>
          have hfe : f = e := by
            by_contra hne
            have hEF : sEntryBefore e f := by
              rcases schainBefore_inv h1 with ⟨d, rest, heq⟩ |
                ⟨d, rest, heq⟩ | ⟨q, e1, e2, t1, t2, hlt, ha, hb⟩
              · rw [List.cons_append] at heq
                injection heq with h3 h3t
                exact absurd h3.symm hne
              · rw [List.cons_append] at heq
                injection heq with h3 h3t
                exact absurd h3 hne
              · cases q with
                | nil =>
                    simp only [List.nil_append] at ha hb
                    injection ha with h3 h3t
                    injection hb with h4 h4t
                    rw [← h3, ← h4] at hlt
                    exact hlt
                | cons y q' =>
                    rw [List.cons_append] at ha hb
                    injection ha with h3 h3t
                    injection hb with h4 h4t
                    exact absurd (h4.trans h3.symm) hne
            have hFE : sEntryBefore f e := by
              rcases schainBefore_inv h2 with ⟨d, rest, heq⟩ |
                ⟨d, rest, heq⟩ | ⟨q, e1, e2, t1, t2, hlt, ha, hb⟩
              · rw [List.cons_append] at heq
                injection heq with h3 h3t
                exact absurd h3 hne
              · rw [List.cons_append] at heq
                injection heq with h3 h3t
                exact absurd h3.symm hne
              · cases q with
                | nil =>
                    simp only [List.nil_append] at ha hb
                    injection ha with h3 h3t
                    injection hb with h4 h4t
                    rw [← h3, ← h4] at hlt
                    exact hlt
                | cons y q' =>
                    rw [List.cons_append] at ha hb
                    injection ha with h3 h3t
                    injection hb with h4 h4t
                    exact absurd (h3.trans h4.symm) hne
            exact sEntryBefore_asymm hEF hFE
          subst hfe
          obtain ⟨ez, hez⟩ := schain_subtree_convex p' ⟨ex, rfl⟩ ⟨ey, rfl⟩
            (schainBefore_cons_strip h1) (schainBefore_cons_strip h2)
          exact ⟨ez, by rw [List.cons_append, hez]⟩

end Sal.EmbedRGA
