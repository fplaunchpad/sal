import Sal.MRDTs.RGA_Embed.Sided_ChainLex

/-!
# The FugueMax chain-lex kernel — right-origin-tagged R entries (task #87a)

Weidner-Kleppmann Definition 6 (arXiv:2305.00583v3): FugueMax is Fugue
with the tree traversal visiting right-side siblings in the REVERSE order
of their right origins, ties by ascending ID; left-side siblings stay in
ascending ID order. The Python validation is
`whiteboard/litmus/fuguemax_check.py`; the design section is appended to
`whiteboard/fugue-maximal-noninterleaving.md`.

The realization decision (machine-witnessed in Python by the `mirror`
control): the R-sibling order depends on the right origin, which is not a
function of `(side, delta)`, so no re-banding of the delta alphabet alone
can realize it. The kernel variant therefore enriches the R ENTRY: an R
entry carries an immutable right-origin TAG (`[0]` for the `end` origin,
otherwise the right origin's sort key, captured at mint time), and the
R-sibling rule compares tags first (smaller tag = display-later right
origin = earlier sibling), then deltas ascending. The L band is the sided
kernel's, unchanged.

Flat realization: tags are embedded through the order-REVERSING
fixed-width map `fw k = [(8-k)/3, (8-k)%3]` (two symbols in {0,1,2}, all
below the marker), and the delta code is complemented into the R band
(`compl` = the sided kernel's L-band trick, here realizing ascending
deltas). Bands: R block symbols {0,1,2} < marker 3 < L band {4,5}; block
heads are never 0, coordinates never contain 3, so keys stay prefix-free
and `keyLt` machinery is reused unchanged.
-/

namespace Sal.EmbedRGA

/-! ## FugueMax entries -/

inductive FMEntry : Type where
  | R (ro : List ℕ) (d : ℕ)
  | L (d : ℕ)
deriving DecidableEq

abbrev FMChain : Type := List FMEntry

/-- The delta of an entry. -/
def fmδ : FMEntry → ℕ
  | .R _ d => d
  | .L d => d

@[simp] def PosFMChain (ch : FMChain) : Prop := ∀ e ∈ ch, 1 ≤ fmδ e

/-- Wellformed right-origin tags: the end tag `[0]`, or a real key —
nonzero non-marker head, marker-free bounded body, marker terminator. -/
def TagOK (t : List ℕ) : Prop :=
  t = [0] ∨ ∃ h c, t = (h :: c) ++ [3] ∧ h ≠ 0 ∧ h ≠ 3 ∧ h ≤ 5 ∧
    ∀ s ∈ c, s ≠ 3 ∧ s ≤ 5

def fmTagOK : FMEntry → Prop
  | .R t _ => TagOK t
  | .L _ => True

@[simp] def TagsOK (ch : FMChain) : Prop := ∀ e ∈ ch, fmTagOK e

theorem tagOK_ne_nil {t : List ℕ} (h : TagOK t) : t ≠ [] := by
  rcases h with rfl | ⟨h, c, rfl, -⟩ <;> simp

theorem tagOK_head {t : List ℕ} (h : TagOK t) :
    ∃ a t', t = a :: t' ∧ a ≤ 5 := by
  rcases h with rfl | ⟨h, c, rfl, -, -, hle, -⟩
  · exact ⟨0, [], rfl, by omega⟩
  · exact ⟨h, c ++ [3], rfl, hle⟩

theorem tagOK_symbols_le {t : List ℕ} (h : TagOK t) : ∀ s ∈ t, s ≤ 5 := by
  rcases h with rfl | ⟨h, c, rfl, -, -, hle, hc⟩
  · intro s hs
    simp at hs
    omega
  · intro s hs
    simp only [List.cons_append, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hle
    · rcases List.mem_append.mp hs with hs' | hs'
      · exact (hc s hs').2
      · rw [List.mem_singleton] at hs'
        omega

/-- Marker-terminated words with marker-free bodies are prefix-free. -/
theorem key_body_prefixFree : ∀ {u v : List ℕ}, (∀ s ∈ v, s ≠ 3) →
    u ≠ v → ¬ ((u ++ [3]) <+: (v ++ [3]))
  | [], [], _, hne, _ => hne rfl
  | [], y :: ys, hv, _, hpre => by
      rw [List.nil_append, List.cons_append, List.cons_prefix_cons] at hpre
      exact hv y List.mem_cons_self hpre.1.symm
  | x :: xs, [], _, _, hpre => by
      rw [List.cons_append, List.nil_append, List.cons_prefix_cons] at hpre
      obtain ⟨rfl, htail⟩ := hpre
      simp at htail
  | x :: xs, y :: ys, hv, hne, hpre => by
      rw [List.cons_append, List.cons_append, List.cons_prefix_cons] at hpre
      obtain ⟨rfl, htail⟩ := hpre
      have hne' : xs ≠ ys := fun h => hne (by rw [h])
      exact key_body_prefixFree
        (fun s hs => hv s (List.mem_cons_of_mem _ hs)) hne' htail

/-- Distinct wellformed tags are never prefixes of one another. -/
theorem tagOK_prefixFree {t₁ t₂ : List ℕ} (h₁ : TagOK t₁) (h₂ : TagOK t₂)
    (hne : t₁ ≠ t₂) : ¬ (t₁ <+: t₂) := by
  rcases h₁ with rfl | ⟨a, c, rfl, ha0, -, -, -⟩
  · rcases h₂ with rfl | ⟨b, d, rfl, hb0, -, -, -⟩
    · exact absurd rfl hne
    · intro hpre
      rw [List.cons_append, List.cons_prefix_cons] at hpre
      exact hb0 hpre.1.symm
  · rcases h₂ with rfl | ⟨b, d, rfl, -, hb3, -, hd⟩
    · intro hpre
      have := hpre.length_le
      simp at this
    · exact key_body_prefixFree
        (by
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · exact hb3
          · exact (hd s hs').1) (by simpa using hne)

/-! ## The order-reversing fixed-width tag embedding -/

/-- Two R-band symbols per tag symbol, order-reversing on {0..5}. -/
def fw (k : ℕ) : List ℕ := [(8 - k) / 3, (8 - k) % 3]

def fwTag : List ℕ → List ℕ
  | [] => []
  | k :: t => fw k ++ fwTag t

theorem fwTag_append (s t : List ℕ) :
    fwTag (s ++ t) = fwTag s ++ fwTag t := by
  induction s with
  | nil => rfl
  | cons k s ih => simp [fwTag, ih]

theorem fw_head_band {k : ℕ} (hk : k ≤ 5) :
    1 ≤ (8 - k) / 3 ∧ (8 - k) / 3 ≤ 2 := by omega

/-- The reversal: a smaller tag symbol yields a lexicographically LARGER
fixed-width block, whatever follows. -/
theorem fw_rev {a b : ℕ} (hab : a < b) (hb : b ≤ 5) (u v : List ℕ) :
    keyLt (fw b ++ u) (fw a ++ v) = true := by
  have h : (8 - b) / 3 < (8 - a) / 3 ∨
      ((8 - b) / 3 = (8 - a) / 3 ∧ (8 - b) % 3 < (8 - a) % 3) := by omega
  show keyLt ((8 - b) / 3 :: (8 - b) % 3 :: u)
    ((8 - a) / 3 :: (8 - a) % 3 :: v) = true
  rcases h with h | ⟨h1, h2⟩
  · simp [keyLt, h]
  · simp [keyLt, h1, h2]

theorem fw_inj {a b : ℕ} (ha : a ≤ 5) (hb : b ≤ 5)
    (h1 : (8 - a) / 3 = (8 - b) / 3) (h2 : (8 - a) % 3 = (8 - b) % 3) :
    a = b := by omega

/-! ## First-difference extraction for `keyLt` on prefix-free words -/

theorem keyLt_first_diff : ∀ {u v : List ℕ}, ¬ (u <+: v) →
    keyLt u v = true →
    ∃ p a b u' v', a < b ∧ u = p ++ a :: u' ∧ v = p ++ b :: v'
  | [], v, hpre, _ => absurd List.nil_prefix hpre
  | x :: xs, [], _, hlt => by simp [keyLt] at hlt
  | x :: xs, y :: ys, hpre, hlt => by
      rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
      · exact ⟨[], x, y, xs, ys, hxy, rfl, rfl⟩
      · have hpre' : ¬ (xs <+: ys) :=
          fun h => hpre (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        have hlt' : keyLt xs ys = true := by
          simp only [keyLt, Nat.lt_irrefl, if_false] at hlt
          exact hlt
        obtain ⟨p, a, b, u', v', hab, hu, hv⟩ := keyLt_first_diff hpre' hlt'
        exact ⟨x :: p, a, b, u', v', hab, by simp [hu], by simp [hv]⟩
      · rw [show keyLt (x :: xs) (y :: ys) = false from by
          simp [keyLt, hxy, Nat.lt_asymm hxy]] at hlt
        exact Bool.noConfusion hlt

/-! ## Blocks and coordinates -/

/-- The block of one entry: R blocks embed the reversed tag then the
complemented delta code in the R band; L blocks are the sided kernel's. -/
def fmBlock (Γ : OrderedPrefixCode) : FMEntry → List ℕ
  | .R t d => fwTag t ++ (compl (Γ.enc d)).map symR
  | .L d   => (compl (Γ.enc d)).map symL

def fmCoordOf (Γ : OrderedPrefixCode) : FMChain → List ℕ
  | [] => []
  | e :: ch => fmBlock Γ e ++ fmCoordOf Γ ch

theorem fmCoordOf_append (Γ : OrderedPrefixCode) (c1 c2 : FMChain) :
    fmCoordOf Γ (c1 ++ c2) = fmCoordOf Γ c1 ++ fmCoordOf Γ c2 := by
  induction c1 with
  | nil => simp [fmCoordOf]
  | cons e es ih => simp [fmCoordOf, ih]

theorem fmBlock_ne_nil (Γ : OrderedPrefixCode) {e : FMEntry}
    (he : 1 ≤ fmδ e) : fmBlock Γ e ≠ [] := by
  cases e with
  | R t d =>
      have hne := enc_ne_nil Γ (show 1 ≤ d from he)
      cases henc : Γ.enc d with
      | nil => exact absurd henc hne
      | cons b bs => simp [fmBlock, compl, henc]
  | L d =>
      have hne := enc_ne_nil Γ (show 1 ≤ d from he)
      cases henc : Γ.enc d with
      | nil => exact absurd henc hne
      | cons b bs => simp [fmBlock, compl, henc]

/-- Block head shape: R blocks start with an fw head (in {1,2} on
wellformed tags), L blocks with an L-band symbol. -/
theorem fmBlock_head_R (Γ : OrderedPrefixCode) {t : List ℕ} {d : ℕ}
    (ht : TagOK t) :
    ∃ a rest, fmBlock Γ (.R t d) = (8 - a) / 3 :: rest ∧ a ≤ 5 := by
  obtain ⟨a, t', rfl, ha⟩ := tagOK_head ht
  exact ⟨a, (8 - a) % 3 :: (fwTag t' ++ (compl (Γ.enc d)).map symR),
    by simp [fmBlock, fwTag, fw], ha⟩

theorem fmBlock_head_L (Γ : OrderedPrefixCode) {d : ℕ} (hd : 1 ≤ d) :
    ∃ b rest, fmBlock Γ (.L d) = symL b :: rest := by
  cases henc : Γ.enc d with
  | nil => exact absurd henc (enc_ne_nil Γ hd)
  | cons b bs =>
      exact ⟨!b, (compl bs).map symL, by simp [fmBlock, compl, henc]⟩

/-! ## Coordinate closure: variant coordinates are valid tag bodies -/

theorem symR_le (b : Bool) : symR b ≤ 5 := by cases b <;> simp [symR]
theorem symR_ne3 (b : Bool) : symR b ≠ 3 := by cases b <;> simp [symR]
theorem symL_le (b : Bool) : symL b ≤ 5 := by cases b <;> simp [symL]
theorem symL_ne3 (b : Bool) : symL b ≠ 3 := by cases b <;> simp [symL]

theorem fwTag_symbols {t : List ℕ} (ht : ∀ s ∈ t, s ≤ 5) :
    ∀ s ∈ fwTag t, s ≠ 3 ∧ s ≤ 5 := by
  induction t with
  | nil => intro s hs; simp [fwTag] at hs
  | cons k t ih =>
      intro s hs
      rcases List.mem_append.mp (by simpa [fwTag] using hs) with h | h
      · have hk := ht k List.mem_cons_self
        simp only [fw, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> constructor <;> omega
      · exact ih (fun s hs => ht s (List.mem_cons_of_mem _ hs)) s h

theorem fmBlock_symbols (Γ : OrderedPrefixCode) {e : FMEntry}
    (ht : fmTagOK e) : ∀ s ∈ fmBlock Γ e, s ≠ 3 ∧ s ≤ 5 := by
  cases e with
  | R t d =>
      intro s hs
      rcases List.mem_append.mp hs with h | h
      · exact fwTag_symbols (tagOK_symbols_le ht) s h
      · obtain ⟨b, -, rfl⟩ := List.mem_map.mp h
        exact ⟨symR_ne3 b, symR_le b⟩
  | L d =>
      intro s hs
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
      exact ⟨symL_ne3 b, symL_le b⟩

theorem fmCoordOf_symbols (Γ : OrderedPrefixCode) {ch : FMChain}
    (ht : TagsOK ch) : ∀ s ∈ fmCoordOf Γ ch, s ≠ 3 ∧ s ≤ 5 := by
  induction ch with
  | nil => intro s hs; simp [fmCoordOf] at hs
  | cons e es ih =>
      intro s hs
      rcases List.mem_append.mp hs with h | h
      · exact fmBlock_symbols Γ (ht e List.mem_cons_self) s h
      · exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx)) s h

/-- **Tag closure**: the key of a wellformed nonempty coordinate is itself
a wellformed tag — what lets minted keys feed back in as right-origin
tags. -/
theorem tagOK_key (Γ : OrderedPrefixCode) {ch : FMChain}
    (hpos : PosFMChain ch) (ht : TagsOK ch) (hne : ch ≠ []) :
    TagOK (sKey (fmCoordOf Γ ch)) := by
  cases ch with
  | nil => exact absurd rfl hne
  | cons e es =>
      right
      have hsym := fmCoordOf_symbols Γ (ch := e :: es) ht
      have hhead : ∃ h rest, fmCoordOf Γ (e :: es) = h :: rest ∧ h ≠ 0 := by
        cases e with
        | R t d =>
            obtain ⟨a, rest, heq, ha⟩ :=
              fmBlock_head_R Γ (d := d) (ht (.R t d) List.mem_cons_self)
            refine ⟨(8 - a) / 3, rest ++ fmCoordOf Γ es, ?_, by omega⟩
            show fmBlock Γ (.R t d) ++ fmCoordOf Γ es = _
            rw [heq]
            rfl
        | L d =>
            obtain ⟨b, rest, heq⟩ := fmBlock_head_L Γ (d := d)
              (show 1 ≤ d from hpos (.L d) List.mem_cons_self)
            refine ⟨symL b, rest ++ fmCoordOf Γ es, ?_, ?_⟩
            · show fmBlock Γ (.L d) ++ fmCoordOf Γ es = _
              rw [heq]
              rfl
            · cases b <;> simp [symL]
      obtain ⟨h, rest, heq, h0⟩ := hhead
      refine ⟨h, rest, ?_, h0, ?_, ?_, ?_⟩
      · show fmCoordOf Γ (e :: es) ++ [3] = (h :: rest) ++ [3]
        rw [heq]
      · exact (hsym h (heq ▸ List.mem_cons_self)).1
      · exact (hsym h (heq ▸ List.mem_cons_self)).2
      · intro s hs
        exact hsym s (heq ▸ List.mem_cons_of_mem _ hs)

/-! ## The entry order -/

/-- FugueMax divergence order: among R-siblings the smaller tag (the
display-later right origin) first, ties by ascending delta; among
L-siblings ascending delta (unchanged); L before node before R. -/
def fmEntryBefore : FMEntry → FMEntry → Prop
  | .R t1 d1, .R t2 d2 => keyLt t1 t2 = true ∨ (t1 = t2 ∧ d1 < d2)
  | .L d1, .L d2 => d1 < d2
  | .L _, .R _ _ => True
  | .R _ _, .L _ => False

theorem fmEntryBefore_irrefl (e : FMEntry) : ¬ fmEntryBefore e e := by
  cases e with
  | R t d =>
      rintro (h | ⟨-, h⟩)
      · rw [keyLt_irrefl] at h
        exact Bool.noConfusion h
      · omega
  | L d => exact fun h => absurd h (by simp [fmEntryBefore])

theorem fmEntryBefore_asymm {e1 e2 : FMEntry} (h : fmEntryBefore e1 e2) :
    ¬ fmEntryBefore e2 e1 := by
  cases e1 with
  | R t1 d1 =>
      cases e2 with
      | R t2 d2 =>
          rcases h with h | ⟨rfl, h⟩
          · rintro (h' | ⟨rfl, h'⟩)
            · rw [keyLt_asymm h] at h'
              exact Bool.noConfusion h'
            · rw [keyLt_irrefl] at h
              exact Bool.noConfusion h
          · rintro (h' | ⟨-, h'⟩)
            · rw [keyLt_irrefl] at h'
              exact Bool.noConfusion h'
            · omega
      | L d2 => exact absurd h (by simp [fmEntryBefore])
  | L d1 =>
      cases e2 with
      | R t2 d2 => exact fun h' => absurd h' (by simp [fmEntryBefore])
      | L d2 =>
          have h' : d1 < d2 := h
          simp only [fmEntryBefore]
          omega

theorem fmEntryBefore_total {e1 e2 : FMEntry} (hne : e1 ≠ e2) :
    fmEntryBefore e1 e2 ∨ fmEntryBefore e2 e1 := by
  cases e1 with
  | R t1 d1 =>
      cases e2 with
      | R t2 d2 =>
          rcases eq_or_ne t1 t2 with rfl | hnt
          · rcases Nat.lt_trichotomy d1 d2 with h | rfl | h
            · exact Or.inl (Or.inr ⟨rfl, h⟩)
            · exact absurd rfl hne
            · exact Or.inr (Or.inr ⟨rfl, h⟩)
          · rcases keyLt_total hnt with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
      | L d2 => exact Or.inr trivial
  | L d1 =>
      cases e2 with
      | R t2 d2 => exact Or.inl trivial
      | L d2 =>
          rcases Nat.lt_trichotomy d1 d2 with h | rfl | h
          · exact Or.inl h
          · exact absurd rfl hne
          · exact Or.inr h

/-! ## The chain order -/

inductive fmChainBefore : FMChain → FMChain → Prop where
  | extL (ch : FMChain) (d : ℕ) (rest : FMChain) :
      fmChainBefore (ch ++ .L d :: rest) ch
  | extR (ch : FMChain) (t : List ℕ) (d : ℕ) (rest : FMChain) :
      fmChainBefore ch (ch ++ .R t d :: rest)
  | diverge (q : FMChain) (e1 e2 : FMEntry) (c1 c2 : FMChain) :
      fmEntryBefore e1 e2 →
      fmChainBefore (q ++ e1 :: c1) (q ++ e2 :: c2)

theorem fmChainBefore_cons (x : FMEntry) {c1 c2 : FMChain}
    (h : fmChainBefore c1 c2) :
    fmChainBefore (x :: c1) (x :: c2) := by
  cases h with
  | extL ch d rest => exact fmChainBefore.extL (x :: c2) d rest
  | extR ch t d rest => exact fmChainBefore.extR (x :: c1) t d rest
  | diverge q e1 e2 t1 t2 hlt =>
      exact fmChainBefore.diverge (x :: q) e1 e2 t1 t2 hlt

theorem fmChainBefore_total : ∀ {c1 c2 : FMChain}, c1 ≠ c2 →
    fmChainBefore c1 c2 ∨ fmChainBefore c2 c1
  | [], [], hne => absurd rfl hne
  | [], e :: es, _ => by
      cases e with
      | R t d => exact Or.inl (fmChainBefore.extR [] t d es)
      | L d => exact Or.inr (fmChainBefore.extL [] d es)
  | e :: es, [], _ => by
      cases e with
      | R t d => exact Or.inr (fmChainBefore.extR [] t d es)
      | L d => exact Or.inl (fmChainBefore.extL [] d es)
  | e1 :: t1, e2 :: t2, hne => by
      by_cases he : e1 = e2
      · subst he
        have hne' : t1 ≠ t2 := fun h => hne (by rw [h])
        rcases fmChainBefore_total hne' with h | h
        · exact Or.inl (fmChainBefore_cons e1 h)
        · exact Or.inr (fmChainBefore_cons e1 h)
      · rcases fmEntryBefore_total he with h | h
        · exact Or.inl (fmChainBefore.diverge [] e1 e2 t1 t2 h)
        · exact Or.inr (fmChainBefore.diverge [] e2 e1 t2 t1 h)

theorem fmChainBefore_inv {c1 c2 : FMChain} (h : fmChainBefore c1 c2) :
    (∃ d rest, c1 = c2 ++ .L d :: rest) ∨
    (∃ t d rest, c2 = c1 ++ .R t d :: rest) ∨
    (∃ q e1 e2 t1 t2, fmEntryBefore e1 e2 ∧
      c1 = q ++ e1 :: t1 ∧ c2 = q ++ e2 :: t2) := by
  cases h with
  | extL ch d rest => exact Or.inl ⟨d, rest, rfl⟩
  | extR ch t d rest => exact Or.inr (Or.inl ⟨t, d, rest, rfl⟩)
  | diverge q e1 e2 t1 t2 hlt =>
      exact Or.inr (Or.inr ⟨q, e1, e2, t1, t2, hlt, rfl, rfl⟩)

theorem fmChainBefore_cons_strip {x : FMEntry} {a b : FMChain}
    (h : fmChainBefore (x :: a) (x :: b)) : fmChainBefore a b := by
  rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, ha, hb⟩
  · rw [List.cons_append] at heq
    injection heq with h1x h2
    rw [h2]
    exact fmChainBefore.extL b d rest
  · rw [List.cons_append] at heq
    injection heq with h1x h2
    rw [h2]
    exact fmChainBefore.extR a t d rest
  · cases q with
    | nil =>
        simp only [List.nil_append] at ha hb
        injection ha with h3 h4
        injection hb with h5 h6
        rw [← h3, ← h5] at hlt
        exact absurd hlt (fmEntryBefore_irrefl x)
    | cons y q' =>
        rw [List.cons_append] at ha hb
        injection ha with hax h4
        injection hb with hbx h6
        rw [h4, h6]
        exact fmChainBefore.diverge q' e1 e2 t1 t2 hlt

theorem fmChainBefore_nil_right {c : FMChain} (h : fmChainBefore c []) :
    ∃ d rest, c = .L d :: rest := by
  rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · exact ⟨d, rest, by simpa using heq⟩
  · simp at heq
  · simp at h2

theorem fmChainBefore_nil_left {c : FMChain} (h : fmChainBefore [] c) :
    ∃ t d rest, c = .R t d :: rest := by
  rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · simp at heq
  · exact ⟨t, d, rest, by simpa using heq⟩
  · simp at h1

theorem fmChainBefore_ne {c1 c2 : FMChain} (h : fmChainBefore c1 c2) :
    c1 ≠ c2 := by
  cases h with
  | extL ch d rest =>
      intro h
      have := congrArg List.length h
      simp at this
  | extR ch t d rest =>
      intro h
      have := congrArg List.length h
      simp at this
  | diverge q e1 e2 c1 c2 hlt =>
      intro h
      have h2 := List.append_cancel_left h
      injection h2 with h3 h4
      subst h3
      exact fmEntryBefore_irrefl e1 hlt

/-- A member of the subtree strictly after the node extends it on the R
side. -/
theorem fm_ext_after_is_R {p ext : FMChain}
    (h : fmChainBefore p (p ++ ext)) :
    ∃ t d rest, ext = FMEntry.R t d :: rest := by
  rcases fmChainBefore_inv h with ⟨d, rest, heq⟩ | ⟨t, d, rest, heq⟩ |
    ⟨q, e1, e2, t1, t2, hlt, h1, h2⟩
  · exfalso
    have := congrArg List.length heq
    simp at this
  · exact ⟨t, d, rest, List.append_cancel_left heq⟩
  · exfalso
    rw [h1, List.append_assoc] at h2
    have h3 := List.append_cancel_left h2
    injection h3 with h4 h5
    subst h4
    exact fmEntryBefore_irrefl e1 hlt

/-! ## Subtree convexity -/

theorem fm_subtree_convex :
    ∀ (p : FMChain) {cx cy cz : FMChain},
      (∃ ex, cx = p ++ ex) → (∃ ey, cy = p ++ ey) →
      fmChainBefore cx cz → fmChainBefore cz cy →
      ∃ ez, cz = p ++ ez
  | [], _, _, cz, _, _, _, _ => ⟨cz, rfl⟩
  | e :: p', cx, cy, cz, hex, hey, h1, h2 => by
      obtain ⟨ex, hx⟩ := hex
      obtain ⟨ey, hy⟩ := hey
      subst hx
      subst hy
      cases cz with
      | nil =>
          obtain ⟨d1, r1, hc1⟩ := fmChainBefore_nil_right h1
          obtain ⟨t2, d2, r2, hc2⟩ := fmChainBefore_nil_left h2
          rw [List.cons_append] at hc1 hc2
          injection hc1 with h3 h3t
          injection hc2 with h4 h4t
          rw [h3] at h4
          exact FMEntry.noConfusion h4
      | cons f cz' =>
          have hfe : f = e := by
            by_contra hne
            have hEF : fmEntryBefore e f := by
              rcases fmChainBefore_inv h1 with ⟨d, rest, heq⟩ |
                ⟨t, d, rest, heq⟩ | ⟨q, e1, e2, t1, t2, hlt, ha, hb⟩
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
            have hFE : fmEntryBefore f e := by
              rcases fmChainBefore_inv h2 with ⟨d, rest, heq⟩ |
                ⟨t, d, rest, heq⟩ | ⟨q, e1, e2, t1, t2, hlt, ha, hb⟩
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
            exact fmEntryBefore_asymm hEF hFE
          subst hfe
          obtain ⟨ez, hez⟩ := fm_subtree_convex p' ⟨ex, rfl⟩ ⟨ey, rfl⟩
            (fmChainBefore_cons_strip h1) (fmChainBefore_cons_strip h2)
          exact ⟨ez, by rw [List.cons_append, hez]⟩

/-! ## The FugueMax marker theorem -/

/-- **Chain order ⟹ key order**: the flat comparison of FugueMax
coordinates realizes the FugueMax in-order rule. -/
theorem fmChainBefore_display (Γ : OrderedPrefixCode) {c1 c2 : FMChain}
    (h1 : PosFMChain c1) (h2 : PosFMChain c2)
    (ht1 : TagsOK c1) (ht2 : TagsOK c2)
    (hb : fmChainBefore c1 c2) :
    keyLt (sKey (fmCoordOf Γ c2)) (sKey (fmCoordOf Γ c1)) = true := by
  cases hb with
  | extL ch d rest =>
      -- c1 = c2 ++ .L d :: rest: marker (c2) meets an L-band symbol (c1)
      have hd : 1 ≤ d :=
        h1 (.L d) (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨b, tl, hbl⟩ := fmBlock_head_L Γ (d := d) hd
      show keyLt (fmCoordOf Γ c2 ++ [3])
        (fmCoordOf Γ (c2 ++ .L d :: rest) ++ [3]) = true
      rw [fmCoordOf_append, List.append_assoc,
        show fmCoordOf Γ (.L d :: rest) ++ [3] =
          symL b :: (tl ++ (fmCoordOf Γ rest ++ [3])) from by
          show (fmBlock Γ (.L d) ++ fmCoordOf Γ rest) ++ [3] = _
          rw [hbl]
          simp,
        show (fmCoordOf Γ c2 ++ [3] : List ℕ) =
          fmCoordOf Γ c2 ++ 3 :: [] from rfl]
      exact keyLt_append_cons_lt _ (three_lt_symL b) _ _
  | extR ch t d rest =>
      -- c2 = c1 ++ .R t d :: rest: an fw head (c2) meets the marker (c1)
      have htag : TagOK t :=
        ht2 (.R t d) (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨a, tl, hbl, ha⟩ := fmBlock_head_R Γ (d := d) htag
      show keyLt (fmCoordOf Γ (c1 ++ .R t d :: rest) ++ [3])
        (fmCoordOf Γ c1 ++ [3]) = true
      rw [fmCoordOf_append, List.append_assoc,
        show fmCoordOf Γ (.R t d :: rest) ++ [3] =
          (8 - a) / 3 :: (tl ++ (fmCoordOf Γ rest ++ [3])) from by
          show (fmBlock Γ (.R t d) ++ fmCoordOf Γ rest) ++ [3] = _
          rw [hbl]
          simp,
        show (fmCoordOf Γ c1 ++ [3] : List ℕ) =
          fmCoordOf Γ c1 ++ 3 :: [] from rfl]
      exact keyLt_append_cons_lt _ (by omega : (8 - a) / 3 < 3) _ _
  | diverge q e1 e2 t1 t2 hlt =>
      show keyLt (fmCoordOf Γ (q ++ e2 :: t2) ++ [3])
        (fmCoordOf Γ (q ++ e1 :: t1) ++ [3]) = true
      rw [fmCoordOf_append, fmCoordOf_append,
        List.append_assoc, List.append_assoc]
      rw [keyLt_append_left]
      have hm1 : e1 ∈ q ++ e1 :: t1 :=
        List.mem_append_right _ List.mem_cons_self
      have hm2 : e2 ∈ q ++ e2 :: t2 :=
        List.mem_append_right _ List.mem_cons_self
      cases e1 with
      | R ta da =>
          cases e2 with
          | R tb db =>
              rcases hlt with htab | ⟨rfl, hdab⟩
              · -- tags differ: the reversed fixed-width embedding decides
                have hta : TagOK ta := ht1 _ hm1
                have htb : TagOK tb := ht2 _ hm2
                have hne : ta ≠ tb := by
                  intro h
                  rw [h, keyLt_irrefl] at htab
                  exact Bool.noConfusion htab
                obtain ⟨p, a, b, u', v', hab, hu, hv⟩ :=
                  keyLt_first_diff (tagOK_prefixFree hta htb hne) htab
                have hble : b ≤ 5 :=
                  tagOK_symbols_le htb b (by
                    rw [hv]
                    exact List.mem_append_right _ List.mem_cons_self)
                rw [show fmCoordOf Γ (.R tb db :: t2) ++ [3] =
                    fwTag p ++ (fw b ++ (fwTag v' ++
                      ((compl (Γ.enc db)).map symR ++
                        (fmCoordOf Γ t2 ++ [3])))) from by
                    show (fmBlock Γ (.R tb db) ++ fmCoordOf Γ t2) ++ [3] = _
                    rw [show fmBlock Γ (.R tb db)
                        = fwTag p ++ (fw b ++ (fwTag v' ++
                          (compl (Γ.enc db)).map symR)) from by
                      show fwTag tb ++ _ = _
                      rw [hv, fwTag_append]
                      show fwTag p ++ fwTag (b :: v') ++ _ = _
                      simp [fwTag]]
                    simp,
                  show fmCoordOf Γ (.R ta da :: t1) ++ [3] =
                    fwTag p ++ (fw a ++ (fwTag u' ++
                      ((compl (Γ.enc da)).map symR ++
                        (fmCoordOf Γ t1 ++ [3])))) from by
                    show (fmBlock Γ (.R ta da) ++ fmCoordOf Γ t1) ++ [3] = _
                    rw [show fmBlock Γ (.R ta da)
                        = fwTag p ++ (fw a ++ (fwTag u' ++
                          (compl (Γ.enc da)).map symR)) from by
                      show fwTag ta ++ _ = _
                      rw [hu, fwTag_append]
                      show fwTag p ++ fwTag (a :: u') ++ _ = _
                      simp [fwTag]]
                    simp]
                rw [keyLt_append_left]
                exact fw_rev hab hble _ _
              · -- equal tags: complemented delta code, ascending
                have hda : 1 ≤ da := h1 _ hm1
                have hdb : 1 ≤ db := h2 _ hm2
                obtain ⟨p, u1, u2, hE1, hE2⟩ :=
                  enc_first_diff Γ hda hdb hdab
                rw [show fmCoordOf Γ (.R ta db :: t2) ++ [3] =
                    fwTag ta ++ ((compl p).map symR ++ 1 ::
                      ((compl u2).map symR ++ (fmCoordOf Γ t2 ++ [3])))
                    from by
                    show (fmBlock Γ (.R ta db) ++ fmCoordOf Γ t2) ++ [3] = _
                    show ((fwTag ta ++ (compl (Γ.enc db)).map symR)
                      ++ fmCoordOf Γ t2) ++ [3] = _
                    rw [hE2]
                    simp [compl, symR],
                  show fmCoordOf Γ (.R ta da :: t1) ++ [3] =
                    fwTag ta ++ ((compl p).map symR ++ 2 ::
                      ((compl u1).map symR ++ (fmCoordOf Γ t1 ++ [3])))
                    from by
                    show (fmBlock Γ (.R ta da) ++ fmCoordOf Γ t1) ++ [3] = _
                    show ((fwTag ta ++ (compl (Γ.enc da)).map symR)
                      ++ fmCoordOf Γ t1) ++ [3] = _
                    rw [hE1]
                    simp [compl, symR]]
                rw [keyLt_append_left, keyLt_append_left]
                simp [keyLt]
          | L db => exact absurd hlt (by simp [fmEntryBefore])
      | L da =>
          cases e2 with
          | R tb db =>
              -- L before R: the bands decide
              have hda : 1 ≤ da := h1 _ hm1
              have htb : TagOK tb := ht2 _ hm2
              obtain ⟨b1, tl1, hbl1⟩ := fmBlock_head_L Γ (d := da) hda
              obtain ⟨a, tl2, hbl2, ha⟩ := fmBlock_head_R Γ (d := db) htb
              rw [show fmCoordOf Γ (.R tb db :: t2) ++ [3] =
                  (8 - a) / 3 :: (tl2 ++ (fmCoordOf Γ t2 ++ [3])) from by
                  show (fmBlock Γ (.R tb db) ++ fmCoordOf Γ t2) ++ [3] = _
                  rw [hbl2]
                  simp,
                show fmCoordOf Γ (.L da :: t1) ++ [3] =
                  symL b1 :: (tl1 ++ (fmCoordOf Γ t1 ++ [3])) from by
                  show (fmBlock Γ (.L da) ++ fmCoordOf Γ t1) ++ [3] = _
                  rw [hbl1]
                  simp]
              have hlt3 : (8 - a) / 3 < symL b1 := by
                have := fw_head_band (k := a) ha
                cases b1 <;> simp [symL] <;> omega
              show keyLt ([] ++ (8 - a) / 3 :: (tl2 ++ (fmCoordOf Γ t2 ++ [3])))
                ([] ++ symL b1 :: (tl1 ++ (fmCoordOf Γ t1 ++ [3]))) = true
              exact keyLt_append_cons_lt [] hlt3 _ _
          | L db =>
              -- L vs L: mirrored, unchanged from the sided kernel
              have hda : 1 ≤ da := h1 _ hm1
              have hdb : 1 ≤ db := h2 _ hm2
              have hdab : da < db := hlt
              obtain ⟨p, u1, u2, hE1, hE2⟩ := enc_first_diff Γ hda hdb hdab
              rw [show fmCoordOf Γ (.L db :: t2) ++ [3] =
                  (compl p).map symL ++ 4 :: ((compl u2).map symL ++
                    (fmCoordOf Γ t2 ++ [3])) from by
                  show (fmBlock Γ (.L db) ++ fmCoordOf Γ t2) ++ [3] = _
                  show ((compl (Γ.enc db)).map symL ++ fmCoordOf Γ t2)
                    ++ [3] = _
                  rw [hE2]
                  simp [compl, symL],
                show fmCoordOf Γ (.L da :: t1) ++ [3] =
                  (compl p).map symL ++ 5 :: ((compl u1).map symL ++
                    (fmCoordOf Γ t1 ++ [3])) from by
                  show (fmBlock Γ (.L da) ++ fmCoordOf Γ t1) ++ [3] = _
                  show ((compl (Γ.enc da)).map symL ++ fmCoordOf Γ t1)
                    ++ [3] = _
                  rw [hE1]
                  simp [compl, symL]]
              rw [keyLt_append_left]
              simp [keyLt]

/-- **The FugueMax marker theorem**: on distinct wellformed chains the
flat key comparison is exactly the FugueMax chain order. -/
theorem fmdisplay_iff_fmChainBefore (Γ : OrderedPrefixCode)
    {c1 c2 : FMChain} (h1 : PosFMChain c1) (h2 : PosFMChain c2)
    (ht1 : TagsOK c1) (ht2 : TagsOK c2) (hne : c1 ≠ c2) :
    keyLt (sKey (fmCoordOf Γ c2)) (sKey (fmCoordOf Γ c1)) = true ↔
      fmChainBefore c1 c2 := by
  constructor
  · intro h
    rcases fmChainBefore_total hne with hb | hb
    · exact hb
    · have h' := fmChainBefore_display Γ h2 h1 ht2 ht1 hb
      rw [keyLt_asymm h'] at h
      exact Bool.noConfusion h
  · exact fmChainBefore_display Γ h1 h2 ht1 ht2

/-! ## Unique decodability -/

/-- R-band delta symbol map (the complement composed into the map). -/
def symRc (b : Bool) : ℕ := symR (!b)

theorem symRc_inj : Function.Injective symRc := by
  intro a b h
  cases a <;> cases b <;> simp [symRc, symR] at h ⊢

theorem compl_map_symR (w : List Bool) :
    (compl w).map symR = w.map symRc := by
  simp [compl, symRc, List.map_map, Function.comp]

def symLc (b : Bool) : ℕ := symL (!b)

theorem symLc_inj : Function.Injective symLc := by
  intro a b h
  cases a <;> cases b <;> simp [symLc, symL] at h ⊢

theorem compl_map_symL (w : List Bool) :
    (compl w).map symL = w.map symLc := by
  simp [compl, symLc, List.map_map, Function.comp]

/-- Same-length prefix-or-equal lists sharing a common extension agree —
packaged as: two lists that are prefixes of one common list are
comparable. -/
theorem fw_group_inj {a b : ℕ} (ha : a ≤ 5) (hb : b ≤ 5)
    {u v : List ℕ} (h : fw a ++ u = fw b ++ v) : a = b ∧ u = v := by
  have h1 : (8 - a) / 3 = (8 - b) / 3 := by
    have := congrArg (fun l => l.headD 0) h
    simpa [fw] using this
  have h2 : (8 - a) % 3 = (8 - b) % 3 := by
    have := congrArg (fun l => (l.drop 1).headD 0) h
    simpa [fw] using this
  have hab : a = b := fw_inj ha hb h1 h2
  subst hab
  exact ⟨rfl, by simpa [fw] using h⟩

/-- Equal tag embeddings with arbitrary continuations force equal tags,
for prefix-free wellformed tags. -/
theorem fwTag_cancel {t₁ t₂ : List ℕ} (h₁ : TagOK t₁) (h₂ : TagOK t₂)
    {u v : List ℕ} (h : fwTag t₁ ++ u = fwTag t₂ ++ v) :
    t₁ = t₂ ∧ u = v := by
  by_cases hne : t₁ = t₂
  · subst hne
    exact ⟨rfl, List.append_cancel_left h⟩
  · exfalso
    have hp₁ := tagOK_prefixFree h₁ h₂ hne
    have hp₂ := tagOK_prefixFree h₂ h₁ (Ne.symm hne)
    -- extract a first difference from either keyLt direction
    obtain ⟨p, a, b, u', v', hab, hu, hv⟩ :
        ∃ p a b u' v', a ≠ b ∧ t₁ = p ++ a :: u' ∧ t₂ = p ++ b :: v' := by
      rcases keyLt_total hne with hk | hk
      · obtain ⟨p, a, b, u', v', hab, hu, hv⟩ := keyLt_first_diff hp₁ hk
        exact ⟨p, a, b, u', v', by omega, hu, hv⟩
      · obtain ⟨p, a, b, u', v', hab, hu, hv⟩ := keyLt_first_diff hp₂ hk
        exact ⟨p, b, a, v', u', by omega, hv, hu⟩
    have ha5 : a ≤ 5 := tagOK_symbols_le h₁ a
      (by rw [hu]; exact List.mem_append_right _ List.mem_cons_self)
    have hb5 : b ≤ 5 := tagOK_symbols_le h₂ b
      (by rw [hv]; exact List.mem_append_right _ List.mem_cons_self)
    rw [hu, hv, fwTag_append, fwTag_append, List.append_assoc,
      List.append_assoc] at h
    have h' := List.append_cancel_left h
    rw [show fwTag (a :: u') = fw a ++ fwTag u' from rfl,
      show fwTag (b :: v') = fw b ++ fwTag v' from rfl,
      List.append_assoc, List.append_assoc] at h'
    exact hab (fw_group_inj ha5 hb5 h').1

/-- **Unique decodability**: distinct wellformed FugueMax chains mint
distinct coordinates. -/
theorem fmCoordOf_inj (Γ : OrderedPrefixCode) :
    ∀ {c1 c2 : FMChain}, PosFMChain c1 → PosFMChain c2 →
      TagsOK c1 → TagsOK c2 →
      fmCoordOf Γ c1 = fmCoordOf Γ c2 → c1 = c2
  | [], [], _, _, _, _, _ => rfl
  | [], e :: es, _, h2, _, _, h => by
      exfalso
      have hd : 1 ≤ fmδ e := h2 e List.mem_cons_self
      have hne := fmBlock_ne_nil Γ hd
      cases hb : fmBlock Γ e with
      | nil => exact hne hb
      | cons x xs =>
          simp only [fmCoordOf, hb] at h
          simp at h
  | e :: es, [], h1, _, _, _, h => by
      exfalso
      have hd : 1 ≤ fmδ e := h1 e List.mem_cons_self
      have hne := fmBlock_ne_nil Γ hd
      cases hb : fmBlock Γ e with
      | nil => exact hne hb
      | cons x xs =>
          simp only [fmCoordOf, hb] at h
          simp at h
  | e1 :: c1, e2 :: c2, h1, h2, ht1, ht2, h => by
      have hd1 : 1 ≤ fmδ e1 := h1 e1 List.mem_cons_self
      have hd2 : 1 ≤ fmδ e2 := h2 e2 List.mem_cons_self
      simp only [fmCoordOf] at h
      have hee : e1 = e2 ∧ fmCoordOf Γ c1 = fmCoordOf Γ c2 := by
        cases e1 with
        | R ta da =>
            cases e2 with
            | R tb db =>
                have hta : TagOK ta := ht1 _ List.mem_cons_self
                have htb : TagOK tb := ht2 _ List.mem_cons_self
                simp only [fmBlock, List.append_assoc] at h
                obtain ⟨rfl, h'⟩ := fwTag_cancel hta htb h
                rw [compl_map_symR, compl_map_symR] at h'
                have hde : da = db := by
                  by_contra hnd
                  have p1 : (Γ.enc da).map symRc <+:
                      (Γ.enc da).map symRc ++ fmCoordOf Γ c1 :=
                    List.prefix_append _ _
                  have p2 : (Γ.enc db).map symRc <+:
                      (Γ.enc da).map symRc ++ fmCoordOf Γ c1 := by
                    rw [h']
                    exact List.prefix_append _ _
                  rcases Nat.le_total ((Γ.enc da).map symRc).length
                    ((Γ.enc db).map symRc).length with hle | hle
                  · exact Γ.prefixFree hd1 hd2 hnd
                      (map_prefix_reflect symRc_inj
                        (List.prefix_of_prefix_length_le p1 p2 hle))
                  · exact Γ.prefixFree hd2 hd1 (Ne.symm hnd)
                      (map_prefix_reflect symRc_inj
                        (List.prefix_of_prefix_length_le p2 p1 hle))
                subst hde
                exact ⟨rfl, List.append_cancel_left h'⟩
            | L db =>
                exfalso
                have hta : TagOK ta := ht1 _ List.mem_cons_self
                obtain ⟨a, tl, hbl, ha⟩ := fmBlock_head_R Γ (d := da) hta
                obtain ⟨b, tl2, hbl2⟩ := fmBlock_head_L Γ (d := db) hd2
                rw [hbl, hbl2] at h
                have hhead : (8 - a) / 3 = symL b := by
                  have := congrArg (fun l => l.headD 0) h
                  simpa using this
                have := fw_head_band (k := a) ha
                cases b <;> simp [symL] at hhead <;> omega
        | L da =>
            cases e2 with
            | R tb db =>
                exfalso
                have htb : TagOK tb := ht2 _ List.mem_cons_self
                obtain ⟨b, tl, hbl⟩ := fmBlock_head_L Γ (d := da) hd1
                obtain ⟨a, tl2, hbl2, ha⟩ := fmBlock_head_R Γ (d := db) htb
                rw [hbl, hbl2] at h
                have hhead : symL b = (8 - a) / 3 := by
                  have := congrArg (fun l => l.headD 0) h
                  simpa using this
                have := fw_head_band (k := a) ha
                cases b <;> simp [symL] at hhead <;> omega
            | L db =>
                simp only [fmBlock] at h
                rw [compl_map_symL, compl_map_symL] at h
                have hde : da = db := by
                  by_contra hnd
                  have p1 : (Γ.enc da).map symLc <+:
                      (Γ.enc da).map symLc ++ fmCoordOf Γ c1 :=
                    List.prefix_append _ _
                  have p2 : (Γ.enc db).map symLc <+:
                      (Γ.enc da).map symLc ++ fmCoordOf Γ c1 := by
                    rw [h]
                    exact List.prefix_append _ _
                  rcases Nat.le_total ((Γ.enc da).map symLc).length
                    ((Γ.enc db).map symLc).length with hle | hle
                  · exact Γ.prefixFree hd1 hd2 hnd
                      (map_prefix_reflect symLc_inj
                        (List.prefix_of_prefix_length_le p1 p2 hle))
                  · exact Γ.prefixFree hd2 hd1 (Ne.symm hnd)
                      (map_prefix_reflect symLc_inj
                        (List.prefix_of_prefix_length_le p2 p1 hle))
                subst hde
                exact ⟨rfl, List.append_cancel_left h⟩
      obtain ⟨he, hc⟩ := hee
      subst he
      rw [fmCoordOf_inj Γ
        (fun e he => h1 e (List.mem_cons_of_mem _ he))
        (fun e he => h2 e (List.mem_cons_of_mem _ he))
        (fun e he => ht1 e (List.mem_cons_of_mem _ he))
        (fun e he => ht2 e (List.mem_cons_of_mem _ he)) hc]

/-! ## Cross-validation examples (Python twin: fuguemax_check.py)

Unary code. The end tag is `[0]`; `fw 0 = [2,2]`; an R entry of delta 1
carries `compl (enc 1) = [false, true]` mapped to `[1,2]`. -/

example : fmCoordOf unaryCode [.R [0] 1] = [2, 2, 1, 2] := by decide

/-- Two R-siblings with the end tag order by ascending delta: the smaller
delta displays first (the two-front-inserts case, FugueMax order). -/
example : keyLt (sKey (fmCoordOf unaryCode [.R [0] 2]))
    (sKey (fmCoordOf unaryCode [.R [0] 1])) = true := by decide

/-- Two R-siblings with distinct real tags order by REVERSE right origin:
the sibling whose right origin displays later (the node `[.R [0] 5]`,
which sits after `[.R [0] 4]` and so has the smaller key) displays FIRST,
even though it has the larger delta — right origin overrides recency and
ID order alike. -/
example : keyLt (sKey (fmCoordOf unaryCode [.R (sKey (fmCoordOf unaryCode
    [.R [0] 4])) 1]))
    (sKey (fmCoordOf unaryCode [.R (sKey (fmCoordOf unaryCode [.R [0] 5]))
      4])) = true := by decide

/-- L-siblings are unchanged: ascending delta, older first. -/
example : keyLt (sKey (fmCoordOf unaryCode [.R [0] 1, .L 20]))
    (sKey (fmCoordOf unaryCode [.R [0] 1, .L 9])) = true := by decide

#print axioms fmdisplay_iff_fmChainBefore
#print axioms fm_subtree_convex
#print axioms fmCoordOf_inj
#print axioms tagOK_key

end Sal.EmbedRGA
