import Sal.MRDTs.RGA_Embed.RGA_Embed_ChainLex
import Sal.MRDTs.RGA_with_tombstones.RGA_ReadSide

/-!
# Read-equivalence with the published tombstoned RGA — the order core

The compaction theorem: the
embedded-chain RGA's display order **is** the published RGA's visible
order, on the shared birth tree of one honest event set.

The published RGA (`Sal/MRDTs/RGA_with_tombstones`) reads through the
relational order `visible_lt` — the RGA traversal of the insert-record
forest (`parent_child` | newer `sibling` | `left_descendant_of_sibling` |
`trans`). The embedded-chain RGA reads by sorting coordinates, which is
chain-lex (`display_iff_chainBefore`). This file proves the two orders
coincide, **against the published definition**, parametrized by a *birth
environment*: the RGA† state's `after_of` edge relation together with a
delta-chain assignment satisfying the honesty facts every honest fold
provides (anchors are earlier and present; a child's chain extends its
anchor's by the timestamp gap). Instantiating the environment at the two
folds of one event set is the remaining wiring (steps 1–3, 5).

Both sides of the equivalence are consumed relationally, so the theorem
is exactly the one the design doc owes: the RGA† visible order and the
chain order are one relation on the birth tree — the tombstoned read and
the coordinate read cannot disagree.
-/

namespace Sal.EmbedRGA

/-! ## The birth environment -/

/-- `c` has an insert record in the RGA† state (the root sentinel `0`
never does, by `anchor_lt`). -/
def RealId (s : _root_.concrete_st) (c : ℕ) : Prop :=
  ∃ p, _root_.after_of s c p

/-- A node of the birth tree: a real id, or the root sentinel. -/
def TreeId (s : _root_.concrete_st) (c : ℕ) : Prop :=
  c = 0 ∨ RealId s c

/-- The honesty interface of the read-equivalence, stated purely in terms
of RGA†'s `after_of` edge relation and a delta-chain assignment:

* `anchor_lt` — causality: an anchor's timestamp is strictly below its
  child's (also rules out records at the sentinel id `0`);
* `anchor_real` — anchors are present: a non-sentinel anchor has its own
  insert record;
* `chain_zero`/`chain_step` — `chainOf` is the delta-chain of the birth
  tree: empty at the root, and a child's chain extends its anchor's by
  the timestamp gap.

Every honest fold of one event set provides these facts; the instance
wiring discharges them (steps 1–3 of the plan). -/
structure BirthEnv (s : _root_.concrete_st) (chainOf : ℕ → List ℕ) : Prop where
  anchor_lt : ∀ {c p : ℕ}, _root_.after_of s c p → p < c
  anchor_real : ∀ {c p : ℕ}, _root_.after_of s c p → p ≠ 0 → RealId s p
  chain_zero : chainOf 0 = []
  chain_step : ∀ {c p : ℕ}, _root_.after_of s c p →
    chainOf c = chainOf p ++ [c - p]

variable {s : _root_.concrete_st} {chainOf : ℕ → List ℕ}

theorem treeId_of_after (B : BirthEnv s chainOf) {c p : ℕ}
    (h : _root_.after_of s c p) : TreeId s p := by
  by_cases hp : p = 0
  · exact Or.inl hp
  · exact Or.inr (B.anchor_real h hp)

/-- Delta chains telescope: the chain of a tree node sums to the node's
timestamp. This is what makes chains injective names. -/
theorem sum_chain (B : BirthEnv s chainOf) :
    ∀ c, TreeId s c → (chainOf c).sum = c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rintro (rfl | ⟨p, hp⟩)
    · rw [B.chain_zero]; rfl
    · have hlt := B.anchor_lt hp
      have hsum := ih p hlt (treeId_of_after B hp)
      rw [B.chain_step hp, List.sum_append, hsum]
      simp
      omega

/-- Chains of tree nodes are positive (causality per level). -/
theorem posChain_of_treeId (B : BirthEnv s chainOf) :
    ∀ c, TreeId s c → PosChain (chainOf c) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rintro (rfl | ⟨p, hp⟩)
    · rw [B.chain_zero]; intro d hd; cases hd
    · rw [B.chain_step hp]
      intro d hd
      rcases List.mem_append.mp hd with h | h
      · exact ih p (B.anchor_lt hp) (treeId_of_after B hp) d h
      · have := B.anchor_lt hp
        simp at h
        omega

/-- **Chains are injective names** on the birth tree (via telescoping). -/
theorem chain_inj (B : BirthEnv s chainOf) {a b : ℕ}
    (ha : TreeId s a) (hb : TreeId s b)
    (h : chainOf a = chainOf b) : a = b := by
  have h1 := sum_chain B a ha
  rw [h, sum_chain B b hb] at h1
  exact h1.symm

theorem chain_ne_nil (B : BirthEnv s chainOf) {c : ℕ}
    (hc : RealId s c) : chainOf c ≠ [] := by
  obtain ⟨p, hp⟩ := hc
  rw [B.chain_step hp]
  simp

/-! ## chainBefore is a strict order (transitivity via the coordinates)

`chainBefore` inherits transitivity from the coordinate order: encode with
any `OrderedPrefixCode` (the unary code suffices), transport through
`display_iff_chainBefore`, and use `keyLt_trans`. The code proves the
order's transitivity — the representation paying rent upstairs. -/

theorem chainBefore_ne {c1 c2 : List ℕ} (h : chainBefore c1 c2) :
    c1 ≠ c2 := by
  cases h with
  | ancestor ch ext hne =>
      intro h
      have hlen := congrArg List.length h
      rw [List.length_append] at hlen
      exact hne (List.eq_nil_of_length_eq_zero (by omega))
  | newer p d e ch1 ch2 hlt =>
      intro h
      have := List.append_cancel_left h
      simp at this
      omega

theorem chainBefore_trans {c1 c2 c3 : List ℕ}
    (h1 : PosChain c1) (h2 : PosChain c2) (h3 : PosChain c3)
    (hb1 : chainBefore c1 c2) (hb2 : chainBefore c2 c3) :
    chainBefore c1 c3 := by
  have k1 := chainBefore_display unaryCode h1 h2 hb1
  have k2 := chainBefore_display unaryCode h2 h3 hb2
  have k13 := keyLt_trans k2 k1
  have hne13 : c1 ≠ c3 := by
    rintro rfl
    rw [keyLt_irrefl] at k13
    exact Bool.noConfusion k13
  exact (display_iff_chainBefore unaryCode h1 h3 hne13).mp k13

/-! ## Soundness: `visible_lt` derivations land in the chain order -/

/-- Walking `afters` upward only strips chain suffixes. -/
theorem reach_chain (B : BirthEnv s chainOf) {d c : ℕ}
    (h : _root_.afters_reach s d c) :
    ∃ ext, chainOf d = chainOf c ++ ext := by
  induction h with
  | refl c => exact ⟨[], by simp⟩
  | step hpc _ ih =>
      obtain ⟨ext, hext⟩ := ih
      exact ⟨ext ++ [_], by
        rw [B.chain_step hpc, hext, List.append_assoc]⟩

theorem real_of_reach {d c : ℕ} (h : _root_.afters_reach s d c)
    (hne : d ≠ c) : RealId s d := by
  cases h with
  | refl _ => exact absurd rfl hne
  | step hpc _ => exact ⟨_, hpc⟩

/-- **Soundness**: every `visible_lt` derivation is a chain-order verdict
(and its endpoints are birth-tree nodes). -/
theorem visible_lt_chainBefore (B : BirthEnv s chainOf) :
    ∀ {a b : ℕ}, _root_.visible_lt s a b →
      TreeId s a ∧ RealId s b ∧ chainBefore (chainOf a) (chainOf b) := by
  intro a b h
  induction h with
  | parent_child hpc =>
      refine ⟨treeId_of_after B hpc, ⟨_, hpc⟩, ?_⟩
      rw [B.chain_step hpc]
      exact chainBefore.ancestor _ _ (by simp)
  | sibling h1 h2 hne hgt =>
      refine ⟨Or.inr ⟨_, h1⟩, ⟨_, h2⟩, ?_⟩
      rw [B.chain_step h1, B.chain_step h2]
      have hl1 := B.anchor_lt h1
      have hl2 := B.anchor_lt h2
      exact chainBefore.newer _ _ _ [] [] (by omega)
  | left_descendant_of_sibling h1 h2 hne hgt hreach hdne =>
      obtain ⟨ext, hext⟩ := reach_chain B hreach
      refine ⟨Or.inr (real_of_reach hreach hdne), ⟨_, h2⟩, ?_⟩
      rw [hext, B.chain_step h1, B.chain_step h2, List.append_assoc]
      have hl1 := B.anchor_lt h1
      have hl2 := B.anchor_lt h2
      exact chainBefore.newer _ _ _ ext [] (by omega)
  | trans h1 h2 ih1 ih2 =>
      obtain ⟨ta, rx, cb1⟩ := ih1
      obtain ⟨_, ry, cb2⟩ := ih2
      exact ⟨ta, ry,
        chainBefore_trans (posChain_of_treeId B _ ta)
          (posChain_of_treeId B _ (Or.inr rx))
          (posChain_of_treeId B _ (Or.inr ry)) cb1 cb2⟩

/-! ## Completeness: chain-order verdicts are derivable -/

/-- **Every chain prefix is realized by an ancestor**, reachable along the
`afters` edges. The witness the `newer` case of completeness needs. -/
theorem prefix_real (B : BirthEnv s chainOf) :
    ∀ b, RealId s b → ∀ u v, chainOf b = u ++ v → u ≠ [] →
      ∃ b', RealId s b' ∧ chainOf b' = u ∧ _root_.afters_reach s b b' := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rintro ⟨p, hp⟩ u v huv hu
    rcases List.eq_nil_or_concat v with rfl | ⟨v', vl, rfl⟩
    · exact ⟨b, ⟨p, hp⟩, by simpa using huv, _root_.afters_reach.refl b⟩
    · simp only [List.concat_eq_append] at huv
      have hcomb : (u ++ v') ++ [vl] = chainOf p ++ [b - p] := by
        rw [List.append_assoc, ← huv]
        exact B.chain_step hp
      obtain ⟨huv', -⟩ := List.append_inj' hcomb rfl
      have hp0 : p ≠ 0 := by
        rintro rfl
        rw [B.chain_zero] at huv'
        rcases u with _ | ⟨x, xs⟩
        · exact hu rfl
        · simp at huv'
      obtain ⟨b', hb', hchain, hreach⟩ :=
        ih p (B.anchor_lt hp) (B.anchor_real hp hp0) u v' huv'.symm hu
      exact ⟨b', hb', hchain, _root_.afters_reach.step hp hreach⟩

/-- Reaching up the `afters` edges is a `visible_lt` verdict (ancestor
before descendant), by chaining `parent_child` through `trans`. -/
theorem visible_of_reach {b a : ℕ} (h : _root_.afters_reach s b a)
    (hne : b ≠ a) : _root_.visible_lt s a b := by
  induction h with
  | refl _ => exact absurd rfl hne
  | @step c cp anc hpc _ ih =>
      by_cases hcp : cp = anc
      · subst hcp
        exact _root_.visible_lt.parent_child hpc
      · exact _root_.visible_lt.trans (ih hcp)
          (_root_.visible_lt.parent_child hpc)

/-- Inversion of `chainBefore` into its two verdict shapes. -/
theorem chainBefore_inv {u v : List ℕ} (h : chainBefore u v) :
    (∃ ext, ext ≠ [] ∧ v = u ++ ext) ∨
    (∃ p d e c1 c2, e < d ∧ u = p ++ d :: c1 ∧ v = p ++ e :: c2) := by
  cases h with
  | ancestor ch ext hne => exact Or.inl ⟨ext, hne, rfl⟩
  | newer p d e c1 c2 hlt => exact Or.inr ⟨p, d, e, c1, c2, hlt, rfl, rfl⟩

/-- **Completeness**: every chain-order verdict between real ids is
derivable in `visible_lt`. -/
theorem chainBefore_visible_lt (B : BirthEnv s chainOf) {a b : ℕ}
    (ha : RealId s a) (hb : RealId s b)
    (hcb : chainBefore (chainOf a) (chainOf b)) :
    _root_.visible_lt s a b := by
  rcases chainBefore_inv hcb with ⟨ext, hne, hext⟩ |
    ⟨p, d, e, c1, c2, hlt, hu, hv⟩
  · -- ancestor: b realizes chainOf a as a prefix, hence reaches a
    obtain ⟨b', hb', hchain, hreach⟩ :=
      prefix_real B b hb (chainOf a) ext hext (chain_ne_nil B ha)
    have hba : b' = a := chain_inj B (Or.inr hb') (Or.inr ha) hchain
    subst hba
    have hne' : b ≠ b' := by
      rintro rfl
      have hlen := congrArg List.length hext
      rw [List.length_append] at hlen
      exact hne (List.eq_nil_of_length_eq_zero (by omega))
    exact visible_of_reach hreach hne'
  · -- newer: realize the two divergent children, then sibling verdicts
    obtain ⟨a₁, ha₁, hca₁, hra₁⟩ :=
      prefix_real B a ha (p ++ [d]) c1 (by rw [hu]; simp) (by simp)
    obtain ⟨b₁, hb₁, hcb₁, hrb₁⟩ :=
      prefix_real B b hb (p ++ [e]) c2 (by rw [hv]; simp) (by simp)
    obtain ⟨pa, hpa⟩ := ha₁
    obtain ⟨pb, hpb⟩ := hb₁
    have h1 : chainOf pa ++ [a₁ - pa] = p ++ [d] :=
      (B.chain_step hpa).symm.trans hca₁
    have h2 : chainOf pb ++ [b₁ - pb] = p ++ [e] :=
      (B.chain_step hpb).symm.trans hcb₁
    obtain ⟨hpa_chain, hd⟩ := List.append_inj' h1 rfl
    obtain ⟨hpb_chain, he⟩ := List.append_inj' h2 rfl
    have hd' : a₁ - pa = d := by simpa using hd
    have he' : b₁ - pb = e := by simpa using he
    have hpapb : pa = pb :=
      chain_inj B (treeId_of_after B hpa) (treeId_of_after B hpb)
        (hpa_chain.trans hpb_chain.symm)
    subst hpapb
    have hlta := B.anchor_lt hpa
    have hltb := B.anchor_lt hpb
    have hgt : a₁ > b₁ := by omega
    have hne₁ : a₁ ≠ b₁ := by omega
    have hstep1 : _root_.visible_lt s a b₁ := by
      by_cases haa : a = a₁
      · subst haa
        exact _root_.visible_lt.sibling hpa hpb hne₁ hgt
      · exact _root_.visible_lt.left_descendant_of_sibling
          hpa hpb hne₁ hgt hra₁ haa
    by_cases hbb : b = b₁
    · subst hbb
      exact hstep1
    · exact _root_.visible_lt.trans hstep1 (visible_of_reach hrb₁ hbb)

/-! ## The order equivalence -/

/-- **The read-equivalence order core**: on the birth
tree of a birth environment, the published RGA's visible order and the
embedded-chain RGA's chain order are the same relation. -/
theorem visible_lt_iff_chainBefore (B : BirthEnv s chainOf) {a b : ℕ}
    (ha : RealId s a) (hb : RealId s b) :
    _root_.visible_lt s a b ↔ chainBefore (chainOf a) (chainOf b) :=
  ⟨fun h => (visible_lt_chainBefore B h).2.2, chainBefore_visible_lt B ha hb⟩

/-- `visible_lt` is asymmetric on a birth environment (inherited from the
coordinate order's asymmetry — another fact the published side never
proved about its own relational read). -/
theorem visible_lt_asymm (B : BirthEnv s chainOf) {a b : ℕ}
    (h : _root_.visible_lt s a b) : ¬ _root_.visible_lt s b a := by
  intro h'
  obtain ⟨ta, rb, cb1⟩ := visible_lt_chainBefore B h
  obtain ⟨-, ra, cb2⟩ := visible_lt_chainBefore B h'
  have k1 := chainBefore_display unaryCode (posChain_of_treeId B _ ta)
    (posChain_of_treeId B _ (Or.inr rb)) cb1
  have k2 := chainBefore_display unaryCode (posChain_of_treeId B _ (Or.inr rb))
    (posChain_of_treeId B _ (Or.inr ra)) cb2
  rw [keyLt_asymm k1] at k2
  exact Bool.noConfusion k2

/-- `visible_lt` is total on distinct real ids (inherited from
`chainBefore_total` through the equivalence — the published RGA's
relational order is a strict total order on the birth tree, a fact the
published side never proved). -/
theorem visible_lt_total (B : BirthEnv s chainOf) {a b : ℕ}
    (ha : RealId s a) (hb : RealId s b) (hne : a ≠ b) :
    _root_.visible_lt s a b ∨ _root_.visible_lt s b a := by
  have hchne : chainOf a ≠ chainOf b :=
    fun h => hne (chain_inj B (Or.inr ha) (Or.inr hb) h)
  rcases chainBefore_total hchne with h | h
  · exact Or.inl ((visible_lt_iff_chainBefore B ha hb).mpr h)
  · exact Or.inr ((visible_lt_iff_chainBefore B hb ha).mpr h)

/-- **The two reads cannot disagree**: on any embed state whose
coordinates are chain-generated (`chainState`, the reachability
invariant) and any RGA† state forming a birth environment over the *same*
chains, the embed display order `before` and the published `visible_lt`
coincide on shared live ids. Instantiating both states as the two folds
of one honest event set is the remaining wiring. -/
theorem before_iff_visible_lt {α : Type} [DecidableEq α]
    (Γ : OrderedPrefixCode) (se : concrete_st α)
    (hcs : chainState Γ se chainOf) (B : BirthEnv s chainOf) {t1 t2 : ℕ}
    (h1 : contains se t1 = true) (h2 : contains se t2 = true)
    (hr1 : RealId s t1) (hr2 : RealId s t2) (hne : t1 ≠ t2) :
    before se t1 t2 ↔ _root_.visible_lt s t1 t2 := by
  have hchne : chainOf t1 ≠ chainOf t2 :=
    fun h => hne (chain_inj B (Or.inr hr1) (Or.inr hr2) h)
  rw [before_iff_chainBefore Γ se chainOf hcs h1 h2 hchne]
  exact (visible_lt_iff_chainBefore B hr1 hr2).symm

end Sal.EmbedRGA
