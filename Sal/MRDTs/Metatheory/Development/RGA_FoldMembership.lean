import Sal.MRDTs.Metatheory.Conditioned.RGA_NoopFeasible_CanonFold

/-!
# Fold membership — a live node stays live absent a delete of it

*Additive; modifies no existing file; 0 `sorry`.*

hEnum step C, foundation.  For the noopFeasibility of the δ-enum we need each insert's anchor live at
its prefix fold.  The primitive fact: `contains` is only ever removed by a `Del` of that exact id —
`Ins` and unrelated `Del`s preserve it.  So a node live at the LCA fold `σ₀` stays live through any
prefix that contains no delete of it (`contains_applySeqR_of_no_del`).  With the delete-deferred order
(anchor-killers placed after their inserts) this delivers anchor-liveness at each insert's point.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAFoldMembership

open Sal.Emulation
open RGAMergeLinearization (applySeqR applySeqR_cons)

/-- `o` deletes id `k` (its removal from the domain): `o` is a `Del` targeting `k`. -/
def deletesId (o : op_t) (k : ℕ) : Prop := ∃ t r p, o = (t, r, app_op_t.Del p k)

/-- **One step preserves a live node unless it deletes it.**  `Ins` only adds; a `Del` of `x ≠ k`
leaves `k`; only `Del k` removes `k`. -/
theorem contains_do_of_no_del (s : concrete_st) (o : op_t) (k : ℕ)
    (hlive : contains s k = true) (hnd : ¬ deletesId o k) :
    contains (do_ s o) k = true := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p a =>
    have hdo : do_ s (t, r, app_op_t.Ins e p a) = upd s t (e, resolve s (a :: p)) := by
      simp only [do_]
    rw [hdo, lemma_InDomUpd1, hlive]; simp
  | Del p x =>
    rw [contains_doDel]
    have hkx : k ≠ x := by rintro rfl; exact hnd ⟨t, r, p, rfl⟩
    rw [hlive]; simp [hkx]

/-- **A live node stays live through a delete-free-of-it prefix.**  Iterating
`contains_do_of_no_del`: if `k` is live in `s` and no op in `L` deletes `k`, then `k` is live in the
whole fold `applySeqR s L`.  (Anchor-liveness for LCA-created anchors under the delete-deferred order.) -/
theorem contains_applySeqR_of_no_del (s : concrete_st) (L : List op_t) (k : ℕ)
    (hlive : contains s k = true) (hnd : ∀ o ∈ L, ¬ deletesId o k) :
    contains (applySeqR s L) k = true := by
  induction L generalizing s with
  | nil => simpa using hlive
  | cons o rest ih =>
    rw [applySeqR_cons]
    exact ih (do_ s o) (contains_do_of_no_del s o k hlive (hnd o (List.mem_cons_self ..)))
      (fun o' ho' => hnd o' (List.mem_cons_of_mem o ho'))

/-! ## `IsAncPath` preservation — an intact chain survives ops that don't touch it -/

/-- **A `upd` off the chain preserves `IsAncPath`.**  `upd σ t v` changes only `t`'s entry, so a chain
avoiding `t` keeps its `anc`/`contains` structure.  (No freshness needed — just `t ∉ z :: p`.) -/
theorem isAncPath_upd_off (σ : concrete_st) (t : ℕ) (v : ℕ × ℕ) :
    ∀ (p : List ℕ) (z : ℕ), t ∉ z :: p → IsAncPath σ z p → IsAncPath (upd σ t v) z p := by
  intro p
  induction p with
  | nil =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    have hzt : z ≠ t := by rintro rfl; exact hz (by simp)
    have hsel : sel (upd σ t v) z = sel σ z :=
      lemma_SelUpd2 σ z t v (by simp only [bne_iff_ne, ne_eq]; exact fun e => hzt e.symm)
    simp only [anc, hsel]; exact h
  | cons q qs ih =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    have hzt : z ≠ t := by rintro rfl; exact hz (by simp)
    have hsel : sel (upd σ t v) z = sel σ z :=
      lemma_SelUpd2 σ z t v (by simp only [bne_iff_ne, ne_eq]; exact fun e => hzt e.symm)
    refine ⟨by simp only [anc, hsel]; exact h1, by rw [lemma_InDomUpd1, h2]; simp, ?_⟩
    exact ih q (fun hm => hz (List.mem_cons_of_mem z hm)) h3

/-- **A `Del` off the chain preserves `IsAncPath`.**  `do_ σ (Del x)` only removes `x` and reparents
`x`'s children; a chain with `x ∉ z :: p` and `x ≠ 0` (so the root-anchored deepest node is untouched)
keeps its structure. -/
theorem isAncPath_doDel_off (σ : concrete_st) (t r x : ℕ) (pre : List ℕ) (hx0 : x ≠ 0) :
    ∀ (p : List ℕ) (z : ℕ), x ∉ z :: p → IsAncPath σ z p →
      IsAncPath (do_ σ (t, r, app_op_t.Del pre x)) z p := by
  intro p
  induction p with
  | nil =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    rw [anc_doDel, h, if_neg (Ne.symm hx0)]
  | cons q qs ih =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    have hqx : q ≠ x := by rintro rfl; exact hz (by simp)
    refine ⟨?_, ?_, ?_⟩
    · rw [anc_doDel, h1, if_neg hqx]
    · rw [contains_doDel, h2]; simp [hqx]
    · exact ih q (fun hm => hz (List.mem_cons_of_mem z hm)) h3

/-- An op that neither creates nor deletes a node of the chain `L` (a fresh `Ins` writes a new id ∉ L;
a `Del` targets `x ∉ L`, `x ≠ 0`). -/
def chainSafe (o : op_t) (L : List ℕ) : Prop :=
  match o with
  | (t, _, app_op_t.Ins _ _ _) => t ∉ L
  | (_, _, app_op_t.Del _ x)   => x ∉ L ∧ x ≠ 0

/-- **One `chainSafe` step preserves `IsAncPath`.**  Dispatches to the `upd`/`Del` off-chain lemmas. -/
theorem isAncPath_do_of_chainSafe (σ : concrete_st) (o : op_t) (z : ℕ) (p : List ℕ)
    (hsafe : chainSafe o (z :: p)) (h : IsAncPath σ z p) :
    IsAncPath (do_ σ o) z p := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p2 a2 =>
    have hdo : do_ σ (t, r, app_op_t.Ins e p2 a2) = upd σ t (e, resolve σ (a2 :: p2)) := by
      simp only [do_]
    rw [hdo]; exact isAncPath_upd_off σ t _ p z hsafe h
  | Del p2 x =>
    exact isAncPath_doDel_off σ t r x p2 hsafe.2 p z hsafe.1 h

/-- **A `chainSafe` prefix preserves `IsAncPath`.**  If every op in `L` is `chainSafe` for `z :: p`, an
intact chain in `σ` stays intact through the whole fold. -/
theorem isAncPath_applySeqR_of_chainSafe (σ : concrete_st) (L : List op_t) (z : ℕ) (p : List ℕ)
    (hsafe : ∀ o ∈ L, chainSafe o (z :: p)) (h : IsAncPath σ z p) :
    IsAncPath (applySeqR σ L) z p := by
  induction L generalizing σ with
  | nil => simpa using h
  | cons o rest ih =>
    rw [applySeqR_cons]
    exact ih (do_ σ o) (fun o' ho' => hsafe o' (List.mem_cons_of_mem o ho'))
      (isAncPath_do_of_chainSafe σ o z p (hsafe o (List.mem_cons_self ..)) h)

/-- A `chainSafe` op does not delete any node of the chain. -/
theorem not_deletesId_of_chainSafe (o : op_t) (L : List ℕ) (k : ℕ)
    (hs : chainSafe o L) (hk : k ∈ L) : ¬ deletesId o k := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p a => rintro ⟨t', r', p', heq⟩; simp at heq
  | Del p x =>
    rintro ⟨t', r', p', heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, _, hop⟩ := heq
    injection hop with _ hxk
    subst hxk; exact hs.1 hk

/-- **An LCA-anchored insert stays accurate at any `chainSafe` prefix.**  Composes the two
preservation primitives: with the anchor chain `a :: p` intact at the LCA fold `σ₀` and every prefix op
`chainSafe` for it (no delete of a chain node, no id-clash), `contains … a` (via
`contains_applySeqR_of_no_del`) and `IsAncPath … a p` (via `isAncPath_applySeqR_of_chainSafe`) both
survive — i.e. the insert is `accurate` at its prefix fold.  The per-insert accuracy obligation of
step C, for anchors present in the LCA. -/
theorem ins_accurate_at_prefix_of_lca_chain (σ₀ : concrete_st) (pfx : List op_t)
    (t r e a : ℕ) (p : List ℕ)
    (hca : contains σ₀ a = true) (hpath : IsAncPath σ₀ a p)
    (hsafe : ∀ o ∈ pfx, chainSafe o (a :: p)) :
    accurate (t, r, app_op_t.Ins e p a) (applySeqR σ₀ pfx) := by
  have hcontains : contains (applySeqR σ₀ pfx) a = true :=
    contains_applySeqR_of_no_del σ₀ pfx a hca
      (fun o ho => not_deletesId_of_chainSafe o (a :: p) a (hsafe o ho) (by simp))
  have hisanc : IsAncPath (applySeqR σ₀ pfx) a p :=
    isAncPath_applySeqR_of_chainSafe σ₀ pfx a p hsafe hpath
  simp only [accurate, opLeaf, opPath]
  exact Or.inr ⟨hcontains, hisanc⟩

#print axioms contains_do_of_no_del
#print axioms contains_applySeqR_of_no_del
#print axioms isAncPath_upd_off
#print axioms isAncPath_doDel_off
#print axioms isAncPath_applySeqR_of_chainSafe
#print axioms not_deletesId_of_chainSafe
#print axioms ins_accurate_at_prefix_of_lca_chain

end Sal.Metatheory.RGAFoldMembership
