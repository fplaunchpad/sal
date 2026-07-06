import Sal.MRDTs.Metatheory.Development.RGA_NoopFeasible_CanonFold

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

#print axioms contains_do_of_no_del
#print axioms contains_applySeqR_of_no_del

end Sal.Metatheory.RGAFoldMembership
