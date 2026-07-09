import Sal.ConditionedMRDTs.Development.RGA_NoopFeasible_CanonFold
import Sal.ConditionedMRDTs.MRDT_Instances.RGA.RGA_LoOnEq_Causal

/-!
# `noopFeasible` forces accuracy — every insert has a live anchor at its point

*Additive; modifies no existing file; 0 `sorry`.*

δ-A, step 1 (the visibility content, enumeration-level).  In a `noopFeasible` fold, the delivery
disjunct at each prefix is `applicable o s ∨ update s o = s`.  For an `Ins` with a *fresh* id the no-op
branch is impossible (`do_` writes the id), so the disjunct collapses to `applicable = accurate ∧
fresh_ts`: **every insert in a `noopFeasible` fold is accurate at its own prefix fold** — its anchor
chain is genuinely live there.  Consequently a delete of an insert's anchor can never precede that
insert in a `noopFeasible` enumeration (it would leave the anchor dead, killing accuracy).  This is the
`¬vis(Del(x), Ins-on-x)` content of δ-A at the enumeration level, with NO commutation reasoning.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGANoopFeasibleAccurate

open Sal.Emulation
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig')

/-- **Prefix extraction for `noopFeasible`.**  The delivery disjunct holds at every prefix fold: from
`noopFeasible D (pfx ++ o :: rest) s`, the op `o` is `applicable`-or-no-op at `applySeq s pfx`. -/
theorem noopFeasible_head_at {D : ConditionedMRDTSig} (pfx : List (Op D.AppOp)) (o : Op D.AppOp)
    (rest : List (Op D.AppOp)) (s : D.State)
    (h : noopFeasible D (pfx ++ o :: rest) s) :
    D.applicable o (applySeq D.toCRDTSig s pfx) ∨
      D.update (applySeq D.toCRDTSig s pfx) o = applySeq D.toCRDTSig s pfx := by
  induction pfx generalizing s with
  | nil => exact h.1
  | cons p ps ih =>
    have h' : noopFeasible D (ps ++ o :: rest) (D.update s p) := h.2
    simpa [applySeq] using ih (D.update s p) h'

/-- **Every insert in a `noopFeasible` fold is accurate at its point.**  Given the insert's id is fresh
at the prefix fold (`contains … t = false` — supplied by id-uniqueness of the enumeration), the no-op
delivery branch is impossible (`do_` writes `t`), so `applicable = accurate ∧ fresh_ts` holds; take the
`accurate` conjunct. -/
theorem ins_accurate_of_noopFeasible (pfx rest : List op_t) (s : concrete_st)
    (t r e a : ℕ) (p : List ℕ)
    (hnf : noopFeasible RGACondSig' (pfx ++ (t, r, app_op_t.Ins e p a) :: rest) s)
    (htf : contains (applySeq RGACondSig'.toCRDTSig s pfx) t = false) :
    accurate (t, r, app_op_t.Ins e p a) (applySeq RGACondSig'.toCRDTSig s pfx) := by
  set σ := applySeq RGACondSig'.toCRDTSig s pfx with hσ
  rcases noopFeasible_head_at (D := RGACondSig') pfx (t, r, app_op_t.Ins e p a) rest s hnf
    with happ | hnoop
  · exact happ.1
  · exfalso
    have hupd : RGACondSig'.update σ (t, r, app_op_t.Ins e p a) = do_ σ (t, r, app_op_t.Ins e p a) := rfl
    have hcontra : contains (do_ σ (t, r, app_op_t.Ins e p a)) t = true := by
      simp only [do_]; rw [lemma_InDomUpd1]; simp
    rw [hupd] at hnoop
    rw [hnoop, htf] at hcontra
    exact absurd hcontra (by simp)

/-- **An insert's anchor is live at its point.**  Corollary of accuracy: the non-root leaf of a
`noopFeasible` insert is contained at its prefix fold.  (`accurate`'s root disjunct is excluded by
`a ≠ 0`.)  So a delete that removed the anchor cannot have run in the prefix — the enumeration-level
form of `¬vis(Del(anchor), Ins)`, established WITHOUT any commutation. -/
theorem ins_anchor_live_of_noopFeasible (pfx rest : List op_t) (s : concrete_st)
    (t r e a : ℕ) (p : List ℕ) (ha0 : a ≠ 0)
    (hnf : noopFeasible RGACondSig' (pfx ++ (t, r, app_op_t.Ins e p a) :: rest) s)
    (htf : contains (applySeq RGACondSig'.toCRDTSig s pfx) t = false) :
    contains (applySeq RGACondSig'.toCRDTSig s pfx) a = true := by
  have hacc := ins_accurate_of_noopFeasible pfx rest s t r e a p hnf htf
  simp only [accurate, opLeaf, opPath] at hacc
  rcases hacc with ⟨hleaf0, _⟩ | ⟨hcont, _⟩
  · exact absurd hleaf0 ha0
  · exact hcont

#print axioms noopFeasible_head_at
#print axioms ins_accurate_of_noopFeasible
#print axioms ins_anchor_live_of_noopFeasible

end Sal.ConditionedMRDTs.RGANoopFeasibleAccurate
