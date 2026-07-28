import Sal.ConditionedMRDTs.Framework.MRDTSig

/-!
# `loOnC` — the set-relative conditioned linearization order

`Sal.ConditionedMRDTs.lo` (`MRDTSig.lean`) made set-relative: `Sal.Emulation.loOn`
(`Merge_Linearization_Set.lean`) with `commutes ↦ commutesOn`.  This is the
baseline order of the conditioned update layer; the applicability-aware
refinement `loOnA` lives in `ConditionedConvergence.lean`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- The set-relative conditioned linearization order: `Sal.Emulation.loOn`
(`Merge_Linearization_Set.lean:159`) with `commutes ↦ commutesOn`, the relation
the conditioned update layer runs `convergence_on_u` against (mirrors
`Sal.ConditionedMRDTs.lo`, `MRDTSig.lean:89`, made set-relative). -/
def loOnC (D : ConditionedMRDTSig) (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) : Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutesOn e₁ e₂)
  ∨ ( ¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ ev, C.vis e₂ e₃ ∧ ¬ D.commutesOn e₂ e₃ )

end Sal.ConditionedMRDTs
