import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.BornApplicable_Guard
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance_Final

/-!
# The remaining quotient VC at the born-applicable guard `WfOpA`

*Additive; modifies no existing file; 0 `sorry`, kernel-clean.*

The re-base guards the quotient with `WfOpA = WfOpQ ∧ accurate`.  Three of the four
quotient VCs transfer immediately: `InvPres` is `rgaInvPresA`
(`BornApplicable_Guard`); `CongVC` is guard-independent (`(rgaCongVC' α)`); the
`WfOpReachable` guard-transparency shifts to `GuardNoopChain`
(`applySeqW_eq_applySeq_of_guardNoop`).  The last is `InvInvVC` — `WfOpA` is
`≈`-invariant because it is the conjunction of two `≈`-invariant predicates
(`WfOpQ` via `rgaInvInvVCQ`, `accurate` via `accurate_eq_iff`).
-/

namespace Sal.ConditionedMRDTs.RGAInstance

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstanceFinal (rgaInvInvVCQ)

/-- **`InvInvVC (RGACondSig' α) (rgaEqEquiv' α) WfOpA`.**  `wf_congr`: `WfOpA = WfOpQ ∧
accurate` is `≈`-invariant as a conjunction — `WfOpQ`-congruence from
`rgaInvInvVCQ`, `accurate`-congruence from `accurate_eq_iff`.  `applicable_congr`
is guard-independent (reused from `rgaInvInvVCQ`). -/
def rgaInvInvVCA : InvInvVC (RGACondSig' α) (rgaEqEquiv' α) WfOpA where
  wf_congr := by
    intro o s s' Is Is' h
    exact and_congr (rgaInvInvVCQ.wf_congr o Is Is' h)
      (RGAEqQuotient.accurate_eq_iff o h)
  applicable_congr := rgaInvInvVCQ.applicable_congr

#print axioms rgaInvInvVCA

end Sal.ConditionedMRDTs.RGAInstance
