import Sal.ConditionedMRDTs.Framework.MRDTSig

/-!
# `noopFeasible`: the relaxed feasibility predicate

The feasibility notion of the conditioned metatheory: `loOnA + noopFeasible` is the
condition under which conditioned convergence holds.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-! ## §0  The relaxed feasibility predicate `noopFeasible`

`noopFeasible D π s` folds `π` from `s` and requires, at every prefix, that the next op is
`D.applicable` or acts as the identity (`D.update s o = s`) on the state reached so far.
This relaxes `applicabilityValid` (`G2_Applicability_Aware.lean`), whose clause is the
strict `D.applicable o s`. -/

/-- Every prefix-fold of `π` (from `s`) keeps the next op applicable OR a no-op there. -/
def noopFeasible (D : ConditionedMRDTSig) : List (Op D.AppOp) → D.State → Prop
  | [], _ => True
  | o :: rest, s => (D.applicable o s ∨ D.update s o = s) ∧ noopFeasible D rest (D.update s o)

end Sal.ConditionedMRDTs
