import Sal.MRDTs.Paper1.ORSet
import Sal.MRDTs.Instances.EfficientORSet

/-! Hand-derived negative controls for dropping compatible-history premises.
These are not counterexamples to the guarded production VCs. -/
namespace NeemExpansionControls
open Sal.MRDTs.Foundation

namespace Exact
open Sal.MRDTs.Paper1.ORSet
def old : State Nat := {(7, 1)}
def remove : Op (Update Nat) := (2, 0, .remove 7)

theorem missing_causal_base :
    merge ∅ old (step ∅ remove) = old ∧
    step old remove = ∅ ∧
    merge ∅ old (step ∅ remove) ≠ step old remove := by decide
end Exact

namespace Efficient
open Sal.MRDTs.Instances.EfficientORSet
def old : State Nat := {(0, 1, 7)}
def add : Op (SetOp Nat) := (2, 0, .add 7)

theorem missing_causal_base :
    merge ∅ old (update ∅ add) = {(0, 1, 7), (0, 2, 7)} ∧
    update old add = {(0, 2, 7)} ∧
    merge ∅ old (update ∅ add) ≠ update old add := by decide

def earlier : Op (SetOp Nat) := (1, 0, .add 7)
theorem policy_is_not_event_commutation :
    rc.order earlier add = .Either ∧
    update (update ∅ earlier) add = {(0, 2, 7)} ∧
    update (update ∅ add) earlier = {(0, 1, 7)} ∧
    update (update ∅ earlier) add ≠ update (update ∅ add) earlier := by decide
end Efficient
end NeemExpansionControls
