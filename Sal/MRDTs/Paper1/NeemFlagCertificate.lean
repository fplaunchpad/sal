import Sal.MRDTs.Paper1.EnableWinsFlagVC
import Sal.MRDTs.Paper1.NeemFlagEvent
import Sal.MRDTs.Paper1.SplitPolicy

/-! Both source polarities use one five-equation proof and independent Boolean
history machine. The exported split laws retain equal-operation commutation;
certification retains the concrete VC reconstruction and join induction. -/
namespace Sal.MRDTs.Paper1.NeemFlagEvent
open Foundation ConcreteMRDT Instances.NeemFlag

abbrev policy := NeemFlagReplay.policy

def splitLaws (initialFlag invert : Bool) :
    SplitPolicy.Laws (D initialFlag invert).toUpdateSig policy :=
  SplitPolicy.Laws.ofGuarded (laws initialFlag invert)

def conditions (initialFlag invert : Bool) :
    VCConditions policy (spec initialFlag invert) (generation initialFlag invert) where
  toVCReplayConditions := { NeemFlagVC.replayConditions initialFlag invert with
    laws := (splitLaws initialFlag invert).toGuarded }
  compatibility := compatible initialFlag invert
  historySound := historySound initialFlag invert

theorem certifiedV (initialFlag invert : Bool) :
    EventCertifiedSpecificationRAV (D initialFlag invert) policy
      (spec initialFlag invert) (generation initialFlag invert) := by
  intro C reach
  exact (conditions initialFlag invert).versionsV reach

theorem certified (initialFlag invert : Bool) :
    EventCertifiedSpecificationRA (D initialFlag invert) policy
      (spec initialFlag invert) (generation initialFlag invert) :=
  (certifiedV initialFlag invert).ordinary

#print axioms certifiedV
#print axioms splitLaws
end Sal.MRDTs.Paper1.NeemFlagEvent
