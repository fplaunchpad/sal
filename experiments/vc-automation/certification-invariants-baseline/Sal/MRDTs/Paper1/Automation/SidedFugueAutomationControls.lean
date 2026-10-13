import Sal.MRDTs.Paper1.Automation.OrderedAutomationControls
import Sal.MRDTs.Paper1.Automation.AutomatedFugue

/-! Independent kernel controls for unchanged Sided/archive data and derivation.
Each interface block has a concrete companion rejecting a degenerate map. -/
namespace Sal.MRDTs.Paper1.Automation.SidedFugueAutomationControls
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.SidedEmbedRGA OrderedRecords
set_option linter.unusedTactic false
variable (Γ : OrderedPrefixCode)

example : (AutomatedRGA.Sided.kit Γ).carrier = List.toFinset := by rfl
example : (AutomatedRGA.Sided.kit Γ).id = Prod.fst := by rfl
example : (AutomatedRGA.Sided.kit Γ).Key = List Nat := by rfl
example : (AutomatedRGA.Sided.kit Γ).key = (fun p => sKey p.2.2) := by rfl
example : (AutomatedRGA.Sided.kit Γ).insertion = sIsIns := by rfl
example : (AutomatedRGA.Sided.kit Γ).written = sRecOf Γ := by rfl
example : (AutomatedRGA.Sided.kit Γ).target = (fun e n => e.2.2 = .del n) := by rfl
example : (AutomatedRGA.Sided.kit Γ).ordered = SSorted := by rfl
example : (AutomatedRGA.Sided.kit Γ).id (1, 0, default) ≠ 0 := by change (1 : Nat) ≠ 0; decide

set_option maxHeartbeats 2000000 in
def freshSidedKit : Kit (S Γ) SRec := by
  derive_ordered_kit (AutomatedRGA.Sided.description Γ) unfolding
    [AutomatedRGA.Sided.description, S, sUpdate, sIds, sIsIns, sRecOf, sCoord, SSorted, sMerge]

#print axioms freshSidedKit

def constantSidedId : Description (S Γ) SRec :=
  { AutomatedRGA.Sided.description Γ with id := fun _ => 0 }
example : (constantSidedId Γ).id ((constantSidedId Γ).written (1, 0, .del 0)) ≠ 1 := by
  change (0 : Nat) ≠ 1; decide
set_option maxHeartbeats 2000000 in
example : True := by
  reject_ordered_derivation
    have wrong : Kit (S Γ) SRec := by
      derive_ordered_kit (constantSidedId Γ) unfolding
        [constantSidedId, AutomatedRGA.Sided.description, S, sUpdate, sIds, sIsIns, sRecOf, sCoord, SSorted, sMerge]
  trivial

open Instances.SidedEmbedRGA.FugueMax CertifiedFugueVCReplay
example : (AutomatedFugue.kit Γ).archive = State.births := by rfl
example : (AutomatedFugue.kit Γ).archive_written = recordOf := by rfl
example : (AutomatedFugue.kit Γ).archive_add = AutomatedFugue.insertion := by rfl
example : (AutomatedFugue.kit Γ).carrier = (fun s => s.live.toFinset) := by rfl
example : (AutomatedFugue.kit Γ).ordered = (fun s => SSorted s.live) := by rfl
example : (AutomatedFugue.kit Γ).id (1, 0, default) ≠ 0 := by change (1 : Nat) ≠ 0; decide
example : (AutomatedFugue.kit Γ).id = Prod.fst := by rfl
example : (AutomatedFugue.kit Γ).Key = List Nat := by rfl
example : (AutomatedFugue.kit Γ).key = (fun p => sKey p.2.2) := by rfl
example : (AutomatedFugue.kit Γ).insertion = AutomatedFugue.insertion := by rfl
example : (AutomatedFugue.kit Γ).written = AutomatedFugue.written Γ := by rfl
example : (AutomatedFugue.kit Γ).target = AutomatedFugue.target := by rfl

example : (AutomatedFugue.issuanceModel Γ).guard = applicable Γ := by rfl
example : (AutomatedFugue.issuanceModel Γ).valid = AutomatedFugue.ChainFacts := by rfl
example : (AutomatedFugue.issuanceModel Γ).archive = State.births := by rfl
example : (AutomatedFugue.issuanceModel Γ).live = (fun s => s.live.toFinset) := by rfl
example : (AutomatedFugue.issuanceModel Γ).record = recordOf := by rfl
example : (AutomatedFugue.issuanceModel Γ).written = AutomatedFugue.written Γ := by rfl
example : (AutomatedFugue.issuanceModel Γ).insertion = AutomatedFugue.insertion := by rfl
example : (AutomatedFugue.issuanceModel Γ).marked = mIsIns := by rfl
example : (AutomatedFugue.issuanceModel Γ).stamp = MRec.ts := by rfl
example : (AutomatedFugue.issuanceModel Γ).id = Prod.fst := by rfl
example : (AutomatedFugue.issuanceModel Γ).target = AutomatedFugue.target := by rfl
example : (AutomatedFugue.issuanceModel Γ).id (1, 0, default) ≠ 0 := by
  change (1 : Nat) ≠ 0; decide

end Sal.MRDTs.Paper1.Automation.SidedFugueAutomationControls
