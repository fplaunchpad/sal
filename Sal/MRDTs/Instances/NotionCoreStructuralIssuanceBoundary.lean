import Sal.MRDTs.Instances.NotionCoreStructuralFacts
import Sal.MRDTs.Instances.NotionCoreMachineNetwork
import Sal.MRDTs.Instances.NotionCoreMachineBootstrap

/-! The direct document-fact projection intentionally forgets reservation
identity for pure erasure. Honest allocator metadata must remain outside this
projection. This is a representation/admission boundary, not a core bug. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralIssuanceBoundary
open NotionCorePayload (Transaction)
open NotionCorePayloadNetwork (State)
open NotionCoreMachineNetwork (Reach issue)

def seed : State := NotionCorePayloadNetwork.seeded [97,98]
def delayed : State := NotionCorePayloadNetwork.gap seed [65] 6
def eraseAt (counter : Nat) : Transaction :=
  ⟨⟨counter,[65]⟩,.erase .initial [(.initial,[⟨1,[65]⟩])]⟩
private def document := NotionCoreMachineBootstrap.seeded [97,98]
def low : State := NotionCorePayloadNetwork.emit seed [65] (eraseAt 3).payload (eraseAt 3)
def high : State := NotionCorePayloadNetwork.emit delayed [65] (eraseAt 9).payload (eraseAt 9)
def facts (state : State) : NotionCoreStructuralFacts.State :=
  NotionCoreStructuralFacts.ofTransactions (state.entries.map (·.tx))
def nextCounter (state : State) : Nat :=
  (NotionRunAllocation.reserve (state.allocation.peers [65]) [65] 1).first.counter

private theorem seed_document : NotionCoreReconstruction.reconstruct seed [65] = some document := by
  simp only [seed,NotionCoreReconstruction.reconstruct,NotionCoreReconstruction.transactions,
    NotionCorePayloadNetwork.seeded,List.map_cons,List.map_nil,List.filter_cons,List.filter_nil]
  decide +kernel
private theorem delayed_document : NotionCoreReconstruction.reconstruct delayed [65] = some document := by
  simp only [delayed,seed,NotionCorePayloadNetwork.gap,NotionCoreReconstruction.reconstruct,
    NotionCoreReconstruction.transactions,NotionCorePayloadNetwork.seeded,
    List.map_cons,List.map_nil,List.filter_cons,List.filter_nil]
  decide +kernel
private theorem selected : NotionCoreMachineNetwork.prepareRequest document (.erase .initial 0 1) =
    some (eraseAt 3).payload := by decide +kernel

theorem low_issued : issue seed [65] (.erase .initial 0 1) = some low := by
  have prepared : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget seed) [65] (eraseAt 3).payload =
      some (eraseAt 3) := by decide +kernel
  simp [issue,NotionCoreMachineNetwork.Request.earlyNoop,seed_document,selected,prepared,low]

theorem high_issued : issue delayed [65] (.erase .initial 0 1) = some high := by
  have prepared : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget delayed) [65] (eraseAt 3).payload =
      some (eraseAt 9) := by decide +kernel
  simp [issue,NotionCoreMachineNetwork.Request.earlyNoop,delayed_document,selected,prepared,high]
  rfl

theorem low_reachable : Reach low :=
  .request [65] (.erase .initial 0 1) (.bootstrap [97,98]) low_issued
theorem high_reachable : Reach high :=
  .request [65] (.erase .initial 0 1) (.gap [65] 6 (.bootstrap [97,98])) high_issued

/-- Both executions actually delete the same a, retaining b. Their archives
and reservation clocks differ while their immutable document facts coincide. -/
theorem fact_clock_control :
    facts low = facts high ∧
    NotionCoreStructuralFacts.Fact.erased .initial ⟨1,[65]⟩ ∈ facts low ∧
    facts low ≠ facts seed ∧
    (low.allocation.peers [65]).clock = 3 ∧
    (high.allocation.peers [65]).clock = 9 ∧
    (low.allocation.peers [65]).clock ≠ (high.allocation.peers [65]).clock := by
  decide +kernel

/-- Equal facts authorize different next source counters under the original
honest allocator. Counter 4 is accepted only in the low-clock execution. -/
theorem next_counter_control :
    nextCounter low = 4 ∧ nextCounter high = 10 ∧
    nextCounter low ≠ nextCounter high ∧ nextCounter high ≠ 4 ∧
    NotionCorePayload.prepare (NotionCorePayloadNetwork.forget low) [65] (.create none) =
      some ⟨⟨4,[65]⟩,.create none⟩ ∧
    NotionCorePayload.prepare (NotionCorePayloadNetwork.forget high) [65] (.create none) ≠
      some ⟨⟨4,[65]⟩,.create none⟩ := by decide +kernel

/-- No function of document facts alone can recover the original allocator's
next counter on all honestly request-reachable states. -/
theorem next_counter_not_from_facts :
    ¬ ∃ recover : NotionCoreStructuralFacts.State → Nat,
      ∀ state, Reach state → recover (facts state) = nextCounter state := by
  rintro ⟨recover,correct⟩
  have equal := fact_clock_control.1
  have lowNext := correct low low_reachable
  have highNext := correct high high_reachable
  rw [equal] at lowNext
  exact next_counter_control.2.2.1 (lowNext.symm.trans highNext)

#print axioms low_reachable
#print axioms high_reachable
#print axioms fact_clock_control
#print axioms next_counter_control
#print axioms next_counter_not_from_facts
end Sal.MRDTs.Instances.NotionCoreStructuralIssuanceBoundary
