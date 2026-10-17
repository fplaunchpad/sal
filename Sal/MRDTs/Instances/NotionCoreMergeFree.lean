import Sal.MRDTs.Instances.NotionCoreReconstruction

/-! The merge-free fragment of the payload network: no archived transaction
carries a merge payload. The fact-set structural carrier and the executable
runtime query are proved on this fragment. An order-free fact query cannot
evaluate a merge, since a merge's effect depends on which blocks are alive when
it replays. -/
namespace Sal.MRDTs.Instances.NotionCoreMergeFree
open NotionCorePayload (Transaction)
open NotionCorePayloadNetwork (State)

/-- The transaction carries no merge payload. -/
def NotMerge (tx : Transaction) : Prop := ∀ source target, tx.payload ≠ .merge source target

/-- No archived transaction of the network carries a merge payload. -/
def MergeFree (network : State) : Prop := ∀ entry ∈ network.entries, NotMerge entry.tx

theorem initial : MergeFree NotionCorePayloadNetwork.initial := by
  simp [MergeFree, NotionCorePayloadNetwork.initial]

theorem seeded (atoms : List Nat) : MergeFree (NotionCorePayloadNetwork.seeded atoms) := by
  intro entry member source target
  simp only [NotionCorePayloadNetwork.seeded, List.mem_singleton] at member
  subst entry
  simp [NotionCorePayload.bootstrap]

@[simp] theorem exchange_iff (network : State) (target source : NotionRunAllocation.Session) :
    MergeFree (NotionCorePayloadNetwork.exchange network target source) ↔ MergeFree network := Iff.rfl

@[simp] theorem gap_iff (network : State) (session : NotionRunAllocation.Session) (ticks : Nat) :
    MergeFree (NotionCorePayloadNetwork.gap network session ticks) ↔ MergeFree network := Iff.rfl

theorem emit_iff (network : State) (session : NotionRunAllocation.Session)
    (payload : NotionCorePayload.Payload) (tx : Transaction) :
    MergeFree (NotionCorePayloadNetwork.emit network session payload tx) ↔ NotMerge tx ∧ MergeFree network := by
  simp [MergeFree, NotionCorePayloadNetwork.emit]

/-- Every transaction of a closed version of a merge-free network is merge-free. -/
theorem transactionsFor (network : State) (free : MergeFree network)
    (version : List NotionRunAllocation.Run) :
    ∀ tx ∈ NotionCoreReconstruction.transactionsFor network version, NotMerge tx := by
  intro tx member
  simp only [NotionCoreReconstruction.transactionsFor, List.mem_mergeSort, List.mem_filter,
    List.mem_map] at member
  obtain ⟨⟨entry, present, rfl⟩, _⟩ := member
  exact free entry present

#print axioms transactionsFor
end Sal.MRDTs.Instances.NotionCoreMergeFree
