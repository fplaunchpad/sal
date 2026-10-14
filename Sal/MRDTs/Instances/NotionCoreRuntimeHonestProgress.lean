import Sal.MRDTs.Instances.NotionCoreRuntimeProgress
import Sal.MRDTs.Instances.NotionCoreRuntimeCompatibility

/-! Progress for the exact native receipt/direct-merge algorithms on one honest
allocated archive. Compatibility and transaction identity guards are derived;
local preparation and closed-version query meaning remain separate layers. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeHonestProgress
open NotionCorePayload (Transaction)
open NotionCoreRuntimeEngine (State Refines receive merge)
open NotionCoreStructuralFacts (Fact ofTransactions decode)

theorem identity_consistent (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) :
    NotionCoreRuntimeEngine.IdentityConsistent (network.entries.map (·.tx)) := by
  intro a ha b hb same
  exact List.inj_on_of_nodup_map (NotionCoreArchiveOrder.archive_keys_unique network reachable) ha hb same

private theorem facts_subset {localTxs allowed : List Transaction}
    (included : ∀ tx ∈ localTxs, tx ∈ allowed) : ofTransactions localTxs ⊆ ofTransactions allowed := by
  intro fact member
  simp only [ofTransactions,List.mem_toFinset,List.mem_flatMap] at member ⊢
  obtain ⟨tx,present,decoded⟩ := member
  exact ⟨tx,included tx present,decoded⟩

/-- A whole transaction from the common honest archive is accepted by the
actual wrapper, including late and duplicate receipt. No free compatibility
or successful receipt premise is required. -/
theorem receive_total (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network)
    (state : State) (valid : Refines state)
    (included : ∀ tx ∈ state.metadata.archive, tx ∈ network.entries.map (·.tx))
    (tx : Transaction) (published : tx ∈ network.entries.map (·.tx)) :
    ∃ next, receive state tx = .ok next ∧ Refines next := by
  apply NotionCoreRuntimeEngine.receive_total (network.entries.map (·.tx))
    (identity_consistent network reachable) state valid included tx published
  apply NotionCoreRuntimeCompatibility.honest_subset_compatible network reachable
  rw [valid.2.2]
  intro fact member
  rcases Finset.mem_union.mp member with old | fresh
  · exact facts_subset included old
  · simp only [decode,List.mem_toFinset] at fresh
    simp only [ofTransactions,List.mem_toFinset,List.mem_flatMap]
    exact ⟨tx,published,fresh⟩

/-- Direct native merge accepts any two represented subarchives of one honest
archive. Duplicate facts and reservation identities retain their original
meaning; each retained index and allocator metadata invariant is preserved. -/
theorem merge_total (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network)
    (left right : State) (lv : Refines left) (rv : Refines right)
    (li : ∀ tx ∈ left.metadata.archive, tx ∈ network.entries.map (·.tx))
    (ri : ∀ tx ∈ right.metadata.archive, tx ∈ network.entries.map (·.tx)) :
    ∃ next, merge left right = .ok next ∧ Refines next := by
  apply NotionCoreRuntimeEngine.merge_total (network.entries.map (·.tx))
    (identity_consistent network reachable) left right lv rv li ri
  apply NotionCoreRuntimeCompatibility.honest_subset_compatible network reachable
  rw [lv.2.2,rv.2.2]
  exact Finset.union_subset (facts_subset li) (facts_subset ri)

/-- The exact batch path used by the native driver accepts any enumeration
of complete transactions from the common honest archive. Order need not be
source-key order; receipt integrates immutable facts without transaction replay. -/
theorem receiveMany_total (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network)
    (state : State) (valid : Refines state)
    (included : ∀ tx ∈ state.metadata.archive, tx ∈ network.entries.map (·.tx))
    (txs : List Transaction) (published : ∀ tx ∈ txs, tx ∈ network.entries.map (·.tx)) :
    ∃ next, NotionCoreRuntimeEngine.receiveMany state txs = .ok next ∧ Refines next ∧
      next.metadata.archive.toFinset = state.metadata.archive.toFinset ∪ txs.toFinset := by
  induction txs generalizing state with
  | nil => exact ⟨state,rfl,valid,by simp⟩
  | cons tx rest ih =>
      obtain ⟨middle,first,mv⟩ := receive_total network reachable state valid included tx
        (published tx (by simp))
      have includedMiddle : ∀ item ∈ middle.metadata.archive, item ∈ network.entries.map (·.tx) := by
        intro item member
        have archive := NotionCoreRuntimeEngine.receive_archive tx first
        have selected : item ∈ insert tx state.metadata.archive.toFinset := by
          rw [← archive]
          simpa using member
        simp only [Finset.mem_insert,List.mem_toFinset] at selected
        rcases selected with rfl | old
        · exact published item (by simp)
        · exact included item old
      obtain ⟨next,tail,nv,_⟩ := ih middle mv includedMiddle
        (fun item member => published item (by simp [member]))
      have accepted : NotionCoreRuntimeEngine.receiveMany state (tx :: rest) = .ok next := by
        simpa [NotionCoreRuntimeEngine.receiveMany,List.foldlM_cons,first,bind,Except.bind] using tail
      exact ⟨next,accepted,nv,(NotionCoreRuntimeEngine.receiveMany_refines valid _ accepted).2⟩

/-- Positional-client reachability is the original honest protocol source.
It derives the weaker allocation/archive assumptions used by receipt progress. -/
theorem receive_honest (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network)
    (state : State) (valid : Refines state)
    (included : ∀ tx ∈ state.metadata.archive, tx ∈ network.entries.map (·.tx))
    (tx : Transaction) (published : tx ∈ network.entries.map (·.tx)) :
    ∃ next, receive state tx = .ok next ∧ Refines next :=
  receive_total network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    state valid included tx published

theorem merge_honest (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network)
    (left right : State) (lv : Refines left) (rv : Refines right)
    (li : ∀ tx ∈ left.metadata.archive, tx ∈ network.entries.map (·.tx))
    (ri : ∀ tx ∈ right.metadata.archive, tx ∈ network.entries.map (·.tx)) :
    ∃ next, merge left right = .ok next ∧ Refines next :=
  merge_total network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    left right lv rv li ri

theorem receiveMany_honest (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network)
    (state : State) (valid : Refines state)
    (included : ∀ tx ∈ state.metadata.archive, tx ∈ network.entries.map (·.tx))
    (txs : List Transaction) (published : ∀ tx ∈ txs, tx ∈ network.entries.map (·.tx)) :
    ∃ next, NotionCoreRuntimeEngine.receiveMany state txs = .ok next ∧ Refines next ∧
      next.metadata.archive.toFinset = state.metadata.archive.toFinset ∪ txs.toFinset :=
  receiveMany_total network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    state valid included txs published

#print axioms receiveMany_honest
#print axioms identity_consistent
#print axioms receive_honest
#print axioms merge_honest
end Sal.MRDTs.Instances.NotionCoreRuntimeHonestProgress
