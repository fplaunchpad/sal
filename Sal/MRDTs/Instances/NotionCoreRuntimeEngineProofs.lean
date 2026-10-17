import Sal.MRDTs.Instances.NotionCoreRuntimeEngine

/-! Receipt-side metadata preservation for the exact executable wrapper.
Core fact/index refinement is composed separately as those lemmas close. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeEngine
open NotionCorePayload (Transaction)

/-- Successful identity checking either retains an identical prior transaction
or observes its whole reservation. It cannot corrupt allocator bounds. -/
theorem receiveMetadata_valid (state next : NotionCoreRuntimeMetadata.State)
    (valid : NotionCoreRuntimeMetadata.Valid state) (tx : Transaction)
    (accepted : receiveMetadata state tx = .ok next) :
    NotionCoreRuntimeMetadata.Valid next := by
  unfold receiveMetadata at accepted
  split at accepted
  · split at accepted
    · cases accepted; exact valid
    · contradiction
  · cases accepted
    exact NotionCoreRuntimeMetadata.receive_valid state valid tx

theorem receiveMetadata_archive (state next : NotionCoreRuntimeMetadata.State)
    (tx : Transaction) (accepted : receiveMetadata state tx = .ok next) :
    next.archive.toFinset = insert tx state.archive.toFinset := by
  cases found : prior state tx with
  | none =>
    simp [receiveMetadata,found] at accepted
    subst next
    simp [NotionCoreRuntimeMetadata.receive]
  | some old =>
    by_cases equal : old = tx
    · have member : tx ∈ state.archive := equal ▸ List.mem_of_find?_eq_some found
      simp [receiveMetadata,found,equal] at accepted
      subst next
      simp [member]
    · simp [receiveMetadata,found,equal] at accepted

/-- Accepted receipt passed admission: the transaction carries no merge. -/
theorem receive_admitted {state next : State} {tx : Transaction}
    (accepted : receive state tx = .ok next) :
    admissible tx = true ∧ receiveAdmitted state tx = .ok next := by
  cases admitted : admissible tx with
  | false => simp [receive,admitted] at accepted
  | true => exact ⟨rfl,by simpa [receive,admitted] using accepted⟩

/-- Receipt refuses every merge transaction. -/
theorem receive_merge (state : State) (tx : Transaction) (source target : NotionCorePayload.BlockKey)
    (payload : tx.payload = .merge source target) : ∃ message, receive state tx = .error message :=
  ⟨"merge transactions are outside the executable scope",by simp [receive,admissible,payload]⟩

theorem receive_metadata_valid (state next : State)
    (valid : NotionCoreRuntimeMetadata.Valid state.metadata) (tx : Transaction)
    (accepted : receive state tx = .ok next) :
    NotionCoreRuntimeMetadata.Valid next.metadata := by
  replace accepted := (receive_admitted accepted).2
  unfold receiveAdmitted at accepted
  split at accepted
  · split at accepted
    · cases accepted; exact valid
    · contradiction
  · cases core : NotionCoreRuntimeState.receive state.core tx with
    | error message => simp [core] at accepted
    | ok result =>
      simp [core] at accepted
      subst next
      exact NotionCoreRuntimeMetadata.receive_valid state.metadata valid tx

theorem gap_metadata_valid (state : State)
    (valid : NotionCoreRuntimeMetadata.Valid state.metadata) (ticks : Nat) :
    NotionCoreRuntimeMetadata.Valid (gap state ticks).metadata :=
  NotionCoreRuntimeMetadata.gap_valid state.metadata valid ticks

theorem receiveMetadata_fold (txs : List Transaction)
    (state next : NotionCoreRuntimeMetadata.State)
    (valid : NotionCoreRuntimeMetadata.Valid state)
    (accepted : txs.foldlM receiveMetadata state = .ok next) :
    NotionCoreRuntimeMetadata.Valid next ∧
      next.archive.toFinset = state.archive.toFinset ∪ txs.toFinset := by
  induction txs generalizing state next with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at accepted
    subst next
    exact ⟨valid,by simp⟩
  | cons tx txs ih =>
    cases first : receiveMetadata state tx with
    | error message => simp [List.foldlM_cons,first, bind, Except.bind] at accepted
    | ok middle =>
      have rest : txs.foldlM receiveMetadata middle = .ok next := by
        simpa [List.foldlM_cons,first, bind, Except.bind] using accepted
      obtain ⟨preserved,archive⟩ := ih middle next
        (receiveMetadata_valid state middle valid tx first) rest
      refine ⟨preserved,?_⟩
      rw [archive,receiveMetadata_archive state middle tx first]
      simp [Finset.union_comm]

theorem merge_metadata (left right next : State)
    (valid : NotionCoreRuntimeMetadata.Valid left.metadata)
    (accepted : merge left right = .ok next) :
    NotionCoreRuntimeMetadata.Valid next.metadata ∧
      next.metadata.archive.toFinset =
        left.metadata.archive.toFinset ∪ right.metadata.archive.toFinset := by
  cases metadataResult : right.metadata.archive.foldlM receiveMetadata left.metadata with
  | error message => simp [merge,metadataResult, bind, Except.bind] at accepted
  | ok merged =>
    cases core : NotionCoreRuntimeState.merge left.core right.core with
    | error message => simp [merge,metadataResult,core, bind, Except.bind, pure, Except.pure] at accepted
    | ok combined =>
      simp [merge,metadataResult,core, bind, Except.bind, pure, Except.pure] at accepted
      subst next
      exact receiveMetadata_fold right.metadata.archive left.metadata merged valid metadataResult

#print axioms merge_metadata
#print axioms receiveMetadata_valid
#print axioms receiveMetadata_archive
#print axioms receive_metadata_valid
#print axioms receive_admitted
#print axioms receive_merge
end Sal.MRDTs.Instances.NotionCoreRuntimeEngine
