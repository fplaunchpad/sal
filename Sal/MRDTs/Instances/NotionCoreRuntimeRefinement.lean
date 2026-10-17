import Sal.MRDTs.Instances.NotionCoreRuntimeEngineProofs
import Sal.MRDTs.Instances.NotionCoreRuntimeStateProofs

/-! The executable wrapper's retained archive and indexed facts describe the
same version. Success premises are separate from honest-domain progress. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeEngine
open NotionCorePayload (Transaction)
namespace Facts
open NotionCoreStructuralFacts

theorem congr {a b : List Transaction} (same : a.toFinset = b.toFinset) :
    ofTransactions a = ofTransactions b := by
  apply Finset.ext
  intro fact
  have members : ∀ tx, tx ∈ a ↔ tx ∈ b := by
    intro tx
    have := Finset.ext_iff.mp same tx
    simpa using this
  simp only [ofTransactions, List.mem_toFinset, List.mem_flatMap]
  simp only [members]
end Facts

/-- The retained archive carries no merge transaction. -/
def ArchiveMergeFree (state : State) : Prop :=
  ∀ tx ∈ state.metadata.archive, NotionCoreMergeFree.NotMerge tx

/-- Representation invariant for the actual executable state. The archive is
merge-free because receipt refuses merge transactions. -/
def Refines (state : State) : Prop :=
  NotionCoreRuntimeState.Valid state.core ∧
  NotionCoreRuntimeMetadata.Valid state.metadata ∧
  NotionCoreRuntimeState.abstract state.core =
    NotionCoreStructuralFacts.ofTransactions state.metadata.archive ∧
  ArchiveMergeFree state

/-- Every archive the runtime holds is merge-free. -/
theorem received_merge_free {state : State} (valid : Refines state) : ArchiveMergeFree state :=
  valid.2.2.2

theorem empty_refines : Refines empty := by
  refine ⟨NotionCoreRuntimeState.empty_valid,NotionCoreRuntimeMetadata.empty_valid,
    NotionCoreRuntimeState.empty_abstract,?_⟩
  intro tx member
  simp [empty,NotionCoreRuntimeMetadata.empty] at member

theorem gap_refines {state : State} (valid : Refines state) (ticks : Nat) :
    Refines (gap state ticks) :=
  ⟨valid.1,gap_metadata_valid state valid.2.1 ticks,valid.2.2.1,valid.2.2.2⟩

theorem receive_refines {state next : State} (valid : Refines state) (tx : Transaction)
    (accepted : receive state tx = .ok next) : Refines next := by
  obtain ⟨admitted,accepted⟩ := receive_admitted accepted
  cases found : prior state.metadata tx with
  | some old =>
    by_cases equal : old = tx
    · simp [receiveAdmitted,found,equal,pure,Except.pure] at accepted
      subst next
      exact valid
    · simp [receiveAdmitted,found,equal,pure,Except.pure] at accepted
  | none =>
    cases received : NotionCoreRuntimeState.receive state.core tx with
    | error message => simp [receiveAdmitted,found,received] at accepted
    | ok core =>
      simp [receiveAdmitted,found,received] at accepted
      subst next
      refine ⟨NotionCoreRuntimeState.receive_valid valid.1 tx received,
        NotionCoreRuntimeMetadata.receive_valid state.metadata valid.2.1 tx,?_,?_⟩
      · rw [NotionCoreRuntimeState.receive_abstract tx received,valid.2.2.1]
        simp [NotionCoreRuntimeMetadata.receive,Finset.union_comm]
      · intro item member
        simp only [NotionCoreRuntimeMetadata.receive,List.mem_cons] at member
        rcases member with rfl | old
        · exact admissible_notMerge admitted
        · exact valid.2.2.2 item old

theorem merge_refines {left right next : State} (lv : Refines left) (rv : Refines right)
    (accepted : merge left right = .ok next) : Refines next := by
  obtain ⟨metadataValid,archive⟩ := merge_metadata left right next lv.2.1 accepted
  cases metadataResult : right.metadata.archive.foldlM receiveMetadata left.metadata with
  | error message => simp [merge,metadataResult,bind,Except.bind] at accepted
  | ok merged =>
    cases coreResult : NotionCoreRuntimeState.merge left.core right.core with
    | error message => simp [merge,metadataResult,coreResult,bind,Except.bind] at accepted
    | ok combined =>
      simp [merge,metadataResult,coreResult,bind,Except.bind,pure,Except.pure] at accepted
      subst next
      have same : merged.archive.toFinset =
          (left.metadata.archive ++ right.metadata.archive).toFinset := by
        simpa using archive
      refine ⟨NotionCoreRuntimeState.merge_valid lv.1 coreResult,metadataValid,?_,?_⟩
      · rw [NotionCoreRuntimeState.merge_abstract coreResult,lv.2.2.1,rv.2.2.1]
        rw [Facts.congr same,NotionCoreStructuralFacts.ofTransactions_append]
      · intro tx member
        have joined : tx ∈ (left.metadata.archive ++ right.metadata.archive).toFinset := by
          rw [← same]; simpa using member
        simp only [List.mem_toFinset,List.mem_append] at joined
        rcases joined with fromLeft | fromRight
        · exact lv.2.2.2 tx fromLeft
        · exact rv.2.2.2 tx fromRight

theorem receive_archive {state next : State} (tx : Transaction)
    (accepted : receive state tx = .ok next) :
    next.metadata.archive.toFinset = insert tx state.metadata.archive.toFinset := by
  replace accepted := (receive_admitted accepted).2
  cases found : prior state.metadata tx with
  | some old =>
    by_cases equal : old = tx
    · have member : tx ∈ state.metadata.archive := equal ▸ List.mem_of_find?_eq_some found
      simp [receiveAdmitted,found,equal,pure,Except.pure] at accepted
      subst next
      simp [member]
    · simp [receiveAdmitted,found,equal] at accepted
  | none =>
    cases received : NotionCoreRuntimeState.receive state.core tx with
    | error message => simp [receiveAdmitted,found,received] at accepted
    | ok core =>
      simp [receiveAdmitted,found,received] at accepted
      subst next
      simp [NotionCoreRuntimeMetadata.receive]

/-- The actual batched receipt entry point preserves the invariant and adds
exactly the supplied transaction set, irrespective of order and duplicates. -/
theorem receiveMany_refines {state next : State} (valid : Refines state)
    (txs : List Transaction) (accepted : receiveMany state txs = .ok next) :
    Refines next ∧ next.metadata.archive.toFinset = state.metadata.archive.toFinset ∪ txs.toFinset := by
  induction txs generalizing state next with
  | nil =>
    simp [receiveMany,List.foldlM,pure,Except.pure] at accepted
    subst next
    exact ⟨valid,by simp⟩
  | cons tx txs ih =>
    cases first : receive state tx with
    | error message => simp [receiveMany,List.foldlM_cons,first,bind,Except.bind] at accepted
    | ok middle =>
      have rest : receiveMany middle txs = .ok next := by
        simpa [receiveMany,List.foldlM_cons,first,bind,Except.bind] using accepted
      obtain ⟨preserved,archive⟩ := ih (receive_refines valid tx first) rest
      refine ⟨preserved,?_⟩
      rw [archive,receive_archive tx first]
      simp [Finset.union_comm]

/-- Every transaction of an accepted batch passed admission, so a batch
containing a merge transaction is refused as a whole. -/
theorem receiveMany_merge_free {state next : State} (txs : List Transaction)
    (accepted : receiveMany state txs = .ok next) : ∀ tx ∈ txs, NotionCoreMergeFree.NotMerge tx := by
  induction txs generalizing state with
  | nil => simp
  | cons tx txs ih =>
    cases first : receive state tx with
    | error message => simp [receiveMany,List.foldlM_cons,first,bind,Except.bind] at accepted
    | ok middle =>
      have rest : receiveMany middle txs = .ok next := by
        simpa [receiveMany,List.foldlM_cons,first,bind,Except.bind] using accepted
      intro item member
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · exact admissible_notMerge (receive_admitted first).1
      · exact ih rest item later

#print axioms receiveMany_refines
#print axioms receiveMany_merge_free
#print axioms receive_refines
#print axioms merge_refines
#print axioms received_merge_free
end Sal.MRDTs.Instances.NotionCoreRuntimeEngine
