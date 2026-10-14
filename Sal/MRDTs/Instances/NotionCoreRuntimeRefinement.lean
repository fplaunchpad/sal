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

/-- Representation invariant for the actual executable state. -/
def Refines (state : State) : Prop :=
  NotionCoreRuntimeState.Valid state.core ∧
  NotionCoreRuntimeMetadata.Valid state.metadata ∧
  NotionCoreRuntimeState.abstract state.core =
    NotionCoreStructuralFacts.ofTransactions state.metadata.archive

theorem empty_refines : Refines empty := by
  exact ⟨NotionCoreRuntimeState.empty_valid,NotionCoreRuntimeMetadata.empty_valid,
    NotionCoreRuntimeState.empty_abstract⟩

theorem gap_refines {state : State} (valid : Refines state) (ticks : Nat) :
    Refines (gap state ticks) :=
  ⟨valid.1,gap_metadata_valid state valid.2.1 ticks,valid.2.2⟩

theorem receive_refines {state next : State} (valid : Refines state) (tx : Transaction)
    (accepted : receive state tx = .ok next) : Refines next := by
  cases found : prior state.metadata tx with
  | some old =>
    by_cases equal : old = tx
    · simp [receive,found,equal,pure,Except.pure] at accepted
      subst next
      exact valid
    · simp [receive,found,equal,pure,Except.pure] at accepted
  | none =>
    cases received : NotionCoreRuntimeState.receive state.core tx with
    | error message => simp [receive,found,received] at accepted
    | ok core =>
      simp [receive,found,received] at accepted
      subst next
      refine ⟨NotionCoreRuntimeState.receive_valid valid.1 tx received,
        NotionCoreRuntimeMetadata.receive_valid state.metadata valid.2.1 tx,?_⟩
      rw [NotionCoreRuntimeState.receive_abstract tx received,valid.2.2]
      simp [NotionCoreRuntimeMetadata.receive,Finset.union_comm]

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
      refine ⟨NotionCoreRuntimeState.merge_valid lv.1 coreResult,metadataValid,?_⟩
      rw [NotionCoreRuntimeState.merge_abstract coreResult,lv.2.2,rv.2.2]
      have same : merged.archive.toFinset =
          (left.metadata.archive ++ right.metadata.archive).toFinset := by
        simpa using archive
      rw [Facts.congr same,NotionCoreStructuralFacts.ofTransactions_append]

theorem receive_archive {state next : State} (tx : Transaction)
    (accepted : receive state tx = .ok next) :
    next.metadata.archive.toFinset = insert tx state.metadata.archive.toFinset := by
  cases found : prior state.metadata tx with
  | some old =>
    by_cases equal : old = tx
    · have member : tx ∈ state.metadata.archive := equal ▸ List.mem_of_find?_eq_some found
      simp [receive,found,equal,pure,Except.pure] at accepted
      subst next
      simp [member]
    · simp [receive,found,equal] at accepted
  | none =>
    cases received : NotionCoreRuntimeState.receive state.core tx with
    | error message => simp [receive,found,received] at accepted
    | ok core =>
      simp [receive,found,received] at accepted
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

#print axioms receiveMany_refines
#print axioms receive_refines
#print axioms merge_refines
end Sal.MRDTs.Instances.NotionCoreRuntimeEngine
