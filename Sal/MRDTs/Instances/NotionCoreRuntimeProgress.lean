import Sal.MRDTs.Instances.NotionCoreRuntimeRefinement

/-! Progress of the actual wrapper, separately from successful-result refinement.
The common allowed archive is later supplied by the existing honest protocol.
Receipt progress covers merge-free transactions; merges are refused on receipt. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeEngine
open NotionCorePayload (Transaction)

def IdentityConsistent (allowed : List Transaction) : Prop :=
  ∀ a ∈ allowed, ∀ b ∈ allowed, a.id = b.id → a = b

theorem receiveMetadata_total (allowed : List Transaction)
    (unique : IdentityConsistent allowed) (state : NotionCoreRuntimeMetadata.State)
    (included : ∀ tx ∈ state.archive, tx ∈ allowed) (tx : Transaction) (member : tx ∈ allowed) :
    ∃ next, receiveMetadata state tx = .ok next := by
  cases found : prior state tx with
  | none => exact ⟨NotionCoreRuntimeMetadata.receive state tx,by simp [receiveMetadata,found]⟩
  | some old =>
    have oldMember : old ∈ state.archive := List.mem_of_find?_eq_some found
    have idEq : old.id = tx.id := by
      have h := List.find?_some found
      simpa [prior] using h
    have equal := unique old (included old oldMember) tx member idEq
    exact ⟨state,by simp [receiveMetadata,found,equal]⟩

theorem receiveMetadata_fold_total (allowed : List Transaction)
    (unique : IdentityConsistent allowed) (txs : List Transaction)
    (state : NotionCoreRuntimeMetadata.State)
    (included : ∀ tx ∈ state.archive, tx ∈ allowed)
    (incoming : ∀ tx ∈ txs, tx ∈ allowed) :
    ∃ next, txs.foldlM receiveMetadata state = .ok next := by
  induction txs generalizing state with
  | nil => exact ⟨state,rfl⟩
  | cons tx txs ih =>
    obtain ⟨middle,first⟩ := receiveMetadata_total allowed unique state included tx
      (incoming tx (by simp))
    have middleIncluded : ∀ item ∈ middle.archive, item ∈ allowed := by
      intro item member
      have archive := receiveMetadata_archive state middle tx first
      have member' : item ∈ insert tx state.archive.toFinset := by
        rw [← archive]; simpa using member
      simp only [Finset.mem_insert,List.mem_toFinset] at member'
      rcases member' with rfl | previous
      · exact incoming item (by simp)
      · exact included item previous
    obtain ⟨next,rest⟩ := ih middle middleIncluded (fun item member => incoming item (by simp [member]))
    exact ⟨next,by simp [List.foldlM_cons,first,bind,Except.bind,rest]⟩

theorem receive_total (allowed : List Transaction) (unique : IdentityConsistent allowed)
    (state : State) (valid : Refines state)
    (included : ∀ tx ∈ state.metadata.archive, tx ∈ allowed)
    (tx : Transaction) (member : tx ∈ allowed) (notMerge : NotionCoreMergeFree.NotMerge tx)
    (compatible : NotionCoreRuntimeState.Compatible
      (NotionCoreRuntimeState.abstract state.core ∪ NotionCoreStructuralFacts.decode tx)) :
    ∃ next, receive state tx = .ok next ∧ Refines next := by
  have existsNext : ∃ next, receive state tx = .ok next := by
    simp only [receive,admissible_of_notMerge notMerge,if_true]
    cases found : prior state.metadata tx with
    | none =>
      obtain ⟨core,accepted⟩ := NotionCoreRuntimeState.receive_total state.core valid.1 tx compatible
      exact ⟨⟨core,NotionCoreRuntimeMetadata.receive state.metadata tx⟩,by simp [receiveAdmitted,found,accepted]⟩
    | some old =>
      have oldMember := List.mem_of_find?_eq_some found
      have idEq : old.id = tx.id := by
        have h := List.find?_some found
        simpa [prior] using h
      have equal := unique old (included old oldMember) tx member idEq
      exact ⟨state,by simp [receiveAdmitted,found,equal,pure,Except.pure]⟩
  obtain ⟨next,accepted⟩ := existsNext
  exact ⟨next,accepted,receive_refines valid tx accepted⟩

theorem merge_total (allowed : List Transaction) (unique : IdentityConsistent allowed)
    (left right : State) (lv : Refines left) (rv : Refines right)
    (li : ∀ tx ∈ left.metadata.archive, tx ∈ allowed)
    (ri : ∀ tx ∈ right.metadata.archive, tx ∈ allowed)
    (compatible : NotionCoreRuntimeState.Compatible
      (NotionCoreRuntimeState.abstract left.core ∪ NotionCoreRuntimeState.abstract right.core)) :
    ∃ next, merge left right = .ok next ∧ Refines next := by
  obtain ⟨metadata,metaAccepted⟩ := receiveMetadata_fold_total allowed unique
    right.metadata.archive left.metadata li ri
  obtain ⟨core,coreAccepted⟩ := NotionCoreRuntimeState.merge_total left.core right.core lv.1 compatible
  have accepted : merge left right = .ok ⟨core,metadata⟩ := by
    simp [merge,metaAccepted,coreAccepted,bind,Except.bind,pure,Except.pure]
  exact ⟨_,accepted,merge_refines lv rv accepted⟩

#print axioms receive_total
#print axioms merge_total
end Sal.MRDTs.Instances.NotionCoreRuntimeEngine
