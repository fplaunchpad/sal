import Sal.MRDTs.Instances.NotionCoreAtomicFormattingEffects
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalForest

/-! A formatting endpoint's earlier item provider remains physically present
through later deletion, split and merge. The provider comes from source mint
provenance; the actual prefix storage and traversal follow from the existing
plain protocol proof. No endpoint/read-coordinate invariant is assumed. -/
namespace Sal.MRDTs.Instances.NotionCoreRichRetainedProviders
open NotionRunAllocation (Run Id)
open NotionCorePayload (Transaction BlockKey reservation)
open NotionCorePayloadNetwork (Entry Reach)
open NotionCoreOriginTree (Item preorder)

theorem prefix_birth_row (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List Run) (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (actual : NotionCoreMachine.State) (replayed : NotionCoreMachine.replay {} pre = some actual)
    (inst : BlockKey) (id : Id) (provider : Entry) (published : provider ∈ network.entries)
    (earlier : reservation provider.tx ∈ pre.map reservation)
    (born : (inst,id) ∈ NotionCorePayloadNetwork.birthAddresses provider.tx) :
    id ∈ (NotionCoreMachine.getInstance actual (NotionCoreMachine.blockName inst)).rows.map
      (fun row => row.item.id) := by
  let deleted : BlockKey → Id → Bool := fun _ id => decide (id ∈ NotionCoreTableView.targets pre inst)
  rw [← NotionCorePayloadNetwork.birthAddresses_deleted provider.tx deleted] at born
  obtain ⟨birth,present,equal⟩ := List.mem_map.mp born
  have instanceEq := congrArg Prod.fst equal
  have idEq := congrArg Prod.snd equal
  have located : (inst,birth.2) ∈ NotionCorePayload.births provider.tx deleted := by
    have pairEq : birth = (inst,birth.2) := Prod.ext instanceEq rfl
    exact pairEq ▸ present
  have prefixMember := (NotionCorePayloadParents.prefix_row_member network.entries
    (pre.map reservation) inst deleted birth.2).mpr ⟨provider,published,earlier,located⟩
  have actualMember := (NotionCoreMachineVersionTables.version_prefix_rows_perm network reachable
    version pre suffix position actual replayed inst).mem_iff.mpr prefixMember
  exact List.mem_map.mpr ⟨birth.2,actualMember,idEq⟩

theorem prefix_birth_forest (network : NotionCorePayloadNetwork.State) (reachable : Reach network)
    (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (inst : BlockKey) (id : Id) (provider : Entry) (published : provider ∈ network.entries)
    (earlier : reservation provider.tx ∈ pre.map reservation)
    (born : (inst,id) ∈ NotionCorePayloadNetwork.birthAddresses provider.tx) :
    id ∈ (preorder (NotionCoreAtomicFormattingMachine.instanceForest actual
      (NotionCoreMachine.blockName inst))).map Item.id := by
  have row := prefix_birth_row network reachable version pre suffix position actual.core replayed
    inst id provider published earlier born
  have model := NotionCoreMachineCanonicalForest.canonical_forest_version network reachable
    version closed pre suffix position actual.core replayed inst
  have graph := NotionCoreMachineVersionTables.version_table_graph network reachable
    version closed pre suffix position actual.core replayed inst
  have traversal := NotionCoreParentCoupling.edges_traversal _ _ model.1 graph.1 model.2
  have rowsToForest := (model.1.map (fun row => row.item.id)).mem_iff.mp row
  have inForest : id ∈ (preorder (NotionCoreMachineCanonicalForest.originForest actual.core inst)).map Item.id := by
    simpa only [NotionCoreParentCoupling.forestRows_ids] using rowsToForest
  rw [NotionCoreAtomicFormattingEffects.storedItems_forest]
  change id ∈ (NotionCoreMachine.traversal _ _ .start).map Item.id
  rw [NotionCoreMachine.traversal_correct,traversal]
  exact inForest

#print axioms prefix_birth_row
#print axioms prefix_birth_forest
end Sal.MRDTs.Instances.NotionCoreRichRetainedProviders
