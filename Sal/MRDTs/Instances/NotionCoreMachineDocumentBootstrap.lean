import Sal.MRDTs.Instances.NotionCoreMachineDocumentInsert
import Sal.MRDTs.Instances.NotionCoreMachineDocumentCreate
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
import Sal.MRDTs.Instances.NotionCoreMachineCommands

/-! Bootstrap source-document simulation in arbitrary honest canonical
context. Bootstrap is not assumed to be the first replayed transaction. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocumentBootstrap
open NotionCoreMachine
open NotionCoreSource (Atom)
open NotionCorePayload (BlockKey Transaction)

/-- Initial text integration also covers the empty seed, whose insertion is
an atomic bootstrap phase rather than an ordinary empty client request. -/
theorem empty_instance_insert (state : State) (key : BlockKey)
    (first : NotionRunAllocation.Id) (atoms : List Nat)
    (empty : getInstance state (blockName key) = {}) :
    ∃ next, applyOperation state (.insert key key first .start atoms) = some next ∧
      physical next (blockName key) = NotionCorePartition.spliceAfterBy Atom.address
        (blockName key,.start)
        ((NotionCorePayload.textItems first atoms (fun _ => false)).map
          (NotionCorePhysicalReplay.atom (blockName key))) (physical state (blockName key)) := by
  cases decoded : NotionCorePayload.textItems first atoms (fun _ => false) with
  | nil =>
    have nilRows : NotionCoreParentMap.runRows .start
        (NotionCorePayload.textItems first atoms (fun _ => false)) = [] := by rw [decoded]; rfl
    let next := putInstance state (blockName key) {}
    refine ⟨next,?_,?_⟩
    · simp [applyOperation,empty,nilRows,next,integrateRows]
    · simp [next,physical,NotionCoreMachineTables.getInstance_put,empty,
        NotionCorePhysicalReplay.physical,NotionCorePhysicalReplay.start,
        NotionCorePartition.spliceAfterBy]
  | cons head rest =>
    have newUnique : ((head :: rest).map NotionCoreOriginTree.Item.id).Nodup := by
      have unique := NotionCorePayloadNetwork.birth_ids_unique
        (⟨first,.bootstrap atoms⟩ : Transaction) (fun _ _ => false)
      simpa [NotionCorePayload.births,NotionCorePayload.operations,NotionCorePayload.Operation.births,
        NotionCorePayload.birthId,NotionCorePayload.runRows_ids,decoded,List.map_map,Function.comp_def]
        using unique
    obtain ⟨next,operation,physicalEq⟩ := NotionCoreMachineSplice.insert_text_physical
      state key key first .start atoms head rest (by simp [empty,decoded]) .nil
      (by simp [empty,NotionCoreParentMap.ParentEdges,NotionCoreParentMap.forestRows])
      (by simp [empty,NotionCoreParentMap.Unique]) trivial newUnique
      (by simp [empty]) (by simp [NotionCoreOriginTree.Ready,NotionCoreOriginTree.Forest.roots]) trivial
    exact ⟨next,operation,by simpa [decoded,NotionCorePhysicalReplay.originAddress] using physicalEq⟩

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- Canonical bootstrap executes in an arbitrary earlier honest context and
is simulated by the existing create/insert source execution. Neither an empty
old machine nor bootstrap-first order nor a final projection is a premise. -/
theorem canonical_bootstrap_source_execution (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (document : NotionCoreSourceDocument.Document)
    (old : NotionCoreMachineDocument.materializeDocument state = some document)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    ∃ next after, applyTransaction state tx = some next ∧
      NotionCoreMachineDocument.materializeDocument next = some after ∧
      NotionCoreSourceDocument.Execution document (NotionCoreMachineCommands.commands tx) after := by
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have networkReach := NotionCoreCreatorNetwork.payload_reachable creators
  obtain ⟨checked,checkedReplay,part,shape,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct network reachable peer pre (tx :: suffix) position
  have stateEq : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreBootstrapProvenance.canonical_bootstrap_fresh
    network creators peer pre suffix tx position atoms payload state accepted
  obtain ⟨created,createStep,createdPart⟩ := NotionCoreMachinePartitionCreate.create_partitioned
    state .initial none part freshInstance freshBlock
  have createdShape := NotionCoreMachineShape.fresh_create_shape_preserves state created .initial none
    shape freshInstance freshBlock createStep
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names]) accepted
  obtain ⟨createdDoc,createdMat,createSource⟩ := NotionCoreMachineDocumentCreate.fresh_create_document
    state created .initial none freshInstance freshBlock createStep aligned document old (by simp)
  have createdPhysical := NotionCoreMachineCanonicalCreate.fresh_create_physical state created .initial none
    freshInstance freshBlock createStep
  have createdStorage := NotionCoreMachineCanonicalCreate.fresh_create_storage state created .initial none
    freshInstance freshBlock createStep
  have createdEmpty : getInstance created 0 = {} := by simpa [blockName] using createdStorage 0
  obtain ⟨next,insertStep,physicalEq⟩ := empty_instance_insert created .initial tx.id atoms createdEmpty
  have transaction : applyTransaction state tx = some next := by
    simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,createStep,insertStep]
  have nextReplay : replay {} (pre ++ [tx]) = some next := by
    rw [replay_append,accepted]
    simp [replay,transaction]
  have nextPosition : NotionCoreReconstruction.transactions network peer = (pre ++ [tx]) ++ suffix := by
    simpa [List.append_assoc] using position
  have oldUnique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network networkReach
    peer pre (tx :: suffix) position state accepted
  have nextUnique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network networkReach
    peer (pre ++ [tx]) suffix nextPosition next nextReplay
  have createdUnique : ∀ key, ((physical created key).map Atom.address).Nodup := by
    intro key
    by_cases selected : key = 0
    · subst key
      have emptyPhysical : physical created 0 = NotionCoreSliceForest.emptyPhysical 0 := by
        simpa only [blockName] using createdPhysical.1
      rw [emptyPhysical]
      simp [NotionCoreSliceForest.emptyPhysical]
    · rw [createdPhysical.2 key selected]
      exact oldUnique key
  have nextEq : ∃ rows, next = putInstance created 0
      {getInstance created 0 with rows := rows} := by
    cases integrated : integrateRows (getInstance created 0).rows
        (NotionCoreParentMap.runRows .start (NotionCorePayload.textItems tx.id atoms
          (fun id => decide (id ∈ (getInstance created 0).pending)))) with
    | none => simp [applyOperation,blockName,integrated] at insertStep
    | some rows => exact ⟨rows,by simpa [applyOperation,blockName,integrated] using insertStep.symm⟩
  obtain ⟨rows,nextEq⟩ := nextEq
  have createdLayout := NotionCoreMachineCanonicalCreate.fresh_create_shape state created .initial none
    freshInstance freshBlock createStep
  have stored : ∃ entry ∈ created.instances, entry.1 = 0 := by
    rw [createdLayout.1]
    simp [blockName]
  have present : (0,NotionCoreSpec.LocalId.start) ∈ (physical created 0).map Atom.address := by
    have emptyPhysical : physical created 0 = NotionCoreSliceForest.emptyPhysical 0 := by
      simpa only [blockName] using createdPhysical.1
    rw [emptyPhysical]
    simp [NotionCoreSliceForest.emptyPhysical,NotionCorePartition.boundary]
  have createdAligned := NotionCoreMachineDisplay.operation_aligned state created (.create .initial none)
    aligned createStep
  have active : NotionCoreMachineShape.ActiveInstance created 0 := by
    refine ⟨⟨0,NotionCoreSliceForest.freshTitle 0⟩,?_,rfl⟩
    rw [createdLayout.2.1]
    simp [blockName]
  have available := NotionCoreMachineDocumentInsert.materialized_origin_available created createdPart
    createdShape createdAligned createdUnique createdDoc createdMat 0 active (0,.start) present
  obtain ⟨after,afterMat,insertSource⟩ := NotionCoreMachineDocumentInsert.insert_source_step created next
    createdPart createdShape.1 createdDoc createdMat 0 (0,.start)
    ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map (NotionCorePhysicalReplay.atom 0)) rfl
    createdUnique nextUnique (by
      intro key oldExists
      rw [nextEq]
      have oldStored : ∃ entry ∈ created.instances, entry.1 = key := by simpa using oldExists
      have result := (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created 0 key
        {getInstance created 0 with rows := rows} stored).mpr oldStored
      simpa using result) present physicalEq (by
        intro key distinct
        rw [nextEq]
        simp [physical,NotionCoreMachineTables.getInstance_put,distinct])
    (by rw [nextEq]; unfold putInstance; split <;> rfl)
    (by rw [nextEq]; unfold putInstance; split <;> rfl) available
  have createGuard := NotionCoreMachineDocumentInvariant.accepted_source_guard state part oldUnique shape
    aligned document createdDoc old (.create 0 0 none) createSource
  have insertGuard := NotionCoreMachineDocumentInvariant.accepted_source_guard created createdPart createdUnique
    createdShape createdAligned createdDoc after createdMat
    (.insert (0,.start) ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map
      (NotionCorePhysicalReplay.atom 0))) insertSource
  refine ⟨next,after,transaction,afterMat,?_⟩
  simpa only [NotionCoreMachineCommands.commands,payload,NotionCoreMachineCommands.text] using
    (NotionCoreSourceDocument.Execution.cons createGuard createSource
      (.cons insertGuard insertSource (.nil after)))

namespace SPOT
private def earlier : Transaction := ⟨⟨1,[64]⟩,.create none⟩
private def earlierName := blockName (.issued earlier.id)
/-- Both creations insert at the display front: even an empty later
bootstrap retains its new title before the pre-existing independent block. -/
theorem later_empty_bootstrap_control :
    (replay {} [earlier,NotionCorePayload.bootstrap []] >>= render) =
      some [(0,[]),(earlierName,[])] ∧
    (replay {} [earlier,NotionCorePayload.bootstrap []] >>= render) ≠ some [(0,[])] ∧
    (replay {} [earlier,NotionCorePayload.bootstrap []] >>= render) ≠
      some [(earlierName,[]),(0,[])] := by decide +kernel
end SPOT

#print axioms SPOT.later_empty_bootstrap_control
#print axioms canonical_bootstrap_source_execution
#print axioms empty_instance_insert
end Sal.MRDTs.Instances.NotionCoreMachineDocumentBootstrap
