import Sal.MRDTs.Instances.NotionCoreMachinePartitionUpdates
import Sal.MRDTs.Instances.NotionCoreMachineCanonicalCreate

/-! Actual bootstrap create+insert succeeds for every source iterator atom
list, including empty seed. The single title owns the entire physical instance.
No replay acceptance or output representation is a premise. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineBootstrap
open NotionCoreMachine
open NotionCoreMachinePartition (Partitioned)
open NotionCorePayload (Transaction bootstrap)
open NotionCoreParentMap (Table)

private def rows (atoms : List Nat) : Table :=
  NotionCoreParentMap.runRows .start (NotionCorePayload.textItems ⟨1,[65]⟩ atoms (fun _ => false))

def seeded (atoms : List Nat) : State :=
  ⟨[(0,⟨rows atoms,[]⟩)], [⟨0,NotionCoreSliceForest.freshTitle 0⟩], [0]⟩

private theorem decoded (atoms : List Nat) :
    NotionCoreMachinePrefix.transactionRows (bootstrap atoms) .initial (fun _ _ => false) = rows atoms := by
  simp [NotionCoreMachinePrefix.transactionRows,bootstrap,NotionCorePayload.births,
    NotionCorePayload.operations,NotionCorePayload.Operation.births,rows,List.filterMap_map,Function.comp_def]

private theorem integrates (atoms : List Nat) : integrateRows [] (rows atoms) = some (rows atoms) := by
  apply NotionCoreMachineRows.integrateRows_increasing
  · rw [← decoded]
    exact NotionCoreMachinePrefix.transaction_rows_unique _ _ _
  · simp
  · rw [← decoded]
    exact NotionCoreMachinePrefix.transaction_rows_increasing
      (entry := ⟨bootstrap atoms,[]⟩) (NotionCorePayloadNetwork.Reach.bootstrap atoms)
      (by simp [NotionCorePayloadNetwork.seeded]) .initial _

/-- Exact result is derived from actual atomic create/insert dispatch. -/
theorem bootstrap_executes (atoms : List Nat) :
    applyTransaction {} (bootstrap atoms) = some (seeded atoms) := by
  have integrated := integrates atoms
  unfold rows at integrated
  simp [applyTransaction,bootstrap,NotionCorePayload.operations,applyOperations,
    applyOperation,blockName,getInstance,putInstance,NotionCoreDisplayOrder.insert,
    NotionCoreDisplayOrder.insertionIndex,seeded,rows,integrated]

/-- Every stored reference is the sole initial title interval; its physical
cell includes virtual START even when no text was supplied. -/
theorem seeded_partitioned (atoms : List Nat) : Partitioned (seeded atoms) := by
  constructor
  · intro owned member
    have same : owned = (0,NotionCoreSliceForest.titleRef 0) := by
      simpa [seeded,NotionCoreForestRefs.ownedRefs,NotionCoreSliceForest.freshTitle,
        NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren] using member
    subst owned
    exact ⟨(0,⟨rows atoms,[]⟩),by simp [seeded],rfl⟩
  · intro inst present
    have same : 0 = inst := by simpa [seeded] using present
    subst inst
    let cell : NotionCorePartition.Cell :=
      ⟨0,⟨(0,.start),(traversal (rows atoms).length (rows atoms) .start).map
        (NotionCorePhysicalReplay.atom 0),none⟩⟩
    refine ⟨[cell],?_,?_⟩
    · simp [cell,physical,seeded,getInstance,NotionCorePhysicalReplay.physical,
        NotionCorePhysicalReplay.start,NotionCorePartition.flatten,
        NotionCorePartition.Cell.physical,NotionCorePartition.boundary]
    · simp [seeded,NotionCoreForestRefs.ownedRefs,NotionCoreSliceForest.freshTitle,
        NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
        NotionCoreMachinePartition.cellRefs,cell,NotionCoreSliceForest.titleRef]

/-- Initial joint partition progress covers empty and nonempty bootstrap. -/
theorem bootstrap_partitioned (atoms : List Nat) :
    ∃ state, applyTransaction {} (bootstrap atoms) = some state ∧ Partitioned state :=
  ⟨seeded atoms,bootstrap_executes atoms,seeded_partitioned atoms⟩

/-- Bootstrap may follow independent creations from peers that have not yet
received it. Freshness of the initial name, rather than an empty whole state,
is sufficient for actual execution and partition preservation. -/
theorem fresh_bootstrap_preserves (state : State) (atoms : List Nat)
    (prior : Partitioned state)
    (freshInstance : ∀ entry ∈ state.instances, entry.1 ≠ 0)
    (freshBlock : FreshBlock state 0) :
    ∃ result, applyTransaction state (bootstrap atoms) = some result ∧ Partitioned result ∧
      result.forest = state.forest ++ [⟨0,NotionCoreSliceForest.freshTitle 0⟩] ∧
      ∀ other, other ≠ 0 → physical result other = physical state other := by
  obtain ⟨created,createStep,createdPart⟩ := NotionCoreMachinePartitionCreate.create_partitioned
    state .initial none prior freshInstance freshBlock.1
  have shape := NotionCoreMachineCanonicalCreate.fresh_create_shape state created .initial none
    freshInstance freshBlock createStep
  have storage := NotionCoreMachineCanonicalCreate.fresh_create_storage state created .initial none
    freshInstance freshBlock createStep
  have physicalCreated := NotionCoreMachineCanonicalCreate.fresh_create_physical state created .initial none
    freshInstance freshBlock createStep
  have emptyPhysical : physical created 0 = NotionCoreSliceForest.emptyPhysical 0 := physicalCreated.1
  have empty : getInstance created 0 = {} := by simpa [blockName] using storage 0
  let result := putInstance created 0 ⟨rows atoms,[]⟩
  have insertStep : applyOperation created (.insert .initial .initial ⟨1,[65]⟩ .start atoms) = some result := by
    have integrated := integrates atoms
    unfold rows at integrated
    simp [applyOperation,blockName,empty,integrated,result,rows]
  have resultForest : result.forest = created.forest := by unfold result putInstance; split <;> rfl
  have oldExists : ∃ entry ∈ created.instances, entry.1 = 0 := by rw [shape.1]; simp [blockName]
  let fresh := (traversal (rows atoms).length (rows atoms) .start).map (NotionCorePhysicalReplay.atom 0)
  have splice : physical result 0 = NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
      (0,NotionCoreSpec.LocalId.start) fresh (physical created 0) := by
    rw [emptyPhysical]
    simp [result,physical,NotionCoreMachineTables.getInstance_put,fresh,
      NotionCoreSliceForest.emptyPhysical,NotionCorePhysicalReplay.physical,
      NotionCorePhysicalReplay.start,NotionCorePartition.boundary,NotionCorePartition.spliceAfterBy]
  have otherFrame : ∀ other, other ≠ 0 → physical result other = physical created other := by
    intro other different
    simp [result,physical,NotionCoreMachineTables.getInstance_put,different]
  have resultPart : Partitioned result := NotionCoreMachinePartitionUpdates.splice_partitioned
    created result 0 (0,.start) fresh createdPart resultForest
    (fun key => NotionCoreMachinePartitionUpdates.putInstance_exists_iff created 0 key _ oldExists)
    oldExists (by rw [emptyPhysical]; simp [NotionCoreSliceForest.emptyPhysical])
    (by rw [emptyPhysical]; simp [NotionCoreSliceForest.emptyPhysical,NotionCorePartition.boundary])
    splice otherFrame
  refine ⟨result,?_,resultPart,resultForest.trans shape.2.1,?_⟩
  · simp [applyTransaction,bootstrap,NotionCorePayload.operations,applyOperations,createStep,insertStep]
  · intro other different
    exact (otherFrame other different).trans (physicalCreated.2 other different)

#print axioms fresh_bootstrap_preserves

/-- PASS+FAIL: empty bootstrap still creates a displayed title and physical
START, rather than failing or omitting its instance. -/
theorem empty_seed_control :
    (applyTransaction {} (bootstrap []) >>= render) = some [(0,[])] ∧
    (applyTransaction {} (bootstrap [])).map (fun state => physical state 0) =
      some [NotionCorePhysicalReplay.start 0] ∧
    (applyTransaction {} (bootstrap [])).map (fun state => physical state 0) ≠ some [] := by decide +kernel

#print axioms bootstrap_executes
#print axioms bootstrap_partitioned
#print axioms empty_seed_control
end Sal.MRDTs.Instances.NotionCoreMachineBootstrap
