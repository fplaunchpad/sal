import Sal.MRDTs.Instances.NotionCoreMachineTables
import Sal.MRDTs.Instances.NotionCorePhysicalReplay

/-! Actual combined-machine erase commutes with finite traversal. No graph
closure or desired traversal equation is needed: tombstones retain all parent
links and identities. Pending lists represent the source set by membership. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineErase
open NotionRunAllocation (Id)
open NotionCoreParentMap (Table Row)
open NotionCoreParentErase (erase eraseRow eraseItem)
open NotionCoreMachine
open NotionCorePayload (BlockKey)

@[simp] theorem eraseRow_id (targets : List Id) (row : Row) :
    (eraseRow targets row).item.id = row.item.id := by
  cases row.item.kind <;> rfl
@[simp] theorem eraseRow_origin (targets : List Id) (row : Row) :
    (eraseRow targets row).origin = row.origin := rfl

theorem lookup_erase (targets : List Id) (rows : Table) (id : Id) :
    NotionCoreParentMap.lookup (erase targets rows) id =
      (NotionCoreParentMap.lookup rows id).map (eraseRow targets) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases selected : row.item.id = id
    · simp [NotionCoreParentMap.lookup,erase,List.find?,selected]
    · simp [NotionCoreParentMap.lookup,erase,List.find?,selected] at ih ⊢
      exact ih

theorem childIds_erase (targets : List Id) (rows : Table) (origin : NotionCoreOriginTree.Origin) :
    NotionCoreParentMap.childIds (erase targets rows) origin =
      NotionCoreParentMap.childIds rows origin := by
  simp [NotionCoreParentMap.childIds,erase,List.filterMap_map,Function.comp_def]

theorem traverse_erase (targets : List Id) (fuel : Nat) (rows : Table)
    (origin : NotionCoreOriginTree.Origin) :
    NotionCoreParentMap.traverse fuel (erase targets rows) origin =
      (NotionCoreParentMap.traverse fuel rows origin).map (eraseItem targets) := by
  induction fuel generalizing origin with
  | zero => rfl
  | succ fuel ih =>
    simp only [NotionCoreParentMap.traverse,NotionCoreParentMap.sortedChildren,
      childIds_erase,List.map_flatMap]
    congr 1
    funext id
    rw [lookup_erase]
    cases found : NotionCoreParentMap.lookup rows id with
    | none => simp
    | some row =>
      simp only [Option.map_some,List.map_cons]
      rw [ih]
      rfl

theorem atom_erase (inst : Nat) (targets : List Id) (item : NotionCoreOriginTree.Item) :
    NotionCorePhysicalReplay.atom inst (eraseItem targets item) =
      NotionCoreSource.eraseAtom (targets.map (NotionCorePhysicalReplay.address inst))
        (NotionCorePhysicalReplay.atom inst item) := by
  have member : (targets.map (NotionCorePhysicalReplay.address inst)).contains
      (NotionCorePhysicalReplay.address inst item.id) = decide (item.id ∈ targets) := by
    simp only [List.contains_eq_mem,decide_eq_decide]
    constructor
    · intro selected
      obtain ⟨id,present,same⟩ := List.mem_map.mp selected
      have equal := NotionCorePhysicalReplay.address_injective inst same
      exact equal ▸ present
    · intro present
      exact List.mem_map.mpr ⟨item.id,present,rfl⟩
  cases item with
  | mk id kind =>
    cases kind <;>
      simp only [NotionCorePhysicalReplay.atom,eraseItem,NotionCoreSource.eraseAtom]
    · exact congrArg (fun flag => (⟨NotionCorePhysicalReplay.address inst id,
        NotionCoreSource.Kind.text _ flag⟩ : NotionCoreSource.Atom))
        (congrArg (fun flag => _ || flag) member.symm)

theorem start_erase (inst : Nat) (targets : List Id) :
    NotionCoreSource.eraseAtom (targets.map (NotionCorePhysicalReplay.address inst))
      (NotionCorePhysicalReplay.start inst) = NotionCorePhysicalReplay.start inst := rfl

theorem physical_erased (inst : Nat) (targets : List Id) (rows : Table) :
    NotionCorePhysicalReplay.physical inst
      (traversal (erase targets rows).length (erase targets rows) .start) =
    (NotionCorePhysicalReplay.physical inst (traversal rows.length rows .start)).map
      (NotionCoreSource.eraseAtom (targets.map (NotionCorePhysicalReplay.address inst))) := by
  simp only [traversal_correct,erase,List.length_map]
  change NotionCorePhysicalReplay.physical inst
    (NotionCoreParentMap.traverse rows.length (erase targets rows) .start) = _
  rw [traverse_erase]
  simp only [NotionCorePhysicalReplay.physical,List.map_cons,List.map_map,
    start_erase]
  congr 1
  apply List.map_congr_left
  intro item _
  exact atom_erase inst targets item

/-- Actual accepted erase keeps forest/display and maps the selected physical
instance, while every other instance is unchanged. -/
theorem erase_physical (state result : State) (block inst : BlockKey) (targets : List Id)
    (accepted : applyOperation state (.erase block inst targets) = some result) :
    result.forest = state.forest ∧ result.display = state.display ∧
    ∀ key, physical result key = if key = blockName inst then
      (physical state key).map (NotionCoreSource.eraseAtom
        (targets.map (NotionCorePhysicalReplay.address key))) else physical state key := by
  simp only [applyOperation,Option.some.injEq] at accepted
  subst result
  refine ⟨by unfold putInstance; split <;> rfl,by unfold putInstance; split <;> rfl,?_⟩
  intro key
  by_cases selected : key = blockName inst
  · subst key
    simp only [physical,NotionCoreMachineTables.getInstance_put]
    exact physical_erased _ targets _
  · simp [physical,NotionCoreMachineTables.getInstance_put,selected]

theorem erase_addresses (state result : State) (block inst : BlockKey) (targets : List Id)
    (accepted : applyOperation state (.erase block inst targets) = some result) (key : Nat) :
    (physical result key).map NotionCoreSource.Atom.address =
      (physical state key).map NotionCoreSource.Atom.address := by
  rw [(erase_physical state result block inst targets accepted).2.2 key]
  split
  · simp [List.map_map,Function.comp_def,NotionCoreSource.eraseAtom]
  · rfl

private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[65]⟩
private def marker : Id := ⟨3,[65]⟩
private def fixture : State :=
  {instances := [(0,⟨[⟨⟨a,.text 97 false⟩,.start⟩,
    ⟨⟨b,.text 98 false⟩,.item a⟩,⟨⟨marker,.split⟩,.item b⟩],[]⟩)], forest := [⟨0,NotionCoreSliceForest.freshTitle 0⟩], display := [0]}

/-- Raw primitive control: hidden parents and targeted markers remain physical.
This is an erase-semantic fixture, not an honest client selecting a marker. -/
theorem hidden_marker_control :
    (applyOperation fixture (.erase .initial .initial [a,marker])).map
      (fun state => physical state 0) = some
        [NotionCorePhysicalReplay.start 0,
         NotionCorePhysicalReplay.atom 0 ⟨a,.text 97 true⟩,
         NotionCorePhysicalReplay.atom 0 ⟨b,.text 98 false⟩,
         NotionCorePhysicalReplay.atom 0 ⟨marker,.split⟩] ∧
    (applyOperation fixture (.erase .initial .initial [a,marker])).map
      (fun state => physical state 0) ≠ some
        [NotionCorePhysicalReplay.start 0,NotionCorePhysicalReplay.atom 0 ⟨b,.text 98 false⟩] := by decide +kernel

#print axioms erase_addresses
#print axioms hidden_marker_control
#print axioms traverse_erase
#print axioms erase_physical
end Sal.MRDTs.Instances.NotionCoreMachineErase
