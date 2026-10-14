import Sal.MRDTs.Instances.NotionCoreMachineDocument

/-! The restricted core tree contributes exactly its active interval. Inactive
titles must be present and physically empty; they are not silently dropped. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralActiveText
open NotionCoreMachine
open NotionCoreSliceForest (Normal active attached)

theorem treeAtoms_active (state : State) (block : NotionCoreSliceForest.Block)
    (normal : Normal block.id block.title)
    (empty : attached block.title = true → physical state block.id = NotionCoreSliceForest.emptyPhysical block.id)
    (titleExists : attached block.title = true → state.instances.any (fun entry => entry.1 == block.id) = true) :
    treeAtoms state block.title = sliceAtoms state (active block.title) := by
  cases block with
  | mk bid tree =>
    change Normal bid tree at normal
    cases normal with
    | own stop =>
      cases h : sliceAtoms state ⟨(bid,.start),stop⟩ <;>
        simp [treeAtoms, NotionCoreSliceForest.preorderTree, NotionCoreSliceForest.preorderChildren,
          active, NotionCoreSliceForest.Tree.children, NotionCoreSliceForest.Tree.slice, h]
    | attached ref =>
      have root := NotionCoreMachineSlices.empty_title_atoms state bid (titleExists rfl) (empty rfl)
      cases h : sliceAtoms state ref <;>
        simp [treeAtoms, NotionCoreSliceForest.preorderTree, NotionCoreSliceForest.preorderChildren,
          active, NotionCoreSliceForest.Tree.children, NotionCoreSliceForest.Tree.slice, root, h]

theorem blockText_active (state : State) (block : NotionCoreSliceForest.Block)
    (found : state.forest.find? (fun old => old.id == block.id) = some block)
    (normal : Normal block.id block.title)
    (empty : attached block.title = true → physical state block.id = NotionCoreSliceForest.emptyPhysical block.id)
    (titleExists : attached block.title = true → state.instances.any (fun entry => entry.1 == block.id) = true) :
    blockText state block.id =
      (sliceAtoms state (active block.title)).map (List.flatMap atomText) := by
  unfold blockText
  rw [found]
  dsimp only [Bind.bind, Option.bind]
  rw [treeAtoms_active state block normal empty titleExists]
  cases sliceAtoms state (active block.title) <;> rfl

#print axioms treeAtoms_active
#print axioms blockText_active
end Sal.MRDTs.Instances.NotionCoreStructuralActiveText
