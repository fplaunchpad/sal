import Mathlib.Data.List.Flatten
import Sal.MRDTs.Instances.NotionCoreSliceForest

/-! Derive owned interval-reference rewrites from actual recursive source-tree
search and update. All nodes, including empty title roots, participate. The
context lists in the conclusions are derived, not supplied projection guards.
These generic lemmas describe the typed tree algorithms. For source detach
correspondence, core fresh markers cannot match a title root: the demo throws
on a first matching root, whereas the typed detach searches children. Duplicate
block IDs are likewise outside the source Map representation. -/
namespace Sal.MRDTs.Instances.NotionCoreForestRefs
open NotionCoreSliceForest
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)

def ownedRefs (forest : Forest) : List (Nat × Ref) :=
  forest.flatMap fun block => (preorderTree block.title).map (block.id, ·)
export NotionCoreSliceForest (leftRef rightRef splitTree_refs splitChildren_refs
  preorderChildren_append preorder_appendRoot detachTree_refs detachChildren_refs)

theorem ownedRefs_refs (forest : Forest) : (ownedRefs forest).map Prod.snd = forestRefs forest := by
  simp [ownedRefs, forestRefs, List.map_flatMap, List.map_map, Function.comp_def]

theorem splitForest_refs (physical : Nat → List Atom) (marker : Address)
    (forest next : Forest) (accepted : splitForest physical marker forest = some next) :
    ∃ before owner ref after, ownedRefs forest = before ++ (owner,ref) :: after ∧
      contains physical ref marker = true ∧
      ownedRefs next = before ++ (owner,leftRef ref marker) :: (owner,rightRef ref marker) :: after := by
  induction forest generalizing next with
  | nil => simp [splitForest] at accepted
  | cons block rest ih =>
    cases selected : splitTree physical marker block.title with
    | some changed =>
      simp only [splitForest,selected,Option.some.injEq] at accepted
      subst next
      obtain ⟨before,ref,after,old,found,new⟩ := splitTree_refs physical marker block.title changed selected
      exact ⟨before.map (block.id,·),block.id,ref,
        after.map (block.id,·) ++ ownedRefs rest,by
          simp [ownedRefs,old,List.map_append,List.append_assoc],found,by
          simp [ownedRefs,new,List.map_append,List.append_assoc]⟩
    | none =>
      simp only [splitForest,selected] at accepted
      obtain ⟨changed,step,same⟩ := Option.map_eq_some_iff.mp accepted
      subst next
      obtain ⟨before,owner,ref,after,old,found,new⟩ := ih changed step
      exact ⟨(preorderTree block.title).map (block.id,·) ++ before,owner,ref,after,by
        change _ ++ ownedRefs rest = _
        rw [old]
        simp [List.append_assoc],found,by
        change _ ++ ownedRefs changed = _
        rw [new]
        simp [List.append_assoc]⟩

theorem ownedRefs_append (a b : Forest) : ownedRefs (a ++ b) = ownedRefs a ++ ownedRefs b := by
  simp [ownedRefs]

theorem ownedRefs_create (forest : Forest) (fresh : Nat) :
    ownedRefs (forest ++ [⟨fresh,freshTitle fresh⟩]) = ownedRefs forest ++ [(fresh,titleRef fresh)] := by
  simp [ownedRefs,freshTitle,preorderTree,preorderChildren]

theorem detachForest_refs (marker : Address) (forest next : Forest) (child : Tree)
    (accepted : detachForest marker forest = some (next,child)) :
    ∃ before owner after,
      ownedRefs forest = before ++ (preorderTree child).map (owner,·) ++ after ∧
      ownedRefs next = before ++ after ∧ child.slice.start = marker := by
  induction forest generalizing next with
  | nil => simp [detachForest] at accepted
  | cons block rest ih =>
    cases found : detachTree marker block.title with
    | some result =>
      simp only [detachForest,found,Option.some.injEq] at accepted
      obtain ⟨nextEq,childEq⟩ := Prod.mk.inj accepted
      subst next; subst child
      obtain ⟨before,after,old,new,start⟩ := detachTree_refs marker block.title result.1 result.2
        (by exact found)
      exact ⟨before.map (block.id,·),block.id,after.map (block.id,·) ++ ownedRefs rest,by
        simp [ownedRefs,old,List.map_append,List.append_assoc],by
        simp [ownedRefs,new,List.map_append,List.append_assoc],start⟩
    | none =>
      simp only [detachForest,found] at accepted
      obtain ⟨result,step,same⟩ := Option.map_eq_some_iff.mp accepted
      obtain ⟨nextEq,childEq⟩ := Prod.mk.inj same
      subst next; subst child
      obtain ⟨before,owner,after,old,new,start⟩ := ih result.1
        (by exact step)
      exact ⟨(preorderTree block.title).map (block.id,·) ++ before,owner,after,by
        change _ ++ ownedRefs rest = _
        rw [old]; simp [List.append_assoc],by
        change _ ++ ownedRefs result.1 = _
        rw [new]; simp [List.append_assoc],start⟩

/-- With malformed duplicate block names appendToBlock updates every matching
block; this literal formula does not hide a uniqueness premise. -/
theorem appendToBlock_refs (bid : Nat) (child : Tree) (forest : Forest) :
    ownedRefs (appendToBlock bid child forest) = forest.flatMap (fun block =>
      (preorderTree block.title).map (block.id,·) ++
        if block.id = bid then (preorderTree child).map (bid,·) else []) := by
  simp only [ownedRefs,appendToBlock,List.flatMap_map]
  congr 1
  funext block
  by_cases selected : block.id = bid
  · simp [selected,preorder_appendRoot,List.map_append]
  · simp [selected]

private def marker : Address := (0,.event (0,1))
private def fixture : Forest := [⟨1,freshTitle 1⟩,⟨0,freshTitle 0⟩]
private def raw (inst : Nat) : List Atom :=
  if inst = 0 then [NotionCorePartition.boundary (0,.start),
    NotionCorePartition.boundary marker] else emptyPhysical inst

/-- The search preserves the preceding empty title and inserts the right
reference immediately after the selected reference. -/
theorem split_context_control :
    ((splitForest raw marker fixture).map ownedRefs) = some
      [(1,titleRef 1),(0,⟨(0,.start),some marker⟩),(0,⟨marker,none⟩)] ∧
    ((splitForest raw marker fixture).map ownedRefs) ≠ some
      [(0,⟨(0,.start),some marker⟩),(0,⟨marker,none⟩)] := by decide +kernel

#print axioms detachForest_refs
#print axioms splitForest_refs
#print axioms preorder_appendRoot
end Sal.MRDTs.Instances.NotionCoreForestRefs
