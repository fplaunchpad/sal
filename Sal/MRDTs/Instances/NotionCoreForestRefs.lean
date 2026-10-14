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
def leftRef (ref : Ref) (marker : Address) : Ref := {ref with stop := some marker}
def rightRef (ref : Ref) (marker : Address) : Ref := ⟨marker,ref.stop⟩

mutual
theorem splitTree_refs (physical : Nat → List Atom) (marker : Address)
    (tree next : Tree) (accepted : splitTree physical marker tree = some next) :
    ∃ before ref after, preorderTree tree = before ++ ref :: after ∧
      contains physical ref marker = true ∧
      preorderTree next = before ++ leftRef ref marker :: rightRef ref marker :: after := by
  cases tree with
  | node ref children =>
    by_cases selected : contains physical ref marker = true
    · simp only [splitTree, selected, if_true, Option.some.injEq] at accepted
      subst next
      exact ⟨[],ref,preorderChildren children,rfl,selected,by
        simp [splitNode,preorderTree,preorderChildren,leftRef,rightRef]⟩
    · have rejected : contains physical ref marker = false := Bool.eq_false_iff.mpr selected
      simp only [splitTree, rejected, Bool.false_eq_true, if_false] at accepted
      obtain ⟨changed, step, same⟩ := Option.map_eq_some_iff.mp accepted
      subst next
      obtain ⟨before,chosen,after,old,found,new⟩ := splitChildren_refs physical marker children changed step
      exact ⟨ref::before,chosen,after,by simp [preorderTree,old],found,by simp [preorderTree,new]⟩
theorem splitChildren_refs (physical : Nat → List Atom) (marker : Address)
    (children next : Children) (accepted : splitChildren physical marker children = some next) :
    ∃ before ref after, preorderChildren children = before ++ ref :: after ∧
      contains physical ref marker = true ∧
      preorderChildren next = before ++ leftRef ref marker :: rightRef ref marker :: after := by
  cases children with
  | nil => simp [splitChildren] at accepted
  | cons tree rest =>
    cases selected : splitTree physical marker tree with
    | some changed =>
      simp only [splitChildren,selected,Option.some.injEq] at accepted
      subst next
      obtain ⟨before,ref,after,old,found,new⟩ := splitTree_refs physical marker tree changed selected
      exact ⟨before,ref,after ++ preorderChildren rest,by
        simp [preorderChildren,old,List.append_assoc],found,by
        simp [preorderChildren,new,List.append_assoc]⟩
    | none =>
      simp only [splitChildren,selected] at accepted
      obtain ⟨changed,step,same⟩ := Option.map_eq_some_iff.mp accepted
      subst next
      obtain ⟨before,ref,after,old,found,new⟩ := splitChildren_refs physical marker rest changed step
      exact ⟨preorderTree tree ++ before,ref,after,by
        simp [preorderChildren,old,List.append_assoc],found,by
        simp [preorderChildren,new,List.append_assoc]⟩
end

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

theorem preorderChildren_append (a b : Children) :
    preorderChildren (a.append b) = preorderChildren a ++ preorderChildren b := by
  cases a with
  | nil => rfl
  | cons tree rest =>
    simp [Children.append,preorderChildren,preorderChildren_append rest b,List.append_assoc]

theorem preorder_appendRoot (tree child : Tree) :
    preorderTree (appendRoot tree child) = preorderTree tree ++ preorderTree child := by
  cases tree
  simp [appendRoot,Tree.slice,Tree.children,preorderTree,preorderChildren,
    preorderChildren_append]

theorem ownedRefs_append (a b : Forest) : ownedRefs (a ++ b) = ownedRefs a ++ ownedRefs b := by
  simp [ownedRefs]

theorem ownedRefs_create (forest : Forest) (fresh : Nat) :
    ownedRefs (forest ++ [⟨fresh,freshTitle fresh⟩]) = ownedRefs forest ++ [(fresh,titleRef fresh)] := by
  simp [ownedRefs,freshTitle,preorderTree,preorderChildren]

mutual
theorem detachTree_refs (marker : Address) (tree next child : Tree)
    (accepted : detachTree marker tree = some (next,child)) :
    ∃ before after, preorderTree tree = before ++ preorderTree child ++ after ∧
      preorderTree next = before ++ after ∧ child.slice.start = marker := by
  cases tree with
  | node ref children =>
    simp only [detachTree] at accepted
    obtain ⟨result,step,same⟩ := Option.map_eq_some_iff.mp accepted
    have pair := Prod.mk.inj same
    obtain ⟨before,after,old,new,start⟩ := detachChildren_refs marker children result.1 result.2
      (by exact step)
    have nextEq := pair.1
    have childEq := pair.2
    subst next; subst child
    exact ⟨ref::before,after,by simp [preorderTree,old,List.append_assoc],
      by simp [preorderTree,new],start⟩
theorem detachChildren_refs (marker : Address) (children next : Children) (child : Tree)
    (accepted : detachChildren marker children = some (next,child)) :
    ∃ before after, preorderChildren children = before ++ preorderTree child ++ after ∧
      preorderChildren next = before ++ after ∧ child.slice.start = marker := by
  cases children with
  | nil => simp [detachChildren] at accepted
  | cons tree rest =>
    by_cases selected : tree.slice.start = marker
    · simp only [detachChildren,selected,if_true,Option.some.injEq] at accepted
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj accepted
      exact ⟨[],preorderChildren rest,by simp [preorderChildren],rfl,selected⟩
    · simp only [detachChildren,selected,if_false] at accepted
      cases found : detachTree marker tree with
      | some result =>
        simp only [found,Option.some.injEq] at accepted
        obtain ⟨nextEq,childEq⟩ := Prod.mk.inj accepted
        subst next; subst child
        obtain ⟨before,after,old,new,start⟩ := detachTree_refs marker tree result.1 result.2
          (by exact found)
        exact ⟨before,after ++ preorderChildren rest,by
          simp [preorderChildren,old,List.append_assoc],by
          simp [preorderChildren,new,List.append_assoc],start⟩
      | none =>
        simp only [found] at accepted
        obtain ⟨result,step,same⟩ := Option.map_eq_some_iff.mp accepted
        obtain ⟨nextEq,childEq⟩ := Prod.mk.inj same
        subst next; subst child
        obtain ⟨before,after,old,new,start⟩ := detachChildren_refs marker rest result.1 result.2
          (by exact step)
        exact ⟨preorderTree tree ++ before,after,by
          simp [preorderChildren,old,List.append_assoc],by
          simp [preorderChildren,new,List.append_assoc],start⟩
end

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
