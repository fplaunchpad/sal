import Sal.MRDTs.Instances.NotionCoreFormattingBridge
import Sal.MRDTs.Instances.NotionCoreParentErase

/-!
Formatting under deletion, fresh annotation batches, and insertion gaps.

The deletion results apply to the actual retained-origin forest erasure.
The insertion result states the independent positional boundary rule: inserting
at the left endpoint is excluded; inserting at the right endpoint is included.
Its connection to a concrete insertion requires the source anchors to move by
the stated gap embedding. This is not a full rich-text protocol certificate.
-/
namespace Sal.MRDTs.Instances.NotionCoreFormattingEvolution
open NotionCoreFormattingSource
open NotionCoreOriginTree (Tree Forest preorder preorderTree)
open NotionCoreParentErase (eraseItem eraseTree eraseForest)
open NotionRunAllocation (Id)

def erasePosition (targets : List Id) (position : Positioned) : Positioned :=
  {position with item := eraseItem targets position.item}

mutual
theorem walkTree_erase (targets : List Id) (offset : Nat) (tree : Tree) :
    walkTree offset (eraseTree targets tree) =
      (walkTree offset tree).map (erasePosition targets) := by
  cases tree with
  | node item children =>
    simp [eraseTree, walkTree, NotionCoreParentErase.eraseForest_preorder,
      walk_erase, erasePosition]
theorem walk_erase (targets : List Id) (offset : Nat) (forest : Forest) :
    walk offset (eraseForest targets forest) =
      (walk offset forest).map (erasePosition targets) := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
    simp [eraseForest, walk, NotionCoreParentErase.eraseTree_preorder,
      walkTree_erase, walk_erase]
end

/-- Tombstoning changes visibility, but neither endpoint identity nor its
physical entry/subtree-exit coordinate. Even a deleted endpoint survives. -/
theorem anchorPosition_erase (targets : List Id) (forest : Forest) (anchor : Anchor) :
    anchorPosition (eraseForest targets forest) anchor = anchorPosition forest anchor := by
  cases anchor with
  | mk endpoint side =>
    cases endpoint with
    | start => rfl
    | finish => simp [anchorPosition, NotionCoreParentErase.eraseForest_preorder]
    | item id =>
      simp only [anchorPosition, walk_erase, List.find?_map, Function.comp_def,
        erasePosition, NotionCoreParentErase.eraseItem_id, Option.map_map]

theorem covers_erase (targets : List Id) (forest : Forest) (operation : MarkOp) (index : Nat) :
    covers (eraseForest targets forest) operation index = covers forest operation index := by
  simp only [covers, anchorPosition_erase]

/-- Retained annotations keep the same per-position meaning after erasure.
The renderer separately filters the newly deleted text. -/
theorem resolveAt_erase (targets : List Id) (forest : Forest)
    (operations : List MarkOp) (index : Nat) :
    resolveAt (eraseForest targets forest) operations index = resolveAt forest operations index := by
  unfold resolveAt applyOrdered
  congr 1
  funext bold operation
  rw [covers_erase]

/-- Existing coordinates move right exactly when insertion precedes them.
The same rule applies to a before-item boundary or to END. -/
def gapShift (gap width position : Nat) : Nat :=
  if gap ≤ position then position + width else position

theorem gapShift_strictMono (gap width : Nat) : StrictMono (gapShift gap width) := by
  intro left right before
  unfold gapShift
  split <;> split <;> omega

/-- Existing characters retain interval membership under an order-preserving
gap insertion. This says nothing about the visibility of those characters. -/
theorem old_membership (gap width lower upper index : Nat) :
    (gapShift gap width lower ≤ gapShift gap width index ∧
      gapShift gap width index < gapShift gap width upper) ↔
    (lower ≤ index ∧ index < upper) := by
  have strict := gapShift_strictMono gap width
  exact and_congr strict.le_iff_le strict.lt_iff_lt

/-- For a nonempty old interval, every new character at the insertion gap
inherits exactly when the gap lies strictly after the left boundary and at
or before the right boundary. The empty interval remains empty. -/
theorem new_membership (gap width lower upper offset : Nat) (inside : offset < width) :
    (gapShift gap width lower ≤ gap + offset ∧ gap + offset < gapShift gap width upper) ↔
      (lower < gap ∧ gap ≤ upper) := by
  unfold gapShift
  split <;> split <;> omega

/-- Source sorting leaves an already ascending annotation sequence intact. -/
theorem resolveAt_ordered (forest : Forest) (operations : List MarkOp) (index : Nat)
    (ordered : operations.Pairwise Ascending) :
    resolveAt forest operations index = applyOrdered forest operations index false := by
  unfold resolveAt sortOperations
  rw [ordered.insertionSort_eq]

/-- A fresh ordered batch is interpreted after all existing annotations.
Freshness is about annotation IDs, not the external framework timestamp. -/
theorem resolve_fresh_batch (forest : Forest) (old fresh : List MarkOp) (index : Nat)
    (oldOrdered : old.Pairwise Ascending) (freshOrdered : fresh.Pairwise Ascending)
    (later : ∀ previous ∈ old, ∀ next ∈ fresh,
      NotionRunAllocation.Before previous.id next.id) :
    resolveAt forest (old ++ fresh) index =
      applyOrdered forest fresh index (resolveAt forest old index) := by
  have ordered : (old ++ fresh).Pairwise Ascending :=
    List.pairwise_append.mpr ⟨oldOrdered, freshOrdered,
      fun a ha b hb => Or.inl (later a ha b hb)⟩
  rw [resolveAt_ordered _ _ _ ordered, applyOrdered_append,
    resolveAt_ordered _ _ _ oldOrdered]

theorem applyOrdered_uniform (forest : Forest) (operations : List MarkOp)
    (index : Nat) (value initial : Bool)
    (uniform : ∀ operation ∈ operations, operation.value = value) :
    applyOrdered forest operations index initial =
      if operations.any (fun operation => covers forest operation index) then value else initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
    have first := uniform operation (by simp)
    have tail : ∀ next ∈ rest, next.value = value :=
      fun next member => uniform next (by simp [member])
    simp only [applyOrdered, List.foldl_cons]
    change applyOrdered forest rest index
      (if covers forest operation index then operation.value else initial) = _
    rw [ih _ tail]
    cases h : covers forest operation index <;>
      cases k : rest.any (fun next => covers forest next index) <;> simp [h, k, first]

/-- Immediate selection correctness must account for old annotations as well
as the newly prepared intervals. Under fresh IDs the batch overwrites exactly
its covered positions, using the issuer's one shared add/remove value. -/
theorem resolve_fresh_uniform (forest : Forest) (old fresh : List MarkOp) (index : Nat)
    (value : Bool) (oldOrdered : old.Pairwise Ascending)
    (freshOrdered : fresh.Pairwise Ascending)
    (later : ∀ previous ∈ old, ∀ next ∈ fresh,
      NotionRunAllocation.Before previous.id next.id)
    (uniform : ∀ next ∈ fresh, next.value = value) :
    resolveAt forest (old ++ fresh) index =
      if fresh.any (fun next => covers forest next index) then value
      else resolveAt forest old index := by
  rw [resolve_fresh_batch forest old fresh index oldOrdered freshOrdered later]
  exact applyOrdered_uniform forest fresh index value _ uniform

/-- An operation ID denotes one payload. This is the source archive's integrity
condition; it allows repeated copies of an identical annotation. -/
def ConsistentIds (operations : List MarkOp) : Prop :=
  ∀ a ∈ operations, ∀ b ∈ operations, a.id = b.id → a = b

theorem sort_fresh_append (old fresh : List MarkOp)
    (consistent : ConsistentIds (old ++ fresh))
    (later : ∀ previous ∈ old, ∀ next ∈ fresh,
      NotionRunAllocation.Before previous.id next.id) :
    sortOperations (old ++ fresh) = sortOperations old ++ sortOperations fresh := by
  have concatPerm := (sorted_perm old).append (sorted_perm fresh)
  have concatSorted : (sortOperations old ++ sortOperations fresh).Pairwise Ascending := by
    apply List.pairwise_append.mpr
    refine ⟨sorted_pairwise old, sorted_pairwise fresh, ?_⟩
    intro a ha b hb
    exact Or.inl (later a ((sorted_perm old).mem_iff.mp ha)
      b ((sorted_perm fresh).mem_iff.mp hb))
  apply List.Perm.eq_of_pairwise _ (sorted_pairwise _) concatSorted
    ((sorted_perm (old ++ fresh)).trans concatPerm.symm)
  intro a b ha hb ab ba
  have aMember := (sorted_perm (old ++ fresh)).mem_iff.mp ha
  have bMember := concatPerm.mem_iff.mp hb
  apply consistent a aMember b bMember
  rcases ab with ab | ab
  · rcases ba with ba | ba
    · exact False.elim (NotionCoreSourceInvariant.before_asymm ab ba)
    · exact ba.symm
  · exact ab

/-- The actual source evaluator sorts arbitrary stored lists. Freshness and
ID integrity suffice; callers do not need an already-sorted annotation store. -/
theorem resolve_fresh_unsorted (forest : Forest) (old fresh : List MarkOp)
    (index : Nat) (value : Bool) (consistent : ConsistentIds (old ++ fresh))
    (later : ∀ previous ∈ old, ∀ next ∈ fresh,
      NotionRunAllocation.Before previous.id next.id)
    (uniform : ∀ next ∈ fresh, next.value = value) :
    resolveAt forest (old ++ fresh) index =
      if fresh.any (fun next => covers forest next index) then value
      else resolveAt forest old index := by
  unfold resolveAt
  rw [sort_fresh_append old fresh consistent later, applyOrdered_append]
  rw [applyOrdered_uniform forest (sortOperations fresh) index value _
    (fun next member => uniform next ((sorted_perm fresh).mem_iff.mp member))]
  rw [(sorted_perm fresh).any_eq]

namespace SPOT
/-- PASS+FAIL: gap 1 is the left boundary of [1,3), gap 3 its right boundary.
The rules deliberately exclude symmetric growth and identity-only marks. -/
theorem boundary_control :
    ¬ (gapShift 1 1 1 ≤ 1 ∧ 1 < gapShift 1 1 3) ∧
    (gapShift 3 1 1 ≤ 3 ∧ 3 < gapShift 3 1 3) ∧
    (gapShift 2 1 1 ≤ 2 ∧ 2 < gapShift 2 1 3) ∧
    ¬ (gapShift 4 1 1 ≤ 4 ∧ 4 < gapShift 4 1 3) := by decide
end SPOT

#print axioms anchorPosition_erase
#print axioms resolveAt_erase
#print axioms old_membership
#print axioms new_membership
#print axioms resolve_fresh_batch
#print axioms resolve_fresh_uniform
#print axioms resolve_fresh_unsorted
end Sal.MRDTs.Instances.NotionCoreFormattingEvolution
