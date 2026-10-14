import Sal.MRDTs.Instances.NotionCoreParentMap
import Sal.MRDTs.Instances.NotionCoreParentErase

/-! Executable origin-index traversal and its exact structural invariant.
This is a component of executable refinement, not a theorem about the existing
JavaScript Map implementation or an extraction claim. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeIndex
open NotionRunAllocation (Id)
open NotionCoreOriginTree (Origin Item)
open NotionCoreParentMap (Table lookup sortedChildren)

abbrev Children := List (Origin × List Id)

def childrenAt (index : Children) (origin : Origin) : List Id :=
  ((index.find? (fun entry => entry.1 == origin)).map Prod.snd).getD []

/-- Every bucket is the exact sorted enumeration of retained row identities.
The invariant constrains structure, not final document observations. -/
def Represents (index : Children) (rows : Table) : Prop :=
  ∀ origin, childrenAt index origin = sortedChildren rows origin

def traverse : Nat → Table → Children → Origin → List Item
  | 0, _, _, _ => []
  | fuel + 1, rows, index, origin =>
    (childrenAt index origin).flatMap fun id =>
      match lookup rows id with
      | none => []
      | some row => row.item :: traverse fuel rows index (.item id)

/-- Maintained adjacency buckets replace sorting/filtering at each recursion
without changing traversal, including retained tombstones and split markers. -/
theorem traverse_correct (rows : Table) (index : Children)
    (represented : Represents index rows) (fuel : Nat) (origin : Origin) :
    traverse fuel rows index origin = NotionCoreParentMap.traverse fuel rows origin := by
  induction fuel generalizing origin with
  | zero => rfl
  | succ fuel ih =>
    simp only [traverse,NotionCoreParentMap.traverse,represented origin]
    apply congrArg (fun f => (sortedChildren rows origin).flatMap f)
    funext id
    cases lookup rows id <;> simp [ih]

theorem initial : Represents [] [] := by
  intro origin
  simp [childrenAt, sortedChildren, NotionCoreParentMap.childIds,
    NotionCoreSourceInvariant.sortChildren]

/-- Tombstoning preserves parent identities and therefore needs no index
rebuild. This also prevents an optimization from deleting retained anchors. -/
theorem represents_erase (index : Children) (rows : Table)
    (represented : Represents index rows) (targets : List Id) :
    Represents index (NotionCoreParentErase.erase targets rows) := by
  intro origin
  rw [represented origin]
  unfold sortedChildren NotionCoreParentMap.childIds
  congr 1
  simp [NotionCoreParentErase.erase, List.filterMap_map, Function.comp_def,
    NotionCoreParentErase.eraseRow, NotionCoreParentErase.eraseItem]

namespace SPOT
private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[66]⟩
private def rows : Table :=
  [⟨⟨a,.text 97 true⟩,.start⟩,⟨⟨b,.text 98 false⟩,.item a⟩]
private def index : Children := [(.start,[a]),(.item a,[b])]
/-- A deleted parent remains an anchor. Traversal does not discard its child
or silently return the visible-only list. Expected item identities are literal. -/
theorem retained_anchor :
    (traverse 2 rows index .start).map Item.id = [a,b] ∧
    (traverse 2 rows index .start).map Item.id ≠ [b] ∧
    (traverse 2 rows [] .start).map Item.id ≠ [a,b] := by
  decide +kernel
end SPOT

#print axioms represents_erase
#print axioms traverse_correct
#print axioms SPOT.retained_anchor
end Sal.MRDTs.Instances.NotionCoreRuntimeIndex
