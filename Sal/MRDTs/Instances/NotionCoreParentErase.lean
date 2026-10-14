import Sal.MRDTs.Instances.NotionCoreParentCoupling

/-! Actual existing-item tombstone update. Split markers retain their kind;
parent links and children remain present. Pending deletes for future births
are handled separately by payload birth decoding. -/
namespace Sal.MRDTs.Instances.NotionCoreParentErase
open NotionRunAllocation (Id)
open NotionCoreOriginTree (Item Kind Origin Tree Forest)
open NotionCoreParentMap
open NotionCoreParentCoupling

def eraseItem (targets : List Id) (item : Item) : Item :=
  {item with kind := match item.kind with
    | .text value deleted => .text value (deleted || decide (item.id ∈ targets))
    | .split => .split}
def eraseRow (targets : List Id) (row : Row) : Row :=
  {row with item := eraseItem targets row.item}
def erase (targets : List Id) (rows : Table) : Table := rows.map (eraseRow targets)
mutual
def eraseTree (targets : List Id) : Tree → Tree
  | .node item children => .node (eraseItem targets item) (eraseForest targets children)
def eraseForest (targets : List Id) : Forest → Forest
  | .nil => .nil
  | .cons tree rest => .cons (eraseTree targets tree) (eraseForest targets rest)
end
@[simp] theorem eraseItem_id (targets : List Id) (item : Item) :
    (eraseItem targets item).id = item.id := rfl
mutual
theorem eraseTree_preorder (targets : List Id) (tree : Tree) :
    NotionCoreOriginTree.preorderTree (eraseTree targets tree) =
      (NotionCoreOriginTree.preorderTree tree).map (eraseItem targets) := by
  cases tree with
  | node item children => simp [eraseTree, NotionCoreOriginTree.preorderTree, eraseForest_preorder]
theorem eraseForest_preorder (targets : List Id) (forest : Forest) :
    NotionCoreOriginTree.preorder (eraseForest targets forest) =
      (NotionCoreOriginTree.preorder forest).map (eraseItem targets) := by
  cases forest with
  | nil => rfl
  | cons tree rest => simp [eraseForest, NotionCoreOriginTree.preorder, eraseTree_preorder, eraseForest_preorder]
end
mutual
theorem eraseTree_rows (targets : List Id) (parent : Origin) (tree : Tree) :
    treeRows parent (eraseTree targets tree) = (treeRows parent tree).map (eraseRow targets) := by
  cases tree with
  | node item children => simp [eraseTree, treeRows, eraseForest_rows, eraseRow]
theorem eraseForest_rows (targets : List Id) (parent : Origin) (forest : Forest) :
    forestRows parent (eraseForest targets forest) = (forestRows parent forest).map (eraseRow targets) := by
  cases forest with
  | nil => rfl
  | cons tree rest => simp [eraseForest, forestRows, eraseTree_rows, eraseForest_rows]
end

theorem erase_edges (targets : List Id) (rows : Table) (forest : Forest)
    (coupled : ParentEdges rows forest) : ParentEdges (erase targets rows) (eraseForest targets forest) := by
  unfold ParentEdges erase
  rw [eraseForest_rows]
  exact coupled.map _

theorem erase_unique (targets : List Id) (rows : Table) (unique : Unique rows) :
    Unique (erase targets rows) := by
  simpa [NotionCoreParentMap.Unique, erase, eraseRow, List.map_map, Function.comp_def] using unique

@[simp] theorem erase_roots (targets : List Id) (forest : Forest) :
    (eraseForest targets forest).roots = forest.roots := by
  cases forest with
  | nil => rfl
  | cons tree rest => cases tree; simp [eraseForest, eraseTree, Forest.roots, Tree.item, erase_roots]
mutual
theorem eraseTree_ordered (targets : List Id) (tree : Tree) (ordered : OrderedTree tree) :
    OrderedTree (eraseTree targets tree) := by
  cases tree with
  | node item children => exact eraseForest_ordered targets children ordered
theorem eraseForest_ordered (targets : List Id) (forest : Forest) (ordered : OrderedForest forest) :
    OrderedForest (eraseForest targets forest) := by
  cases forest with
  | nil => trivial
  | cons tree rest =>
      have same : (eraseTree targets tree).item.id = tree.item.id := by cases tree; rfl
      exact ⟨by simpa only [Forest.roots, erase_roots, same] using ordered.1,
        eraseTree_ordered targets tree ordered.2.1, eraseForest_ordered targets rest ordered.2.2⟩
end

/-- Exact new physical visibility follows from parent-edge coupling, without
assuming any traversal equation for the updated table. -/
theorem erase_traversal (targets : List Id) (rows : Table) (forest : Forest)
    (coupled : ParentEdges rows forest) (unique : Unique rows) (ordered : OrderedForest forest) :
    traverse (erase targets rows).length (erase targets rows) .start =
      (traverse rows.length rows .start).map (eraseItem targets) := by
  rw [edges_traversal _ _ (erase_edges targets rows forest coupled)
    (erase_unique targets rows unique) (eraseForest_ordered targets forest ordered),
    eraseForest_preorder, edges_traversal rows forest coupled unique ordered]

theorem erase_traversal_ids (targets : List Id) (rows : Table) (forest : Forest)
    (coupled : ParentEdges rows forest) (unique : Unique rows) (ordered : OrderedForest forest) :
    (traverse (erase targets rows).length (erase targets rows) .start).map Item.id =
      (traverse rows.length rows .start).map Item.id := by
  rw [erase_traversal targets rows forest coupled unique ordered]
  simp [List.map_map, Function.comp_def]

private def a : Id := ⟨1, [65]⟩
private def b : Id := ⟨2, [65]⟩
private def m : Id := ⟨3, [65]⟩
private def fixture : Table :=
  [⟨⟨a, .text 97 false⟩, .start⟩, ⟨⟨b, .text 98 false⟩, .item a⟩,
   ⟨⟨m, .split⟩, .item b⟩]
/-- PASS+FAIL: deleting a parent retains its live child and descendant marker;
this is not physical removal of the selected node or its subtree. -/
theorem hidden_parent_control :
    (erase [a] fixture).map Row.item =
      [⟨a, .text 97 true⟩, ⟨b, .text 98 false⟩, ⟨m, .split⟩] ∧
    (erase [a] fixture).map Row.item ≠ [] := by decide
private def fixtureForest : Forest := .cons (.node ⟨a, .text 97 false⟩
  (.cons (.node ⟨b, .text 98 false⟩ (.cons (.node ⟨m, .split⟩ .nil) .nil)) .nil)) .nil

theorem retained_child_control :
    NotionCoreOriginTree.preorder (eraseForest [a] fixtureForest) =
      [⟨a, .text 97 true⟩, ⟨b, .text 98 false⟩, ⟨m, .split⟩] ∧
    NotionCoreOriginTree.preorder (eraseForest [a] fixtureForest) ≠ [⟨a, .text 97 true⟩] := by decide

/-- PASS+FAIL: a raw delete naming a marker leaves it a marker. -/
theorem marker_control : eraseItem [m] ⟨m, .split⟩ = ⟨m, .split⟩ ∧
    eraseItem [m] ⟨m, .split⟩ ≠ ⟨m, .text 0 true⟩ := by decide
#print axioms erase_traversal
end Sal.MRDTs.Instances.NotionCoreParentErase
