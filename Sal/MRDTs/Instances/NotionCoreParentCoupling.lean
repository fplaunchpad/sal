import Sal.MRDTs.Instances.NotionCoreParentMap

/-! Recover ordered parent-map models from exact edge coupling and unique IDs.
No traversal or desired observation equation is a premise. Source issuance and
transaction decoding remain separate from this structural integration. -/
namespace Sal.MRDTs.Instances.NotionCoreParentCoupling
open NotionRunAllocation (Id)
open NotionCoreOriginTree (Item Origin Tree Forest)
open NotionCoreParentMap

mutual
def OrderedTree : Tree → Prop
  | .node _ children => OrderedForest children
def OrderedForest : Forest → Prop
  | .nil => True
  | .cons tree rest =>
      (Forest.cons tree rest).roots.Pairwise NotionCoreSourceInvariant.Desc ∧
        OrderedTree tree ∧ OrderedForest rest
end

abbrev treeIds (tree : Tree) := (NotionCoreOriginTree.preorderTree tree).map Item.id
abbrev forestIds (forest : Forest) := (NotionCoreOriginTree.preorder forest).map Item.id

@[simp] theorem treeIds_node (item : Item) (children : Forest) :
    treeIds (.node item children) = item.id :: forestIds children := rfl
@[simp] theorem forestIds_nil : forestIds .nil = [] := rfl
@[simp] theorem forestIds_cons (tree : Tree) (rest : Forest) :
    forestIds (.cons tree rest) = treeIds tree ++ forestIds rest := List.map_append

mutual
theorem treeRows_ids (parent : Origin) (tree : Tree) :
    (treeRows parent tree).map (fun row => row.item.id) = treeIds tree := by
  cases tree with
  | node item children => simp [treeRows, forestRows_ids]
theorem forestRows_ids (parent : Origin) (forest : Forest) :
    (forestRows parent forest).map (fun row => row.item.id) = forestIds forest := by
  cases forest with
  | nil => rfl
  | cons tree rest => simp [forestRows, treeRows_ids, forestRows_ids]
end

mutual
theorem treeRows_origins (parent : Origin) (tree : Tree) (row : Row)
    (member : row ∈ treeRows parent tree) :
    row.origin = parent ∨ ∃ id ∈ treeIds tree, row.origin = .item id := by
  cases tree with
  | node item children =>
    simp only [treeRows, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inl rfl
    · rcases forestRows_origins (.item item.id) children row member with same | ⟨id, inside, same⟩
      · exact Or.inr ⟨item.id, by simp, same⟩
      · exact Or.inr ⟨id, by simp [inside], same⟩
theorem forestRows_origins (parent : Origin) (forest : Forest) (row : Row)
    (member : row ∈ forestRows parent forest) :
    row.origin = parent ∨ ∃ id ∈ forestIds forest, row.origin = .item id := by
  cases forest with
  | nil => simp [forestRows] at member
  | cons tree rest =>
    rcases List.mem_append.mp member with head | tail
    · rcases treeRows_origins parent tree row head with same | ⟨id, inside, same⟩
      · exact Or.inl same
      · exact Or.inr ⟨id, by simp [inside], same⟩
    · rcases forestRows_origins parent rest row tail with same | ⟨id, inside, same⟩
      · exact Or.inl same
      · exact Or.inr ⟨id, by simp [inside], same⟩
end

def SafeParent (parent : Origin) (ids : List Id) : Prop := ∀ id ∈ ids, parent ≠ .item id
def SafeContext (extra : Table) (ids : List Id) : Prop :=
  ∀ row ∈ extra, ∀ id ∈ ids, row.origin ≠ .item id

theorem childIds_append (left right : Table) (parent : Origin) :
    childIds (left ++ right) parent = childIds left parent ++ childIds right parent := by
  simp [childIds]

theorem childIds_absent (rows : Table) (parent : Origin)
    (absent : ∀ row ∈ rows, row.origin ≠ parent) : childIds rows parent = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro row member
  simp [absent row member]

theorem childIds_forest_absent (parent query : Origin) (forest : Forest)
    (different : parent ≠ query) (safe : ∀ id ∈ forestIds forest, query ≠ .item id) :
    childIds (forestRows parent forest) query = [] := by
  apply childIds_absent
  intro row member same
  rcases forestRows_origins parent forest row member with original | ⟨id, inside, original⟩
  · exact different (original.symm.trans same)
  · exact safe id inside (same.symm.trans original)

mutual
theorem childIds_tree_parent (parent : Origin) (tree : Tree)
    (safe : SafeParent parent (treeIds tree)) :
    childIds (treeRows parent tree) parent = [tree.item.id] := by
  cases tree with
  | node item children =>
    have head := safe item.id (by simp)
    have tail : ∀ id ∈ forestIds children, parent ≠ .item id :=
      fun id member => safe id (by simp [member])
    simp only [treeRows, childIds, List.filterMap_cons]
    change item.id :: childIds (forestRows (.item item.id) children) parent = [item.id]
    rw [childIds_forest_absent (.item item.id) parent children head.symm tail]
theorem childIds_forest_parent (parent : Origin) (forest : Forest)
    (safe : SafeParent parent (forestIds forest)) :
    childIds (forestRows parent forest) parent = forest.roots := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
    have head : SafeParent parent (treeIds tree) :=
      fun id member => safe id (by simp [member])
    have tail : SafeParent parent (forestIds rest) :=
      fun id member => safe id (by simp [member])
    rw [forestRows, childIds_append, childIds_tree_parent parent tree head,
      childIds_forest_parent parent rest tail]
    rfl
end

theorem childIds_permutation {left right : Table} (permutation : left.Perm right) (parent : Origin) :
    (childIds left parent).Perm (childIds right parent) :=
  permutation.filterMap _

theorem adjacency_context (rows extra : Table) (parent : Origin) (forest : Forest)
    (coupled : rows.Perm (extra ++ forestRows parent forest))
    (outside : ∀ row ∈ extra, row.origin ≠ parent)
    (safe : SafeParent parent (forestIds forest)) :
    (childIds rows parent).Perm forest.roots := by
  have permutation := childIds_permutation coupled parent
  simpa only [childIds_append, childIds_absent extra parent outside,
    childIds_forest_parent parent forest safe, List.nil_append] using permutation

theorem generated_safe (parent : Origin) (forest : Forest) (targets : List Id)
    (parentSafe : SafeParent parent targets)
    (apart : List.Disjoint targets (forestIds forest)) :
    SafeContext (forestRows parent forest) targets := by
  intro row member id selected collision
  rcases forestRows_origins parent forest row member with old | ⟨other, inside, old⟩
  · exact parentSafe id selected (old.symm.trans collision)
  · have same : other = id := Origin.item.inj (old.symm.trans collision)
    exact List.disjoint_left.mp apart selected (same ▸ inside)

theorem generated_tree_safe (parent : Origin) (tree : Tree) (targets : List Id)
    (parentSafe : SafeParent parent targets)
    (apart : List.Disjoint targets (treeIds tree)) :
    SafeContext (treeRows parent tree) targets := by
  intro row member id selected collision
  rcases treeRows_origins parent tree row member with old | ⟨other, inside, old⟩
  · exact parentSafe id selected (old.symm.trans collision)
  · have same : other = id := Origin.item.inj (old.symm.trans collision)
    exact List.disjoint_left.mp apart selected (same ▸ inside)

theorem ordered_roots (forest : Forest) (ordered : OrderedForest forest) :
    forest.roots.Pairwise NotionCoreSourceInvariant.Desc := by
  cases forest with
  | nil => exact .nil
  | cons tree rest => exact ordered.1

private theorem swap_suffix {A : Type} [DecidableEq A] (extra head tail : List A) :
    (extra ++ (head ++ tail)).Perm ((extra ++ tail) ++ head) := by
  apply List.perm_iff_count.mpr
  intro value
  simp only [List.count_append]
  omega

theorem unique_context_ids {rows extra : Table} {parent : Origin} {forest : Forest}
    (unique : Unique rows) (coupled : rows.Perm (extra ++ forestRows parent forest)) :
    (forestIds forest).Nodup := by
  have known := (coupled.map (fun (row : Row) => row.item.id)).nodup_iff.mp unique
  simp only [List.map_append, forestRows_ids] at known
  exact (List.nodup_append'.mp known).2.1

theorem unique_tree_context_ids {rows extra : Table} {parent : Origin} {tree : Tree}
    (unique : Unique rows) (coupled : rows.Perm (extra ++ treeRows parent tree)) :
    (treeIds tree).Nodup := by
  have known := (coupled.map (fun (row : Row) => row.item.id)).nodup_iff.mp unique
  simp only [List.map_append, treeRows_ids] at known
  exact (List.nodup_append'.mp known).2.1

mutual
theorem tree_model_context (rows extra : Table) (parent : Origin) (tree : Tree)
    (coupled : rows.Perm (extra ++ treeRows parent tree)) (unique : Unique rows)
    (outside : SafeContext extra (treeIds tree)) (parentSafe : SafeParent parent (treeIds tree))
    (ordered : OrderedTree tree) : TreeModel rows parent tree := by
  cases tree with
  | node item children =>
    have itemUnique := unique_tree_context_ids unique coupled
    have childUnique := (List.nodup_cons.mp itemUnique).1
    have childParentSafe : SafeParent (.item item.id) (forestIds children) := by
      intro id member collision
      exact childUnique ((Origin.item.inj collision) ▸ member)
    have parentHead : parent ≠ .item item.id := parentSafe item.id (by simp)
    have newCoupled : rows.Perm ((extra ++ [⟨item, parent⟩]) ++ forestRows (.item item.id) children) := by
      simpa only [treeRows, List.append_assoc, List.singleton_append] using coupled
    have newSafe : SafeContext (extra ++ [⟨item, parent⟩]) (forestIds children) := by
      intro row member id inside
      rcases List.mem_append.mp member with old | new
      · exact outside row old id (by simp [inside])
      · have same := List.mem_singleton.mp new
        subst row
        exact parentSafe id (by simp [inside])
    have noParent : ∀ row ∈ extra ++ [⟨item, parent⟩], row.origin ≠ .item item.id := by
      intro row member
      rcases List.mem_append.mp member with old | new
      · exact outside row old item.id (by simp)
      · have same := List.mem_singleton.mp new
        subst row
        exact parentHead
    have adjacency := adjacency_context rows (extra ++ [⟨item, parent⟩]) (.item item.id) children
      newCoupled noParent childParentSafe
    have models := trees_model_context rows (extra ++ [⟨item, parent⟩]) (.item item.id) children
      newCoupled unique newSafe childParentSafe ordered
    have member : (⟨item, parent⟩ : Row) ∈ rows :=
      coupled.mem_iff.mpr (List.mem_append_right _ (by simp [treeRows]))
    exact .node (lookup_member rows _ unique member)
      (.model adjacency (ordered_roots children ordered) models)

theorem trees_model_context (rows extra : Table) (parent : Origin) (forest : Forest)
    (coupled : rows.Perm (extra ++ forestRows parent forest)) (unique : Unique rows)
    (outside : SafeContext extra (forestIds forest)) (parentSafe : SafeParent parent (forestIds forest))
    (ordered : OrderedForest forest) : TreesModel rows parent forest := by
  cases forest with
  | nil => exact .nil
  | cons tree rest =>
    have idsUnique := unique_context_ids unique coupled
    simp only [forestIds_cons] at idsUnique
    have separated := (List.nodup_append'.mp idsUnique).2.2
    have outside' : SafeContext extra (treeIds tree ++ forestIds rest) := by
      simpa only [forestIds_cons] using outside
    have parentSafe' : SafeParent parent (treeIds tree ++ forestIds rest) := by
      simpa only [forestIds_cons] using parentSafe
    have headParent : SafeParent parent (treeIds tree) :=
      fun id member => parentSafe' id (List.mem_append_left _ member)
    have tailParent : SafeParent parent (forestIds rest) :=
      fun id member => parentSafe' id (List.mem_append_right _ member)
    have headCoupled : rows.Perm ((extra ++ forestRows parent rest) ++ treeRows parent tree) :=
      coupled.trans (by simpa only [forestRows] using swap_suffix extra (treeRows parent tree) (forestRows parent rest))
    have headSafe : SafeContext (extra ++ forestRows parent rest) (treeIds tree) := by
      intro row member id inside
      rcases List.mem_append.mp member with old | sibling
      · exact outside' row old id (List.mem_append_left _ inside)
      · exact generated_safe parent rest (treeIds tree) headParent separated row sibling id inside
    have tailCoupled : rows.Perm ((extra ++ treeRows parent tree) ++ forestRows parent rest) := by
      simpa only [forestRows, List.append_assoc] using coupled
    have tailSafe : SafeContext (extra ++ treeRows parent tree) (forestIds rest) := by
      intro row member id inside
      rcases List.mem_append.mp member with old | sibling
      · exact outside' row old id (List.mem_append_right _ inside)
      · exact generated_tree_safe parent tree (forestIds rest) tailParent
          (List.disjoint_left.mpr (fun _ inRest inTree => separated inTree inRest)) row sibling id inside
    exact .cons
      (tree_model_context rows (extra ++ forestRows parent rest) parent tree headCoupled unique headSafe headParent ordered.2.1)
      (trees_model_context rows (extra ++ treeRows parent tree) parent rest tailCoupled unique tailSafe tailParent ordered.2.2)
end

/-- Exact parent records plus source sibling order and unique IDs establish
the lookup/adjacency forest model. Neither a traversal equation nor the model
being proved is supplied as a premise. -/
theorem edges_model (rows : Table) (forest : Forest) (coupled : ParentEdges rows forest)
    (unique : Unique rows) (ordered : OrderedForest forest) : ForestModel rows .start forest := by
  have coupled' : rows.Perm ([] ++ forestRows .start forest) := by simpa using coupled
  have safe : SafeParent .start (forestIds forest) := by intro id member; simp
  have outside : SafeContext [] (forestIds forest) := by intro row member; simp at member
  exact .model (adjacency_context rows [] .start forest coupled' (by simp) safe)
    (ordered_roots forest ordered) (trees_model_context rows [] .start forest coupled' unique outside safe ordered)

theorem edges_traversal (rows : Table) (forest : Forest) (coupled : ParentEdges rows forest)
    (unique : Unique rows) (ordered : OrderedForest forest) :
    traverse rows.length rows .start = NotionCoreOriginTree.preorder forest := by
  exact traversal_model rows .start forest (edges_model rows forest coupled unique ordered)
    (unique_context_ids (extra := []) (parent := .start) unique
      (by simpa only [List.nil_append, ParentEdges] using coupled))

theorem insertChild_ordered (fresh : Tree) (old : Forest)
    (oldOrdered : OrderedForest old) (freshOrdered : OrderedTree fresh)
    (dominates : ∀ id ∈ old.roots, NotionRunAllocation.Before id fresh.item.id) :
    OrderedForest (NotionCoreOriginTree.insertChild fresh old) := by
  rw [NotionCoreOriginTree.insertChild_first fresh old dominates]
  refine ⟨List.pairwise_cons.mpr ⟨?_, ordered_roots old oldOrdered⟩, freshOrdered, oldOrdered⟩
  intro id member
  exact Or.inl (dominates id member)

mutual
theorem insertTree_root (origin : Id) (fresh old next : Tree)
    (accepted : NotionCoreOriginTree.insertTree origin fresh old = some next) :
    next.item.id = old.item.id := by
  cases old with
  | node item children =>
    by_cases hit : item.id = origin
    · simp only [NotionCoreOriginTree.insertTree, if_pos hit, Option.some.injEq] at accepted
      subst next
      rfl
    · cases changed : NotionCoreOriginTree.insertForest origin fresh children with
      | none => simp [NotionCoreOriginTree.insertTree, hit, changed] at accepted
      | some children' =>
        simp only [NotionCoreOriginTree.insertTree, if_neg hit, changed,
          Option.map_some, Option.some.injEq] at accepted
        subst next
        rfl
theorem insertForest_roots (origin : Id) (fresh : Tree) (old next : Forest)
    (accepted : NotionCoreOriginTree.insertForest origin fresh old = some next) :
    next.roots = old.roots := by
  cases old with
  | nil => simp [NotionCoreOriginTree.insertForest] at accepted
  | cons tree rest =>
    cases changed : NotionCoreOriginTree.insertTree origin fresh tree with
    | some tree' =>
      simp only [NotionCoreOriginTree.insertForest, changed, Option.some.injEq] at accepted
      subst next
      simp only [Forest.roots, insertTree_root origin fresh tree tree' changed]
    | none =>
      cases tail : NotionCoreOriginTree.insertForest origin fresh rest with
      | none => simp [NotionCoreOriginTree.insertForest, changed, tail] at accepted
      | some rest' =>
        simp only [NotionCoreOriginTree.insertForest, changed, tail,
          Option.map_some, Option.some.injEq] at accepted
        subst next
        simp only [Forest.roots, insertForest_roots origin fresh rest rest' tail]
end

mutual
theorem insertTree_ordered (origin : Id) (fresh old next : Tree)
    (oldOrdered : OrderedTree old) (freshOrdered : OrderedTree fresh)
    (ready : NotionCoreOriginTree.DominatesTree origin fresh.item.id old)
    (accepted : NotionCoreOriginTree.insertTree origin fresh old = some next) :
    OrderedTree next := by
  cases old with
  | node item children =>
    by_cases hit : item.id = origin
    · simp only [NotionCoreOriginTree.insertTree, if_pos hit, Option.some.injEq] at accepted
      subst next
      exact insertChild_ordered fresh children oldOrdered freshOrdered (ready.1 hit)
    · cases changed : NotionCoreOriginTree.insertForest origin fresh children with
      | none => simp [NotionCoreOriginTree.insertTree, hit, changed] at accepted
      | some children' =>
        simp only [NotionCoreOriginTree.insertTree, if_neg hit, changed,
          Option.map_some, Option.some.injEq] at accepted
        subst next
        exact insertForest_ordered origin fresh children children' oldOrdered freshOrdered ready.2 changed
theorem insertForest_ordered (origin : Id) (fresh : Tree) (old next : Forest)
    (oldOrdered : OrderedForest old) (freshOrdered : OrderedTree fresh)
    (ready : NotionCoreOriginTree.DominatesForest origin fresh.item.id old)
    (accepted : NotionCoreOriginTree.insertForest origin fresh old = some next) :
    OrderedForest next := by
  cases old with
  | nil => simp [NotionCoreOriginTree.insertForest] at accepted
  | cons tree rest =>
    cases changed : NotionCoreOriginTree.insertTree origin fresh tree with
    | some tree' =>
      simp only [NotionCoreOriginTree.insertForest, changed, Option.some.injEq] at accepted
      subst next
      have roots := insertTree_root origin fresh tree tree' changed
      refine ⟨?_, insertTree_ordered origin fresh tree tree' oldOrdered.2.1 freshOrdered ready.1 changed,
        oldOrdered.2.2⟩
      simpa only [Forest.roots, roots] using oldOrdered.1
    | none =>
      cases tail : NotionCoreOriginTree.insertForest origin fresh rest with
      | none => simp [NotionCoreOriginTree.insertForest, changed, tail] at accepted
      | some rest' =>
        simp only [NotionCoreOriginTree.insertForest, changed, tail,
          Option.map_some, Option.some.injEq] at accepted
        subst next
        have roots := insertForest_roots origin fresh rest rest' tail
        refine ⟨?_, oldOrdered.2.1,
          insertForest_ordered origin fresh rest rest' oldOrdered.2.2 freshOrdered ready.2 tail⟩
        simpa only [Forest.roots, roots] using oldOrdered.1
end

theorem insert_ordered (origin : Origin) (fresh : Tree) (old next : Forest)
    (oldOrdered : OrderedForest old) (freshOrdered : OrderedTree fresh)
    (ready : NotionCoreOriginTree.Ready origin fresh old)
    (accepted : NotionCoreOriginTree.insert origin fresh old = some next) :
    OrderedForest next := by
  cases origin with
  | start =>
    simp only [NotionCoreOriginTree.insert, Option.some.injEq] at accepted
    subst next
    exact insertChild_ordered fresh old oldOrdered freshOrdered ready
  | item id => exact insertForest_ordered id fresh old next oldOrdered freshOrdered ready accepted

theorem runTree_ordered (first : Item) (rest : List Item) :
    OrderedTree (NotionCoreOriginTree.runTree first rest) := by
  induction rest generalizing first with
  | nil => trivial
  | cons next rest ih => exact ⟨by simp [Forest.roots], ih next, trivial⟩

theorem runRows_ids (origin : Origin) (items : List Item) :
    (runRows origin items).map (fun row => row.item.id) = items.map Item.id := by
  induction items generalizing origin with
  | nil => rfl
  | cons item rest ih => simp [runRows, ih]

/-- Actual append-run parent-table traversal equals independently computed
recursive tree insertion. Exact edges, unique fresh item names, and source
sibling dominance derive the ordered forest model of the output. -/
theorem appended_run_traversal (rows : Table) (old next : Forest) (origin : Origin)
    (first : Item) (rest : List Item) (coupled : ParentEdges rows old)
    (unique : Unique rows) (ordered : OrderedForest old)
    (newUnique : ((first :: rest).map Item.id).Nodup)
    (apart : List.Disjoint (rows.map (fun row => row.item.id)) ((first :: rest).map Item.id))
    (ready : NotionCoreOriginTree.Ready origin (NotionCoreOriginTree.runTree first rest) old)
    (accepted : NotionCoreOriginTree.insert origin (NotionCoreOriginTree.runTree first rest) old = some next) :
    ForestModel (rows ++ runRows origin (first :: rest)) .start next ∧
      traverse (rows ++ runRows origin (first :: rest)).length
        (rows ++ runRows origin (first :: rest)) .start = NotionCoreOriginTree.preorder next := by
  have nextEdges := fresh_run_edges_any rows old next origin first rest coupled ready accepted
  have nextOrdered := insert_ordered origin (NotionCoreOriginTree.runTree first rest) old next
    ordered (runTree_ordered first rest) ready accepted
  have nextUnique : Unique (rows ++ runRows origin (first :: rest)) := by
    simp only [NotionCoreParentMap.Unique, List.map_append, runRows_ids]
    exact List.nodup_append'.mpr ⟨unique, newUnique, apart⟩
  exact ⟨edges_model _ _ nextEdges nextUnique nextOrdered,
    edges_traversal _ _ nextEdges nextUnique nextOrdered⟩

private def literal (counter value : Nat) (deleted : Bool := false) : Item :=
  NotionCoreOriginTree.literal counter value deleted
private def oldForest := NotionCoreOriginTree.fixture
private def oldRows : Table :=
  [⟨literal 1 100, .start⟩, ⟨literal 2 97, .start⟩,
   ⟨literal 3 98 true, .item (literal 2 97).id⟩,
   ⟨literal 4 99, .item (literal 3 98 true).id⟩]
private def freshFirst := literal 10 88
private def freshRest := [literal 11 89]
private def newForest : Forest :=
  .cons (.node (literal 2 97)
    (.cons (.node (literal 3 98 true)
      (.cons (NotionCoreOriginTree.runTree freshFirst freshRest)
        (.cons (.node (literal 4 99) .nil) .nil))) .nil))
    (.cons (.node (literal 1 100) .nil) .nil)

private theorem oldCoupled : ParentEdges oldRows oldForest := by unfold ParentEdges; decide
private theorem oldUnique : Unique oldRows := by unfold NotionCoreParentMap.Unique; decide
private theorem oldOrdered : OrderedForest oldForest := by
  simp [oldForest, NotionCoreOriginTree.fixture, OrderedForest, OrderedTree,
    Forest.roots, NotionCoreOriginTree.Tree.item, NotionCoreOriginTree.literal,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before]

/-- PASS+FAIL: the same actual appended table and independently computed tree
have the hand-derived hidden-origin traversal. The fresh run is not appended
after the later root's entire subtree. -/
theorem hidden_run_coupling_control :
    ForestModel (oldRows ++ runRows (.item (literal 3 98 true).id)
      (freshFirst :: freshRest)) .start newForest ∧
    NotionCoreOriginTree.visible (traverse
      (oldRows ++ runRows (.item (literal 3 98 true).id) (freshFirst :: freshRest)).length
      (oldRows ++ runRows (.item (literal 3 98 true).id) (freshFirst :: freshRest)) .start) =
      [97, 88, 89, 99, 100] ∧
    NotionCoreOriginTree.visible (traverse
      (oldRows ++ runRows (.item (literal 3 98 true).id) (freshFirst :: freshRest)).length
      (oldRows ++ runRows (.item (literal 3 98 true).id) (freshFirst :: freshRest)) .start) ≠
      [97, 99, 100, 88, 89] := by
  have result := appended_run_traversal oldRows oldForest newForest
    (.item (literal 3 98 true).id) freshFirst freshRest oldCoupled oldUnique oldOrdered
    (by decide) (by simp [List.disjoint_left, oldRows, freshFirst, freshRest, literal, NotionCoreOriginTree.literal])
    (by simp [oldForest, NotionCoreOriginTree.fixture, NotionCoreOriginTree.Ready,
      NotionCoreOriginTree.DominatesForest, NotionCoreOriginTree.DominatesTree,
      NotionCoreOriginTree.Tree.item, NotionCoreOriginTree.runTree, freshFirst, freshRest,
      literal, NotionCoreOriginTree.literal, Forest.roots, NotionRunAllocation.Before])
    (by rfl)
  refine ⟨result.1, ?_, ?_⟩ <;> rw [result.2] <;>
    simp [newForest, NotionCoreOriginTree.preorder, NotionCoreOriginTree.preorderTree,
      NotionCoreOriginTree.runTree, NotionCoreOriginTree.visible, freshFirst, freshRest,
      literal, NotionCoreOriginTree.literal]

private def wrongOrder : Forest :=
  .cons (.node (literal 1 100) .nil)
    (.cons (.node (literal 2 97)
      (.cons (.node (literal 3 98 true) (.cons (.node (literal 4 99) .nil) .nil)) .nil)) .nil)

/-- PASS+FAIL: exact parent edges alone admit a rival sibling enumeration.
Source sorting excludes it; dropping OrderedForest would be a false claim. -/
theorem ordering_is_needed_control :
    ParentEdges oldRows wrongOrder ∧ ¬ OrderedForest wrongOrder ∧
    traverse oldRows.length oldRows .start ≠ NotionCoreOriginTree.preorder wrongOrder := by
  refine ⟨by unfold ParentEdges; decide, ?_, ?_⟩
  · simp [wrongOrder, OrderedForest, OrderedTree, Forest.roots,
      NotionCoreOriginTree.Tree.item, literal, NotionCoreOriginTree.literal,
      NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before]
  · rw [edges_traversal oldRows oldForest oldCoupled oldUnique oldOrdered]
    decide

#print axioms edges_model
#print axioms appended_run_traversal
end Sal.MRDTs.Instances.NotionCoreParentCoupling
