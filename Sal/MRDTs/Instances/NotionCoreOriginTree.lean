import Sal.MRDTs.Instances.NotionCoreSourceInvariant

/-! Finite source-origin trees with actual origin search. START is the external
forest root, not a stored item. Preorder retains tombstones and split markers.
The map-to-tree extraction for the JavaScript parent map is not proved here.
This is the known-origin fragment: raw source #integrate also accepts orphans
which are unreachable in preorder. A failed tree search below is not a claim
that JavaScript rejects those messages.
-/
namespace Sal.MRDTs.Instances.NotionCoreOriginTree
open NotionRunAllocation (Id Before)
open NotionCoreSourceInvariant (compareIds)

inductive Kind where
  | text (value : Nat) (deleted : Bool)
  | split
  deriving DecidableEq, Repr

structure Item where
  id : Id
  kind : Kind
  deriving DecidableEq, Repr

mutual
inductive Tree where
  | node (item : Item) (children : Forest)
inductive Forest where
  | nil
  | cons (tree : Tree) (rest : Forest)
end

def Tree.item : Tree → Item | .node item _ => item

def Forest.roots : Forest → List Id
  | .nil => []
  | .cons tree rest => tree.item.id :: rest.roots

mutual
def preorderTree : Tree → List Item
  | .node item children => item :: preorder children
def preorder : Forest → List Item
  | .nil => []
  | .cons tree rest => preorderTree tree ++ preorder rest
end

/-- Literal descending-ID child insertion. On fresh IDs and an already sorted
old sibling list, this is the unique order specified by the source comparator.
The global splice theorem derives first placement from strict dominance. -/
def insertChild (fresh : Tree) : Forest → Forest
  | .nil => .cons fresh .nil
  | .cons tree rest =>
      if compareIds tree.item.id fresh.item.id = .lt then
        .cons fresh (.cons tree rest)
      else .cons tree (insertChild fresh rest)

mutual
def insertTree (origin : Id) (fresh : Tree) : Tree → Option Tree
  | .node item children =>
      if item.id = origin then some (.node item (insertChild fresh children))
      else (insertForest origin fresh children).map (.node item)
def insertForest (origin : Id) (fresh : Tree) : Forest → Option Forest
  | .nil => none
  | .cons tree rest =>
      match insertTree origin fresh tree with
      | some next => some (.cons next rest)
      | none => (insertForest origin fresh rest).map (.cons tree)
end

inductive Origin where
  | start
  | item (id : Id)
  deriving DecidableEq, Repr

def insert (origin : Origin) (fresh : Tree) (forest : Forest) : Option Forest :=
  match origin with
  | .start => some (insertChild fresh forest)
  | .item id => insertForest id fresh forest

/-- A run is a chain, matching insertRun's previous-ID origin links. -/
def runTree (first : Item) : List Item → Tree
  | [] => .node first .nil
  | next :: rest => .node first (.cons (runTree next rest) .nil)

/-- Independent list splice with an actual identity search. Missing origins
fail; no surrounding prefix/suffix equation is supplied by the caller. -/
def spliceAfter (origin : Id) (fresh : List Item) : List Item → Option (List Item)
  | [] => none
  | item :: rest =>
      if item.id = origin then some (item :: (fresh ++ rest))
      else (spliceAfter origin fresh rest).map (item :: ·)

mutual
def DominatesTree (origin fresh : Id) : Tree → Prop
  | .node item children =>
      (item.id = origin → ∀ child ∈ children.roots, Before child fresh) ∧
      DominatesForest origin fresh children
def DominatesForest (origin fresh : Id) : Forest → Prop
  | .nil => True
  | .cons tree rest => DominatesTree origin fresh tree ∧ DominatesForest origin fresh rest
end

theorem insertChild_first (fresh : Tree) (forest : Forest)
    (dominates : ∀ child ∈ forest.roots, Before child fresh.item.id) :
    insertChild fresh forest = .cons fresh forest := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
    have before := dominates tree.item.id (by simp [Forest.roots])
    have compared := (NotionCoreSourceInvariant.compare_lt_iff _ _).mpr before
    simp [insertChild, compared]

theorem runTree_preorder (first : Item) (rest : List Item) :
    preorderTree (runTree first rest) = first :: rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih => simp [runTree, preorderTree, preorder, ih]

theorem spliceAfter_append (origin : Id) (fresh left right : List Item) :
    spliceAfter origin fresh (left ++ right) =
      match spliceAfter origin fresh left with
      | some changed => some (changed ++ right)
      | none => (spliceAfter origin fresh right).map (left ++ ·) := by
  induction left with
  | nil => simp [spliceAfter]
  | cons item rest ih =>
    by_cases hit : item.id = origin
    · simp [spliceAfter, hit, List.append_assoc]
    · simp only [List.cons_append, spliceAfter, if_neg hit, ih]
      cases found : spliceAfter origin fresh rest <;>
        cases next : spliceAfter origin fresh right <;> rfl

mutual
/-- Actual recursive origin search in a tree projects to the independent
identity splice on its complete physical preorder. -/
theorem insertTree_splice (origin : Id) (fresh tree : Tree)
    (dominates : DominatesTree origin fresh.item.id tree) :
    (insertTree origin fresh tree).map preorderTree =
      spliceAfter origin (preorderTree fresh) (preorderTree tree) := by
  cases tree with
  | node item children =>
    by_cases hit : item.id = origin
    · simp only [insertTree, if_pos hit, Option.map_some, preorderTree]
      rw [insertChild_first fresh children (dominates.1 hit)]
      simp [preorder, spliceAfter, hit]
    · have ih := insertForest_splice origin fresh children dominates.2
      simpa only [insertTree, if_neg hit, Option.map_map, preorderTree,
        spliceAfter, if_neg hit, Function.comp_def] using
        congrArg (Option.map (item :: ·)) ih
/-- The enclosing preorder context is derived by recursive forest search and
list append laws. It is not an equality premise supplied by the caller. -/
theorem insertForest_splice (origin : Id) (fresh : Tree) (forest : Forest)
    (dominates : DominatesForest origin fresh.item.id forest) :
    (insertForest origin fresh forest).map preorder =
      spliceAfter origin (preorderTree fresh) (preorder forest) := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
    have treeIH := insertTree_splice origin fresh tree dominates.1
    have restIH := insertForest_splice origin fresh rest dominates.2
    simp only [insertForest, preorder, spliceAfter_append]
    rw [← treeIH]
    cases found : insertTree origin fresh tree with
    | none =>
      simp only [Option.map_none]
      simpa only [Option.map_map, preorder, Function.comp_def] using
        congrArg (Option.map (preorderTree tree ++ ·)) restIH
    | some next => simp [preorder]

end

def Ready (origin : Origin) (fresh : Tree) (forest : Forest) : Prop :=
  match origin with
  | .start => ∀ child ∈ forest.roots, Before child fresh.item.id
  | .item id => DominatesForest id fresh.item.id forest

def linearInsert (origin : Origin) (fresh old : List Item) : Option (List Item) :=
  match origin with
  | .start => some (fresh ++ old)
  | .item id => spliceAfter id fresh old

/-- Includes the START sentinel case, where inserting a greatest root child
prepends the run before all old root subtrees. -/
theorem insert_preorder (origin : Origin) (fresh : Tree) (forest : Forest)
    (ready : Ready origin fresh forest) :
    (insert origin fresh forest).map preorder =
      linearInsert origin (preorderTree fresh) (preorder forest) := by
  cases origin with
  | start =>
    simp only [insert, Option.map_some, linearInsert]
    rw [insertChild_first fresh forest ready]
    rfl
  | item id => exact insertForest_splice id fresh forest ready

theorem spliceAfter_indices (origin : Id) (fresh items : List Item)
    (present : origin ∈ items.map Item.id) :
    spliceAfter origin fresh items =
      some (items.take ((items.map Item.id).idxOf origin + 1) ++ fresh ++
        items.drop ((items.map Item.id).idxOf origin + 1)) := by
  induction items with
  | nil => simp at present
  | cons item rest ih =>
    by_cases hit : item.id = origin
    · simp [spliceAfter, hit]
    · have inside : origin ∈ rest.map Item.id := by
        simpa [Ne.symm hit] using present
      simp [spliceAfter, hit, ih inside, Nat.add_assoc]

/-- The global immediate splice coordinate is derived from origin search and
physical preorder, not supplied as a surrounding-context equality. No unique
address premise is needed for first-occurrence search; a unique source item
map makes this the unique origin occurrence. Hidden items remain searchable. -/
theorem insert_item_indices (origin : Id) (fresh : Tree) (forest : Forest)
    (ready : DominatesForest origin fresh.item.id forest)
    (present : origin ∈ (preorder forest).map Item.id) :
    (insert (.item origin) fresh forest).map preorder =
      some ((preorder forest).take (((preorder forest).map Item.id).idxOf origin + 1) ++
        preorderTree fresh ++
        (preorder forest).drop (((preorder forest).map Item.id).idxOf origin + 1)) := by
  rw [insert_preorder (.item origin) fresh forest ready]
  exact spliceAfter_indices origin (preorderTree fresh) (preorder forest) present

/-- The nonempty run is linked as a chain and the global splice contains
exactly its literal inserted physical items in their run order. -/
theorem insert_run_indices (origin : Id) (first : Item) (rest : List Item) (forest : Forest)
    (ready : DominatesForest origin first.id forest)
    (present : origin ∈ (preorder forest).map Item.id) :
    (insert (.item origin) (runTree first rest) forest).map preorder =
      some ((preorder forest).take (((preorder forest).map Item.id).idxOf origin + 1) ++
        (first :: rest) ++
        (preorder forest).drop (((preorder forest).map Item.id).idxOf origin + 1)) := by
  have head : (runTree first rest).item.id = first.id := by cases rest <;> rfl
  simpa [runTree_preorder] using
    insert_item_indices origin (runTree first rest) forest (head ▸ ready) present

/-- A failed identity search is not silently modeled as appending text. -/
theorem spliceAfter_missing (origin : Id) (fresh items : List Item)
    (absent : origin ∉ items.map Item.id) : spliceAfter origin fresh items = none := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have distinct : item.id ≠ origin := by
      intro same
      exact absent (by simp [same])
    have tail : origin ∉ rest.map Item.id := fun mem => absent (by simp [mem])
    simp [spliceAfter, distinct, ih tail]

theorem missing_origin_fails (origin : Id) (fresh : Tree) (forest : Forest)
    (ready : DominatesForest origin fresh.item.id forest)
    (absent : origin ∉ (preorder forest).map Item.id) :
    insert (.item origin) fresh forest = none := by
  have projected := insert_preorder (.item origin) fresh forest ready
  rw [linearInsert, spliceAfter_missing origin _ _ absent] at projected
  exact Option.map_eq_none_iff.mp projected

/-- Visible text is a projection; origins are searched in the unfiltered
physical tree, so tombstoned characters and split markers retain their role. -/
def visible (items : List Item) : List Nat := items.filterMap fun item =>
  match item.kind with
  | .text value false => some value
  | _ => none

def literal (counter value : Nat) (deleted : Bool := false) : Item :=
  ⟨⟨counter, [65]⟩, .text value deleted⟩

def fixture : Forest :=
  .cons (.node (literal 2 97) (.cons (.node (literal 3 98 true)
    (.cons (.node (literal 4 99) .nil) .nil)) .nil))
    (.cons (.node (literal 1 100) .nil) .nil)

/-- PASS+FAIL: search reaches a hidden nonroot origin. Its child subtree stays
behind the new run, and the tombstone remains in physical preorder. -/
theorem hidden_nonroot_control :
    let fresh := runTree (literal 10 88) [literal 11 89]
    let result := (insert (.item (literal 3 98 true).id) fresh fixture).map preorder
    result.map (List.map Item.id) = some ([2, 3, 10, 11, 4, 1].map fun n => ⟨n, [65]⟩) ∧
    result.map visible = some [97, 88, 89, 99, 100] ∧
    result.map visible ≠ some [97, 99, 100, 88, 89] := by
  simp [insert, insertForest, insertTree, insertChild, runTree, fixture, literal,
    Tree.item, preorderTree, preorder, compareIds, visible]

/-- PASS+FAIL: inserting at a leaf also finds the enclosing forest context;
it does not append after a later root sibling. -/
theorem leaf_control :
    let result := (insert (.item (literal 4 99).id)
      (runTree (literal 10 88) []) fixture).map preorder
    result.map visible = some [97, 99, 88, 100] ∧
    result.map visible ≠ some [97, 99, 100, 88] := by
  simp [insert, insertForest, insertTree, insertChild, runTree, fixture, literal,
    preorderTree, preorder, visible]

/-- PASS+FAIL: START is not stored as an item. A new greatest root chain goes
before the complete existing forest, rather than after its first visible item. -/
theorem start_control :
    let result := (insert .start (runTree (literal 10 88) []) fixture).map preorder
    result.map visible = some [88, 97, 99, 100] ∧
    result.map visible ≠ some [97, 88, 99, 100] := by
  simp [insert, insertChild, runTree, fixture, literal, Tree.item, preorderTree,
    preorder, compareIds, visible]

/-- PASS+FAIL: an absent origin fails even in a nonempty document. -/
theorem missing_control :
    let result := (insert (.item (literal 99 0).id)
      (runTree (literal 10 88) []) fixture).map preorder
    result = none ∧ result ≠ some (preorder fixture) := by
  simp [insert, insertForest, insertTree, fixture, literal]

/-- At the modified node, ordered insertion agrees with complete source-key
sorting. This is a structural ordering premise, not a preorder effect premise. -/
theorem insertChild_sorted_keys (fresh : Tree) (forest : Forest)
    (dominates : ∀ child ∈ forest.roots, Before child fresh.item.id)
    (ordered : forest.roots.Pairwise NotionCoreSourceInvariant.Desc) :
    (insertChild fresh forest).roots =
      NotionCoreSourceInvariant.sortChildren (fresh.item.id :: forest.roots) := by
  rw [insertChild_first fresh forest dominates]
  simp only [Forest.roots]
  rw [NotionCoreSourceInvariant.sort_fresh_first fresh.item.id forest.roots dominates]
  have old : NotionCoreSourceInvariant.sortChildren forest.roots = forest.roots :=
    List.mergeSort_eq_self NotionCoreSourceInvariant.Desc ordered
  rw [old]

private theorem splice_permutation {Value : Type} [DecidableEq Value]
    (before fresh after : List Value) :
    (before ++ fresh ++ after).Perm ((before ++ after) ++ fresh) := by
  apply List.perm_iff_count.mpr
  intro value
  simp only [List.count_append]
  omega

theorem splice_nodup {Value : Type} [DecidableEq Value] (old fresh : List Value)
    (position : Nat) (oldUnique : old.Nodup) (freshUnique : fresh.Nodup)
    (disjoint : List.Disjoint old fresh) :
    (old.take position ++ fresh ++ old.drop position).Nodup := by
  have permutation := splice_permutation (old.take position) fresh (old.drop position)
  rw [List.take_append_drop] at permutation
  exact permutation.nodup_iff.mpr (List.nodup_append'.mpr ⟨oldUnique, freshUnique, disjoint⟩)

/-- The derived global splice preserves the source's unique item-key property
when the run's keys are fresh and internally unique. Freshness is an allocation
premise here; no parent-map correspondence theorem is assumed. -/
theorem insert_preserves_unique_ids (origin : Id) (fresh : Tree) (old next : Forest)
    (ready : DominatesForest origin fresh.item.id old)
    (present : origin ∈ (preorder old).map Item.id)
    (oldUnique : ((preorder old).map Item.id).Nodup)
    (freshUnique : ((preorderTree fresh).map Item.id).Nodup)
    (disjoint : List.Disjoint ((preorder old).map Item.id) ((preorderTree fresh).map Item.id))
    (accepted : insert (.item origin) fresh old = some next) :
    ((preorder next).map Item.id).Nodup := by
  have projected := insert_item_indices origin fresh old ready present
  rw [accepted] at projected
  simp only [Option.map_some, Option.some.injEq] at projected
  have addresses := congrArg (List.map Item.id) projected
  simp only [List.map_append, List.map_take, List.map_drop] at addresses
  rw [addresses]
  exact splice_nodup _ _ _ oldUnique freshUnique disjoint

/-- PASS+FAIL: split-marker origins are retained and found, although they have
no visible character. Source block ownership is outside this tree fixture. -/
theorem split_marker_control :
    let marker : Item := ⟨⟨2, [65]⟩, .split⟩
    let old : Forest := .cons (.node marker
      (.cons (.node (literal 3 97) .nil) .nil)) .nil
    let result := (insert (.item marker.id) (runTree (literal 10 88) []) old).map preorder
    result.map visible = some [88, 97] ∧ result.map visible ≠ none := by
  simp [insert, insertForest, insertTree, insertChild, runTree, literal,
    Tree.item, preorderTree, preorder, compareIds, visible]

#print axioms insertForest_splice
#print axioms insert_run_indices

end Sal.MRDTs.Instances.NotionCoreOriginTree
