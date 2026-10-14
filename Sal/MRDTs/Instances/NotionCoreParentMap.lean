import Sal.MRDTs.Instances.NotionCoreOriginTree
import Mathlib.Data.List.Nodup

/-! Source-shaped finite parent tables and actual child-enumerating traversal.
Rows store physical items and origin links, independently of the rose tree.
The extraction theorem uses a structural adjacency/lookup relation, not a
traversal equality. Raw orphan rows remain permitted by fresh integration.
-/
namespace Sal.MRDTs.Instances.NotionCoreParentMap
open NotionRunAllocation (Id)
open NotionCoreOriginTree (Item Origin Tree Forest)

structure Row where
  item : Item
  origin : Origin
  deriving DecidableEq, Repr

abbrev Table := List Row

def lookup (rows : Table) (id : Id) : Option Row :=
  rows.find? (fun row => decide (row.item.id = id))

def childIds (rows : Table) (origin : Origin) : List Id :=
  rows.filterMap fun row => if row.origin = origin then some row.item.id else none

def sortedChildren (rows : Table) (origin : Origin) : List Id :=
  NotionCoreSourceInvariant.sortChildren (childIds rows origin)

/-- Source fresh-key integration appends the record without requiring its
origin to be present. Freshness and non-self-origin are caller obligations. -/
def insertFresh (rows : Table) (row : Row) : Table := rows ++ [row]

/-- Actual recursive child enumeration with a finite fuel bound. The theorem
below derives a sufficient bound from a finite structural graph model. -/
def traverse : Nat → Table → Origin → List Item
  | 0, _, _ => []
  | fuel + 1, rows, origin =>
      (sortedChildren rows origin).flatMap fun id =>
        match lookup rows id with
        | none => []
        | some row => row.item :: traverse fuel rows (.item id)

def buildForest (rows : Table) (children : Id → Forest) : List Id → Forest
  | [] => .nil
  | id :: rest =>
      match lookup rows id with
      | none => buildForest rows children rest
      | some row => .cons (.node row.item (children id)) (buildForest rows children rest)

/-- The same executable search builds the finite origin forest, retaining
physical tombstones and split markers exactly as traversal does. -/
def extract : Nat → Table → Origin → Forest
  | 0, _, _ => .nil
  | fuel + 1, rows, origin =>
      buildForest rows (fun id => extract fuel rows (.item id)) (sortedChildren rows origin)

mutual
def treeHeight : Tree → Nat
  | .node _ children => forestHeight children + 1
def forestHeight : Forest → Nat
  | .nil => 0
  | .cons tree rest => max (treeHeight tree) (forestHeight rest)
end

/- Structural graph correspondence: each tree node has the actual table row,
and each child list is exactly the table's adjacency list up to permutation,
with the source comparator's descending order. No traversal equation appears. -/
mutual
inductive TreeModel (rows : Table) : Origin → Tree → Prop where
  | node {parent item children} : lookup rows item.id = some ⟨item, parent⟩ →
      ForestModel rows (.item item.id) children → TreeModel rows parent (.node item children)
inductive ForestModel (rows : Table) : Origin → Forest → Prop where
  | model {parent forest} : (childIds rows parent).Perm forest.roots →
      forest.roots.Pairwise NotionCoreSourceInvariant.Desc →
      TreesModel rows parent forest → ForestModel rows parent forest
inductive TreesModel (rows : Table) : Origin → Forest → Prop where
  | nil {parent} : TreesModel rows parent .nil
  | cons {parent tree rest} : TreeModel rows parent tree →
      TreesModel rows parent rest → TreesModel rows parent (.cons tree rest)
end

theorem sorted_children_model {rows : Table} {parent : Origin} {forest : Forest}
    (model : ForestModel rows parent forest) : sortedChildren rows parent = forest.roots := by
  cases model with
  | model permutation ordered trees =>
    rw [sortedChildren, NotionCoreSourceInvariant.sort_permutation permutation]
    exact List.mergeSort_eq_self NotionCoreSourceInvariant.Desc ordered

private theorem buildForest_preorder (rows : Table) (children : Id → Forest) (keys : List Id) :
    NotionCoreOriginTree.preorder (buildForest rows children keys) =
      keys.flatMap (fun id => match lookup rows id with
        | none => []
        | some row => row.item :: NotionCoreOriginTree.preorder (children id)) := by
  induction keys with
  | nil => rfl
  | cons id rest ih =>
    cases found : lookup rows id <;>
      simp [buildForest, found, NotionCoreOriginTree.preorder,
        NotionCoreOriginTree.preorderTree, ih]

/-- Tree extraction and raw parent-map traversal are executable counterparts,
not separate assumed observations. This theorem requires no well-formedness. -/
theorem extract_preorder (fuel : Nat) (rows : Table) (origin : Origin) :
    NotionCoreOriginTree.preorder (extract fuel rows origin) = traverse fuel rows origin := by
  induction fuel generalizing origin with
  | zero => rfl
  | succ fuel ih =>
    simp only [extract, traverse, buildForest_preorder]
    congr 1
    funext id
    cases found : lookup rows id <;> simp [ih]

def roots (forest : Forest) : List Tree :=
  match forest with
  | .nil => []
  | .cons tree rest => tree :: roots rest

theorem root_height_bound (forest : Forest) (tree : Tree) (member : tree ∈ roots forest) :
    treeHeight tree ≤ forestHeight forest := by
  cases forest with
  | nil => simp [roots] at member
  | cons head rest =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact (root_height_bound rest tree member).trans (Nat.le_max_right _ _)

private theorem buildForest_model (rows : Table) (parent : Origin) (forest : Forest)
    (models : TreesModel rows parent forest) (children : Id → Forest)
    (correct : ∀ item child, .node item child ∈ roots forest →
      TreeModel rows parent (.node item child) → children item.id = child) :
    buildForest rows children forest.roots = forest := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
    cases models with
    | cons treeModel restModels =>
      cases tree with
      | node item child =>
        cases treeModel with
        | node found childModel =>
          simp only [Forest.roots, NotionCoreOriginTree.Tree.item, buildForest, found]
          rw [correct item child (by simp [roots]) (.node found childModel)]
          congr 1
          apply buildForest_model rows parent rest restModels children
          intro item child member model
          exact correct item child (by simp [roots, member]) model

/-- Fuel suffices by structural height; adjacency and actual row lookup
recover the entire ordered tree, rather than only its visible text. -/
theorem extract_model (fuel : Nat) (rows : Table) (parent : Origin) (forest : Forest)
    (model : ForestModel rows parent forest) (enough : forestHeight forest ≤ fuel) :
    extract fuel rows parent = forest := by
  induction fuel generalizing parent forest with
  | zero =>
    cases forest with
    | nil => rfl
    | cons tree rest =>
      cases tree with
      | node item children => simp [forestHeight, treeHeight] at enough
  | succ fuel ih =>
    rw [extract, sorted_children_model model]
    cases model with
    | model adjacency ordered trees =>
      apply buildForest_model rows parent forest trees
      intro item child member memberModel
      have height := (root_height_bound forest (.node item child) member).trans enough
      have bound : forestHeight child ≤ fuel := by
        simp only [treeHeight] at height
        omega
      cases memberModel with
      | node found childModel => exact ih _ _ childModel bound

mutual
theorem tree_covered (rows : Table) (parent : Origin) (tree : Tree)
    (model : TreeModel rows parent tree) :
    ∀ item ∈ NotionCoreOriginTree.preorderTree tree,
      item.id ∈ rows.map (fun row => row.item.id) := by
  cases tree with
  | node root children =>
    cases model with
    | node found childModel =>
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_map.mpr ⟨⟨item, parent⟩, List.mem_of_find?_eq_some found, rfl⟩
      · cases childModel with
        | model adjacency ordered models =>
          exact trees_covered rows (.item root.id) children models item member

theorem trees_covered (rows : Table) (parent : Origin) (forest : Forest)
    (models : TreesModel rows parent forest) :
    ∀ item ∈ NotionCoreOriginTree.preorder forest,
      item.id ∈ rows.map (fun row => row.item.id) := by
  cases forest with
  | nil => simp [NotionCoreOriginTree.preorder]
  | cons tree rest =>
    cases models with
    | cons head tail =>
      intro item member
      rcases List.mem_append.mp member with member | member
      · exact tree_covered rows parent tree head item member
      · exact trees_covered rows parent rest tail item member
end

mutual
theorem tree_height_le_size (tree : Tree) :
    treeHeight tree ≤ (NotionCoreOriginTree.preorderTree tree).length := by
  cases tree with
  | node item children =>
    simpa [treeHeight, NotionCoreOriginTree.preorderTree] using
      Nat.succ_le_succ (forest_height_le_size children)

theorem forest_height_le_size (forest : Forest) :
    forestHeight forest ≤ (NotionCoreOriginTree.preorder forest).length := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
    simp only [forestHeight, NotionCoreOriginTree.preorder, List.length_append]
    apply max_le
    · exact (tree_height_le_size tree).trans (Nat.le_add_right _ _)
    · exact (forest_height_le_size rest).trans (Nat.le_add_left _ _)
end

/-- The actual table length is sufficient fuel. The bound follows from
unique represented item IDs and actual lookup membership, not termination or
preorder equations assumed of the source interpreter. Unreachable raw orphans
can increase this bound but cannot invalidate it. -/
theorem table_length_fuel (rows : Table) (parent : Origin) (forest : Forest)
    (model : ForestModel rows parent forest)
    (unique : ((NotionCoreOriginTree.preorder forest).map Item.id).Nodup) :
    forestHeight forest ≤ rows.length := by
  have covered : (NotionCoreOriginTree.preorder forest).map Item.id ⊆
      rows.map (fun row => row.item.id) := by
    intro id member
    obtain ⟨item, physicalMember, rfl⟩ := List.mem_map.mp member
    cases model with
    | model adjacency ordered models => exact trees_covered rows parent forest models item physicalMember
  have lengthBound := (List.subperm_of_subset unique covered).length_le
  have sizes : (NotionCoreOriginTree.preorder forest).length ≤ rows.length := by
    simpa only [List.length_map] using lengthBound
  exact (forest_height_le_size forest).trans sizes

/-- Full ordered physical traversal of the parent table agrees with the
represented source forest at a bound computed from the table itself. -/
theorem traversal_model (rows : Table) (parent : Origin) (forest : Forest)
    (model : ForestModel rows parent forest)
    (unique : ((NotionCoreOriginTree.preorder forest).map Item.id).Nodup) :
    traverse rows.length rows parent = NotionCoreOriginTree.preorder forest := by
  rw [← extract_preorder, extract_model _ rows parent forest model
    (table_length_fuel rows parent forest model unique)]

def originCounter : Origin → Nat
  | .start => 0
  | .item id => id.counter

def Unique (rows : Table) : Prop := (rows.map (fun row => row.item.id)).Nodup

def Increasing (rows : Table) : Prop :=
  ∀ row ∈ rows, originCounter row.origin < row.item.id.counter

def Closed (rows : Table) : Prop :=
  ∀ row ∈ rows, match row.origin with
    | .start => True
    | .item id => id ∈ rows.map (fun row => row.item.id)

def maximumCounter (rows : Table) : Nat :=
  rows.foldr (fun row bound => max row.item.id.counter bound) 0

theorem counter_bounded (rows : Table) : ∀ row ∈ rows, row.item.id.counter ≤ maximumCounter rows := by
  induction rows with
  | nil => simp
  | cons head rest ih =>
    intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact (ih row member).trans (Nat.le_max_right _ _)

theorem lookup_member (rows : Table) (row : Row) (unique : Unique rows) (member : row ∈ rows) :
    lookup rows row.item.id = some row := by
  induction rows with
  | nil => simp at member
  | cons head rest ih =>
    simp only [Unique, List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | member
    · simp [lookup]
    · have distinct : head.item.id ≠ row.item.id := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨row, member, same.symm⟩)
      simpa [lookup, distinct] using ih unique.2 member

theorem child_lookup (rows : Table) (origin : Origin) (id : Id)
    (unique : Unique rows) (member : id ∈ childIds rows origin) :
    ∃ row ∈ rows, lookup rows id = some row ∧ row.item.id = id ∧ row.origin = origin := by
  obtain ⟨row, member, selected⟩ := List.mem_filterMap.mp member
  by_cases parent : row.origin = origin
  · simp only [if_pos parent, Option.some.injEq] at selected
    exact ⟨row, member, by simpa [selected] using lookup_member rows row unique member, selected, parent⟩
  · simp [parent] at selected

private theorem buildForest_graph (rows : Table) (parent : Origin) (keys : List Id)
    (children : Id → Forest)
    (known : ∀ id ∈ keys, ∃ item, lookup rows id = some ⟨item, parent⟩ ∧ item.id = id)
    (childModels : ∀ id ∈ keys, ForestModel rows (.item id) (children id)) :
    (buildForest rows children keys).roots = keys ∧
      TreesModel rows parent (buildForest rows children keys) := by
  cases keys with
  | nil => exact ⟨rfl, .nil⟩
  | cons id rest =>
    obtain ⟨item, found, name⟩ := known id (by simp)
    have tail := buildForest_graph rows parent rest children
      (fun id member => known id (by simp [member]))
      (fun id member => childModels id (by simp [member]))
    have child : ForestModel rows (.item item.id) (children id) := by
      simpa [name] using childModels id (by simp)
    simp only [buildForest, found]
    exact ⟨by simpa [Forest.roots, NotionCoreOriginTree.Tree.item, name] using tail.1,
      .cons (.node (by simpa [name] using found) child) tail.2⟩

/-- The forest model is DERIVED from raw parent-table guards. Counter rank
excludes cycles and bounds recursive extraction; no pre-given tree, adjacency
isomorphism, or desired traversal equation is required. Orphans can remain
outside the reachable START component until their parents arrive. -/
theorem extract_rank_model (fuel : Nat) (rows : Table) (origin : Origin) (maximum : Nat)
    (unique : Unique rows) (increasing : Increasing rows)
    (bounded : ∀ row ∈ rows, row.item.id.counter ≤ maximum)
    (enough : maximum ≤ originCounter origin + fuel) :
    ForestModel rows origin (extract fuel rows origin) := by
  induction fuel generalizing origin with
  | zero =>
    have noChildren : childIds rows origin = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro id member
      obtain ⟨row, rowMember, found, name, parent⟩ := child_lookup rows origin id unique member
      have inc := increasing row rowMember
      have bound := bounded row rowMember
      rw [parent] at inc
      omega
    exact .model (by simp [extract, noChildren, Forest.roots]) (by simp [extract, Forest.roots]) .nil
  | succ fuel ih =>
    let keys := sortedChildren rows origin
    have known : ∀ id ∈ keys, ∃ item, lookup rows id = some ⟨item, origin⟩ ∧ item.id = id := by
      intro id member
      have rawMember := (NotionCoreSourceInvariant.sort_children_perm _).mem_iff.mp member
      obtain ⟨row, rowMember, found, name, parent⟩ := child_lookup rows origin id unique rawMember
      exact ⟨row.item, by simpa only [← parent] using found, name⟩
    have children : ∀ id ∈ keys, ForestModel rows (.item id) (extract fuel rows (.item id)) := by
      intro id member
      have rawMember := (NotionCoreSourceInvariant.sort_children_perm _).mem_iff.mp member
      obtain ⟨row, rowMember, found, name, parent⟩ := child_lookup rows origin id unique rawMember
      have inc := increasing row rowMember
      rw [parent, name] at inc
      have remaining : maximum ≤ originCounter (.item id) + fuel := by
        simp only [originCounter]
        omega
      exact ih (.item id) remaining
    have built := buildForest_graph rows origin keys
      (fun id => extract fuel rows (.item id)) known children
    rw [extract]
    apply ForestModel.model
    · rw [built.1]
      exact (NotionCoreSourceInvariant.sort_children_perm _).symm
    · rw [built.1]
      exact NotionCoreSourceInvariant.sort_children_pairwise _
    · exact built.2

/-- Executable extraction from raw source data uses an explicitly computed
counter bound. Known-origin row coverage is a separate closed-state theorem. -/
theorem extract_raw_model (rows : Table) (unique : Unique rows) (increasing : Increasing rows) :
    ForestModel rows .start (extract (maximumCounter rows) rows .start) :=
  extract_rank_model _ rows .start _ unique increasing (counter_bounded rows) (by simp [originCounter])

inductive Reachable (rows : Table) : Origin → Prop where
  | start : Reachable rows .start
  | item {row : Row} : row ∈ rows → Reachable rows row.origin → Reachable rows (.item row.item.id)

/-- Known-origin closure plus strict parent counter rank derives a path to
START for every stored record. Orphan coverage is not silently assumed. -/
theorem closed_reachable (rows : Table) (increasing : Increasing rows) (closed : Closed rows) :
    ∀ row ∈ rows, Reachable rows (.item row.item.id) := by
  suffices all : ∀ counter, ∀ row ∈ rows, row.item.id.counter = counter →
      Reachable rows (.item row.item.id) from fun row member => all _ row member rfl
  intro counter
  induction counter using Nat.strong_induction_on with
  | h counter ih =>
    intro row member counterEq
    cases parentEq : row.origin with
    | start => exact .item member (parentEq ▸ .start)
    | item parent =>
      have known : parent ∈ rows.map (fun row => row.item.id) := by
        simpa [Closed, parentEq] using closed row member
      obtain ⟨provider, providerMember, name⟩ := List.mem_map.mp known
      have lower := increasing row member
      rw [parentEq] at lower
      simp only [originCounter] at lower
      have providerPath := ih parent.counter (by omega) provider providerMember (congrArg Id.counter name)
      exact .item member (by simpa [name, parentEq] using providerPath)

theorem root_keys_covered (forest : Forest) :
    ∀ id ∈ forest.roots, id ∈ (NotionCoreOriginTree.preorder forest).map Item.id := by
  cases forest with
  | nil => simp [Forest.roots]
  | cons tree rest =>
    intro id member
    simp only [Forest.roots, List.mem_cons] at member
    simp only [NotionCoreOriginTree.preorder, List.map_append, List.mem_append]
    rcases member with rfl | member
    · left
      cases tree with
      | node item children => simp [NotionCoreOriginTree.preorderTree, NotionCoreOriginTree.Tree.item]
    · exact Or.inr (root_keys_covered rest id member)

theorem direct_child_covered (rows : Table) (origin : Origin) (forest : Forest)
    (model : ForestModel rows origin forest) (row : Row) (member : row ∈ rows)
    (parent : row.origin = origin) :
    row.item.id ∈ (NotionCoreOriginTree.preorder forest).map Item.id := by
  have child : row.item.id ∈ childIds rows origin := by
    exact List.mem_filterMap.mpr ⟨row, member, by simp [parent]⟩
  cases model with
  | model permutation ordered trees =>
    exact root_keys_covered forest _ (permutation.mem_iff.mp child)

mutual
theorem tree_edge_covered (rows : Table) (parent : Origin) (tree : Tree)
    (model : TreeModel rows parent tree) (origin : Id) (row : Row)
    (member : row ∈ rows) (edge : row.origin = .item origin)
    (present : origin ∈ (NotionCoreOriginTree.preorderTree tree).map Item.id) :
    row.item.id ∈ (NotionCoreOriginTree.preorderTree tree).map Item.id := by
  cases tree with
  | node item children =>
    cases model with
    | node found childModel =>
      simp only [NotionCoreOriginTree.preorderTree, List.map_cons, List.mem_cons] at present ⊢
      rcases present with same | inside
      · right
        exact direct_child_covered rows (.item item.id) children childModel row member
          (by simpa [same] using edge)
      · right
        cases childModel with
        | model adjacency ordered childModels =>
          exact trees_edge_covered rows (.item item.id) children childModels origin row member edge inside

theorem trees_edge_covered (rows : Table) (parent : Origin) (forest : Forest)
    (models : TreesModel rows parent forest) (origin : Id) (row : Row)
    (member : row ∈ rows) (edge : row.origin = .item origin)
    (present : origin ∈ (NotionCoreOriginTree.preorder forest).map Item.id) :
    row.item.id ∈ (NotionCoreOriginTree.preorder forest).map Item.id := by
  cases forest with
  | nil => simp [NotionCoreOriginTree.preorder] at present
  | cons tree rest =>
    cases models with
    | cons treeModel restModels =>
      simp only [NotionCoreOriginTree.preorder, List.map_append, List.mem_append] at present ⊢
      rcases present with head | tail
      · exact Or.inl (tree_edge_covered rows parent tree treeModel origin row member edge head)
      · exact Or.inr (trees_edge_covered rows parent rest restModels origin row member edge tail)
end

def Contains (forest : Forest) : Origin → Prop
  | .start => True
  | .item id => id ∈ (NotionCoreOriginTree.preorder forest).map Item.id

theorem reachable_covered (rows : Table) (forest : Forest)
    (model : ForestModel rows .start forest) {origin : Origin} (path : Reachable rows origin) :
    Contains forest origin := by
  induction path with
  | start => trivial
  | @item row member parentPath ih =>
    cases parentEq : row.origin with
    | start => exact direct_child_covered rows .start forest model row member parentEq
    | item id =>
      cases model with
      | model adjacency ordered trees =>
        exact trees_edge_covered rows .start forest trees id row member parentEq
          (by simpa [Contains, parentEq] using ih)

/-- Every source record is included in extraction on closed increasing tables.
Without Closed, the raw interpreter faithfully omits unreachable orphans. -/
theorem extraction_covers_rows (rows : Table) (unique : Unique rows)
    (increasing : Increasing rows) (closed : Closed rows) :
    ∀ row ∈ rows, row.item.id ∈
      (NotionCoreOriginTree.preorder (extract (maximumCounter rows) rows .start)).map Item.id := by
  intro row member
  exact reachable_covered rows _ (extract_raw_model rows unique increasing)
    (closed_reachable rows increasing closed row member)

def KnownOrigin (rows : Table) : Origin → Prop
  | .start => True
  | .item id => id ∈ rows.map (fun row => row.item.id)

/-- A structural parent-map generation history. Guards constrain actual IDs,
parent presence and allocation rank; none assumes tree extraction or rendering.
Coupling a published-demo issuer to these guards remains separate. -/
inductive Reach : Table → Prop where
  | initial : Reach []
  | integration {rows : Table} (row : Row) : Reach rows →
      row.item.id ∉ rows.map (fun row => row.item.id) → KnownOrigin rows row.origin →
      originCounter row.origin < row.item.id.counter → Reach (insertFresh rows row)

theorem reachable_unique {rows : Table} (reachable : Reach rows) : Unique rows := by
  induction reachable with
  | initial => simp [Unique]
  | @integration rows row prior fresh known rank ih =>
    simp only [Unique, insertFresh, List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append'.mpr
    refine ⟨ih, by simp, ?_⟩
    apply List.disjoint_left.mpr
    intro id member selected
    have same : id = row.item.id := List.mem_singleton.mp selected
    exact fresh (same ▸ member)

theorem reachable_increasing {rows : Table} (reachable : Reach rows) : Increasing rows := by
  induction reachable with
  | initial => simp [Increasing]
  | @integration rows row prior fresh known rank ih =>
    intro item member
    rcases List.mem_append.mp member with old | newest
    · exact ih item old
    · have same : item = row := List.mem_singleton.mp newest
      simpa [same] using rank

theorem reachable_closed {rows : Table} (reachable : Reach rows) : Closed rows := by
  induction reachable with
  | initial => simp [Closed]
  | @integration rows row prior fresh known rank ih =>
    intro item member
    have originKnown : KnownOrigin rows item.origin := by
      rcases List.mem_append.mp member with old | newest
      · exact ih item old
      · have same : item = row := List.mem_singleton.mp newest
        simpa [same] using known
    cases parentEq : item.origin with
    | start => trivial
    | item id =>
      have old : id ∈ rows.map (fun row => row.item.id) := by
        simpa [KnownOrigin, parentEq] using originKnown
      simpa only [insertFresh, List.map_append] using List.mem_append_left
        ([row.item.id]) old

/-- Raw insertion histories derive a complete acyclic ordered extraction and
cover every stored row. This is a source-graph theorem, not an RA history or
client-preparation theorem. -/
theorem reachable_extraction {rows : Table} (reachable : Reach rows) :
    ForestModel rows .start (extract (maximumCounter rows) rows .start) ∧
    ∀ row ∈ rows, row.item.id ∈
      (NotionCoreOriginTree.preorder (extract (maximumCounter rows) rows .start)).map Item.id :=
  ⟨extract_raw_model rows (reachable_unique reachable) (reachable_increasing reachable),
    extraction_covers_rows rows (reachable_unique reachable) (reachable_increasing reachable)
      (reachable_closed reachable)⟩

/-- Literal map records preserve source origins and insertion-run chaining. -/
def runRows (origin : Origin) : List Item → Table
  | [] => []
  | first :: rest => ⟨first, origin⟩ :: runRows (.item first.id) rest

mutual
def treeRows (parent : Origin) : Tree → Table
  | .node item children => ⟨item, parent⟩ :: forestRows (.item item.id) children
def forestRows (parent : Origin) : Forest → Table
  | .nil => []
  | .cons tree rest => treeRows parent tree ++ forestRows parent rest
end

/-- Source `insertRun`'s emitted parent links are exactly the rose chain's
edge table; internal characters point to the preceding character. -/
theorem run_rows (origin : Origin) (first : Item) (rest : List Item) :
    runRows origin (first :: rest) = treeRows origin (NotionCoreOriginTree.runTree first rest) := by
  induction rest generalizing origin first with
  | nil => rfl
  | cons next rest ih =>
    simpa [runRows, treeRows, forestRows, NotionCoreOriginTree.runTree] using
      congrArg (⟨first, origin⟩ :: ·) (ih (.item first.id) next)

mutual
/-- Actual origin search changes precisely the newly linked subtree's parent
records, independently of map enumeration order. -/
theorem insertTree_edges (parent : Origin) (origin : Id) (fresh old next : Tree)
    (ready : NotionCoreOriginTree.DominatesTree origin fresh.item.id old)
    (accepted : NotionCoreOriginTree.insertTree origin fresh old = some next) :
    (treeRows parent next).Perm (treeRows parent old ++ treeRows (.item origin) fresh) := by
  cases old with
  | node item children =>
    by_cases hit : item.id = origin
    · have first := NotionCoreOriginTree.insertChild_first fresh children (ready.1 hit)
      simp only [NotionCoreOriginTree.insertTree, if_pos hit, first, Option.some.injEq] at accepted
      subst next
      apply List.perm_iff_count.mpr
      intro row
      simp only [treeRows, forestRows, hit, List.count_append, List.count_cons]
      omega
    · cases found : NotionCoreOriginTree.insertForest origin fresh children with
      | none => simp [NotionCoreOriginTree.insertTree, hit, found] at accepted
      | some changed =>
        simp only [NotionCoreOriginTree.insertTree, if_neg hit, found,
          Option.map_some, Option.some.injEq] at accepted
        subst next
        have edges := insertForest_edges (.item item.id) origin fresh children changed ready.2 found
        apply List.perm_iff_count.mpr
        intro row
        have counts := edges.count_eq row
        simp only [treeRows, List.count_cons, List.count_append] at counts ⊢
        omega

theorem insertForest_edges (parent : Origin) (origin : Id) (fresh : Tree) (old next : Forest)
    (ready : NotionCoreOriginTree.DominatesForest origin fresh.item.id old)
    (accepted : NotionCoreOriginTree.insertForest origin fresh old = some next) :
    (forestRows parent next).Perm (forestRows parent old ++ treeRows (.item origin) fresh) := by
  cases old with
  | nil => simp [NotionCoreOriginTree.insertForest] at accepted
  | cons tree rest =>
    cases found : NotionCoreOriginTree.insertTree origin fresh tree with
    | some changed =>
      simp only [NotionCoreOriginTree.insertForest, found, Option.some.injEq] at accepted
      subst next
      have edges := insertTree_edges parent origin fresh tree changed ready.1 found
      apply List.perm_iff_count.mpr
      intro row
      have counts := edges.count_eq row
      simp only [forestRows, List.count_append] at counts ⊢
      omega
    | none =>
      cases tail : NotionCoreOriginTree.insertForest origin fresh rest with
      | none => simp [NotionCoreOriginTree.insertForest, found, tail] at accepted
      | some changed =>
        simp only [NotionCoreOriginTree.insertForest, found, tail,
          Option.map_some, Option.some.injEq] at accepted
        subst next
        have edges := insertForest_edges parent origin fresh rest changed ready.2 tail
        apply List.perm_iff_count.mpr
        intro row
        have counts := edges.count_eq row
        simp only [forestRows, List.count_append] at counts ⊢
        omega
end

/-- Structural parent-edge coupling uses physical records and origin links,
not a traversal equation or a projected document. -/
def ParentEdges (rows : Table) (forest : Forest) : Prop :=
  rows.Perm (forestRows .start forest)

/-- Source fresh-run integration appends literal run rows. The independently
computed recursive tree insertion preserves exact parent-edge coupling.
Identity collision/error handling and allocation freshness remain separate. -/
theorem fresh_run_edges (rows : Table) (old next : Forest) (origin : Id)
    (first : Item) (rest : List Item)
    (coupled : ParentEdges rows old)
    (ready : NotionCoreOriginTree.DominatesForest origin first.id old)
    (accepted : NotionCoreOriginTree.insert (.item origin)
      (NotionCoreOriginTree.runTree first rest) old = some next) :
    ParentEdges (rows ++ runRows (.item origin) (first :: rest)) next := by
  have head : (NotionCoreOriginTree.runTree first rest).item.id = first.id := by
    cases rest <;> rfl
  have edges := insertForest_edges .start origin (NotionCoreOriginTree.runTree first rest)
    old next (head ▸ ready) accepted
  exact (coupled.append_right _).trans (by simpa only [run_rows] using edges.symm)
/-- Includes fresh root runs under the external START sentinel. -/
theorem fresh_run_edges_any (rows : Table) (old next : Forest) (origin : Origin)
    (first : Item) (rest : List Item) (coupled : ParentEdges rows old)
    (ready : NotionCoreOriginTree.Ready origin (NotionCoreOriginTree.runTree first rest) old)
    (accepted : NotionCoreOriginTree.insert origin
      (NotionCoreOriginTree.runTree first rest) old = some next) :
    ParentEdges (rows ++ runRows origin (first :: rest)) next := by
  cases origin with
  | item id =>
    have head : (NotionCoreOriginTree.runTree first rest).item.id = first.id := by cases rest <;> rfl
    exact fresh_run_edges rows old next id first rest coupled (head ▸ ready) accepted
  | start =>
    have firstChild := NotionCoreOriginTree.insertChild_first
      (NotionCoreOriginTree.runTree first rest) old ready
    simp only [NotionCoreOriginTree.insert, firstChild, Option.some.injEq] at accepted
    subst next
    rw [ParentEdges, run_rows]
    exact (coupled.append_right _).trans List.perm_append_comm


def fixture : Table :=
  [⟨NotionCoreOriginTree.literal 1 100, .start⟩,
   ⟨NotionCoreOriginTree.literal 2 97, .start⟩,
   ⟨NotionCoreOriginTree.literal 3 98 true, .item (NotionCoreOriginTree.literal 2 97).id⟩,
   ⟨⟨⟨4, [65]⟩, .split⟩, .item (NotionCoreOriginTree.literal 3 98 true).id⟩,
   ⟨NotionCoreOriginTree.literal 5 99, .item ⟨4, [65]⟩⟩]

/-- PASS+FAIL: actual map child enumeration/sorting traverses through tombstone
and marker origins; output is neither map iteration order nor empty text. -/
theorem physical_parent_control :
    (traverse (maximumCounter fixture) fixture .start).map (fun item => item.id.counter) = [2,3,4,5,1] ∧
    (traverse (maximumCounter fixture) fixture .start).map (fun item => item.id.counter) ≠ [1,2,3,4,5] ∧
    NotionCoreOriginTree.visible (traverse (maximumCounter fixture) fixture .start) = [97,99,100] ∧
    NotionCoreOriginTree.visible (traverse (maximumCounter fixture) fixture .start) ≠ [] := by
  simp [traverse, maximumCounter, fixture, sortedChildren, childIds, lookup,
    NotionCoreOriginTree.literal, NotionCoreOriginTree.visible,
    NotionCoreSourceInvariant.sortChildren, List.mergeSort,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before]

/-- PASS+FAIL: raw integration permits an orphan. START traversal omits it,
which distinguishes the actual source behavior from rejecting its row or
simply echoing every stored item. It lies outside Closed/Reach. -/
theorem orphan_control :
    let orphan : Row := ⟨NotionCoreOriginTree.literal 2 88, .item ⟨1, [65]⟩⟩
    let rows := insertFresh [] orphan
    rows = [orphan] ∧ traverse (maximumCounter rows) rows .start = [] ∧
    traverse (maximumCounter rows) rows .start ≠ [orphan.item] ∧ ¬ Closed rows := by
  simp [insertFresh, traverse, maximumCounter, sortedChildren, childIds, Closed,
    NotionCoreOriginTree.literal, NotionCoreSourceInvariant.sortChildren]

#print axioms extract_model
#print axioms traversal_model
#print axioms extract_raw_model
#print axioms reachable_extraction
#print axioms fresh_run_edges_any

end Sal.MRDTs.Instances.NotionCoreParentMap
