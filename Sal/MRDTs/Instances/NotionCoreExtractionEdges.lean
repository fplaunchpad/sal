import Sal.MRDTs.Instances.NotionCoreReplayGraph

/-! Exact edge reconstruction from raw unique, increasing, closed parent
maps. No extracted-forest uniqueness or output equation is assumed. -/
namespace Sal.MRDTs.Instances.NotionCoreExtractionEdges
open NotionRunAllocation (Id)
open NotionCoreOriginTree (Item Origin Tree Forest)
open NotionCoreParentMap
open NotionCoreParentCoupling

private theorem childIds_sublist (rows : Table) (parent : Origin) :
    (childIds rows parent).Sublist (rows.map (fun row => row.item.id)) := by
  induction rows with
  | nil => exact .slnil
  | cons row rest ih =>
      by_cases same : row.origin = parent
      · simpa [childIds, same] using List.Sublist.cons₂ row.item.id ih
      · simpa [childIds, same] using List.Sublist.cons row.item.id ih

private theorem child_count (rows : Table) (unique : NotionCoreParentMap.Unique rows)
    (row : Row) (present : row ∈ rows) (parent : Origin) :
    (childIds rows parent).count row.item.id = if row.origin = parent then 1 else 0 := by
  have uniqueChildren := (childIds_sublist rows parent).nodup unique
  by_cases same : row.origin = parent
  · rw [if_pos same]
    exact List.count_eq_one_of_mem uniqueChildren
      (List.mem_filterMap.mpr ⟨row, present, by simp [same]⟩)
  · rw [if_neg same]
    apply List.count_eq_zero.mpr
    intro member
    obtain ⟨other, otherMember, found, id, origin⟩ := child_lookup rows parent row.item.id unique member
    have eq : other = row := Option.some.inj (found.symm.trans (lookup_member rows row unique present))
    exact same (eq ▸ origin)

mutual
private theorem tree_count (rows : Table) (unique : NotionCoreParentMap.Unique rows)
    (target : Row) (present : target ∈ rows) (parent : Origin) (tree : Tree)
    (model : TreeModel rows parent tree) :
    (treeIds tree).count target.item.id =
      (if tree.item.id = target.item.id then 1 else 0) +
      match target.origin with
      | .start => 0
      | .item id => (treeIds tree).count id := by
  cases tree with
  | node item children =>
      cases model with
      | node found childModel =>
        have equation := forest_count rows unique target present (.item item.id) children childModel
        cases targetOrigin : target.origin with
        | start =>
            simp only [targetOrigin, reduceCtorEq, if_false] at equation
            simp [treeIds_node, List.count_cons, equation, Tree.item, beq_iff_eq, Nat.add_comm]
        | item id =>
            simp only [targetOrigin, Origin.item.injEq] at equation
            simp only [treeIds_node, List.count_cons, beq_iff_eq, Tree.item]
            rw [equation]
            by_cases same : id = item.id <;> simp [same, eq_comm, Nat.add_comm, Nat.add_left_comm]
termination_by (sizeOf tree, 0)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.left; omega
private theorem trees_count (rows : Table) (unique : NotionCoreParentMap.Unique rows)
    (target : Row) (present : target ∈ rows) (parent : Origin) (forest : Forest)
    (model : TreesModel rows parent forest) :
    (forestIds forest).count target.item.id = forest.roots.count target.item.id +
      match target.origin with
      | .start => 0
      | .item id => (forestIds forest).count id := by
  cases forest with
  | nil => cases target.origin <;> simp [Forest.roots]
  | cons tree rest =>
      cases model with
      | cons head tail =>
        have first := tree_count rows unique target present parent tree head
        have later := trees_count rows unique target present parent rest tail
        simp only [forestIds_cons, List.count_append, Forest.roots, List.count_cons, beq_iff_eq]
        rw [first, later]
        cases target.origin <;> simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
termination_by (sizeOf forest, 0)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.left; omega
private theorem forest_count (rows : Table) (unique : NotionCoreParentMap.Unique rows)
    (target : Row) (present : target ∈ rows) (parent : Origin) (forest : Forest)
    (model : ForestModel rows parent forest) :
    (forestIds forest).count target.item.id = (if target.origin = parent then 1 else 0) +
      match target.origin with
      | .start => 0
      | .item id => (forestIds forest).count id := by
  cases model with
  | model adjacency ordered models =>
      rw [trees_count rows unique target present parent forest models,
        ← adjacency.count_eq, child_count rows unique target present parent]
termination_by (sizeOf forest, 1)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.right; omega
end

/-- Multiplicity follows the unique parent backwards. Strict counter rank
terminates that descent; closed maps end at START rather than an orphan. -/
theorem model_ids_unique (rows : Table) (unique : NotionCoreParentMap.Unique rows)
    (increasing : Increasing rows) (closed : Closed rows) (forest : Forest)
    (model : ForestModel rows .start forest) : (forestIds forest).Nodup := by
  have counts : ∀ counter, ∀ row ∈ rows, row.item.id.counter = counter →
      (forestIds forest).count row.item.id ≤ 1 := by
    intro counter
    induction counter using Nat.strong_induction_on with
    | h counter ih =>
      intro row member same
      have equation := forest_count rows unique row member .start forest model
      cases parent : row.origin with
      | start => simpa [parent] using equation.le
      | item old =>
          have known := closed row member
          rw [parent] at known
          obtain ⟨provider, present, id⟩ := List.mem_map.mp known
          have rank := increasing row member
          rw [parent] at rank
          have less : provider.item.id.counter < counter := by
            simpa [originCounter, id, same] using rank
          have bound := ih provider.item.id.counter less provider present rfl
          rw [equation, parent]
          simpa [id] using bound
  apply List.nodup_iff_count_le_one.mpr
  intro id
  by_cases present : id ∈ forestIds forest
  · cases model with
    | model adjacency ordered trees =>
      obtain ⟨item, member, equal⟩ := List.mem_map.mp present
      have covered := trees_covered rows .start forest trees item member
      obtain ⟨row, memberRow, same⟩ := List.mem_map.mp covered
      have eq : row.item.id = id := same.trans equal
      simpa [eq] using counts row.item.id.counter row memberRow rfl
  · rw [List.count_eq_zero.mpr present]; omega

mutual
theorem tree_rows_member (rows : Table) (parent : Origin) (tree : Tree)
    (model : TreeModel rows parent tree) : ∀ row ∈ treeRows parent tree, row ∈ rows := by
  cases tree with
  | node item children =>
      cases model with
      | node found childrenModel =>
          intro row member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_of_find?_eq_some found
          · cases childrenModel with
            | model adjacency ordered models => exact forest_rows_member rows (.item item.id) children models row member
theorem forest_rows_member (rows : Table) (parent : Origin) (forest : Forest)
    (models : TreesModel rows parent forest) : ∀ row ∈ forestRows parent forest, row ∈ rows := by
  cases forest with
  | nil => simp [forestRows]
  | cons tree rest =>
      cases models with
      | cons head tail =>
          intro row member
          rcases List.mem_append.mp member with first | later
          · exact tree_rows_member rows parent tree head row first
          · exact forest_rows_member rows parent rest tail row later
end

/-- The actual raw extraction reconstructs every parent row exactly once.
Neither extracted ID uniqueness nor an edge-coupling equation is a premise. -/
theorem extraction_edges (rows : Table) (unique : NotionCoreParentMap.Unique rows)
    (increasing : Increasing rows) (closed : Closed rows) :
    ParentEdges rows (extract (maximumCounter rows) rows .start) := by
  let forest := extract (maximumCounter rows) rows .start
  have model : ForestModel rows .start forest := extract_raw_model rows unique increasing
  have idsUnique := model_ids_unique rows unique increasing closed forest model
  have forestUnique : (forestRows .start forest).Nodup :=
    List.Nodup.of_map (fun row => row.item.id) (by rw [forestRows_ids]; exact idsUnique)
  apply (List.perm_ext_iff_of_nodup (List.Nodup.of_map _ unique) forestUnique).mpr
  intro row
  have models : TreesModel rows .start forest := by cases model; assumption
  constructor
  · intro present
    have covered := extraction_covers_rows rows unique increasing closed row present
    change row.item.id ∈ forestIds forest at covered
    rw [← forestRows_ids .start forest] at covered
    obtain ⟨other, member, id⟩ := List.mem_map.mp covered
    have inTable := forest_rows_member rows .start forest models other member
    have found : lookup rows row.item.id = some other := by
      simpa [id] using lookup_member rows other unique inTable
    have equal : other = row := Option.some.inj
      (found.symm.trans (lookup_member rows row unique present))
    exact equal ▸ member
  · exact forest_rows_member rows .start forest models row


/-- Canonical prefix extraction has exact edges derived from issuance. -/
theorem prefix_extraction_edges {state : NotionCorePayloadNetwork.State}
    (reachable : NotionCorePayloadNetwork.Reach state) (peer : NotionRunAllocation.Session)
    (pre suffix : List NotionRunAllocation.Run)
    (prefixEq : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      (state.allocation.peers peer).received = pre ++ suffix)
    (inst : NotionCorePayload.BlockKey) (deleted : NotionCorePayload.BlockKey → Id → Bool) :
    let rows := NotionCorePayloadParents.prefixRows state.entries pre inst deleted
    ParentEdges rows (extract (maximumCounter rows) rows .start) := by
  obtain ⟨unique, increasing, closed⟩ :=
    NotionCoreReplayGraph.prefix_graph reachable peer pre suffix prefixEq inst deleted
  exact extraction_edges _ unique increasing closed

/-- Actual prefix extraction supplies insertion readiness without a caller's
forest or coupling assumption. Fresh-run identity still comes from decoding. -/
theorem prefix_extraction_ready {state : NotionCorePayloadNetwork.State}
    (reachable : NotionCorePayloadNetwork.Reach state) (peer : NotionRunAllocation.Session)
    {entry : NotionCorePayloadNetwork.Entry} (member : entry ∈ state.entries)
    (pre suffix : List NotionRunAllocation.Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      (state.allocation.peers peer).received = pre ++ NotionCorePayload.reservation entry.tx :: suffix)
    (inst : NotionCorePayload.BlockKey) (deleted : NotionCorePayload.BlockKey → Id → Bool)
    (fresh : Tree) (first : fresh.item.id = entry.tx.id) :
    let rows := NotionCorePayloadParents.prefixRows state.entries pre inst deleted
    NotionCoreOriginTree.Ready (NotionCorePayloadParents.payloadOrigin entry.tx.payload) fresh
      (extract (maximumCounter rows) rows .start) := by
  apply NotionCorePayloadParents.prefix_ready reachable peer member pre suffix position inst deleted _ fresh first
  exact prefix_extraction_edges reachable peer pre (NotionCorePayload.reservation entry.tx :: suffix) position inst deleted

/-- PASS+FAIL: extraction preserves the hidden physical parent and marker,
while actual sibling sorting differs from archive enumeration. -/
theorem extracted_rows_control :
    (forestRows .start (extract (maximumCounter fixture) fixture .start)).map (fun row => row.item.id.counter) =
      [2,3,4,5,1] ∧
    (forestRows .start (extract (maximumCounter fixture) fixture .start)).map (fun row => row.item.id.counter) ≠
      [1,2,3,4,5] := by
  simp [extract, buildForest, maximumCounter, fixture, sortedChildren, childIds, lookup,
    forestRows, treeRows, NotionCoreOriginTree.literal,
    NotionCoreSourceInvariant.sortChildren, List.mergeSort,
    NotionCoreSourceInvariant.Desc, NotionRunAllocation.Before]

/-- PASS+FAIL: an orphan is physically stored but omitted by raw extraction;
Closed is essential to exact edge reconstruction. -/
theorem orphan_boundary_control :
    let orphan : Table := [⟨NotionCoreOriginTree.literal 2 97, .item ⟨1,[65]⟩⟩]
    forestRows .start (extract 2 orphan .start) = [] ∧
    forestRows .start (extract 2 orphan .start) ≠ orphan := by
  simp [extract, buildForest, sortedChildren, childIds, forestRows,
    NotionCoreOriginTree.literal, NotionCoreSourceInvariant.sortChildren]

#print axioms extraction_edges
#print axioms prefix_extraction_ready
end Sal.MRDTs.Instances.NotionCoreExtractionEdges
