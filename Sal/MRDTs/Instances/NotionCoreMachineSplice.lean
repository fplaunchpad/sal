import Sal.MRDTs.Instances.NotionCoreMachineTables
import Sal.MRDTs.Instances.NotionCoreParentCoupling
import Sal.MRDTs.Instances.NotionCorePhysicalReplay

/-! Actual machine row integration to physical endpoint splice. The old
parent-edge tree is structural input; neither insertion success nor a chosen
next physical observation is a premise. Canonical provenance and interval
partition preservation are separate compositions. -/
set_option maxHeartbeats 2000000
namespace Sal.MRDTs.Instances.NotionCoreMachineSplice
open NotionRunAllocation (Id)
open NotionCoreOriginTree (Item Origin Tree Forest)
open NotionCoreParentMap (Row Table runRows ParentEdges)
open NotionCoreParentCoupling (OrderedForest)
open NotionCoreMachine

private def Outside (origin : Origin) (ids : List Id) : Prop := match origin with
  | .start => True
  | .item id => id ∉ ids

private theorem runRows_nonself (origin : Origin) (items : List Item)
    (unique : (items.map Item.id).Nodup) (outside : Outside origin (items.map Item.id)) :
    ∀ row ∈ runRows origin items, row.origin ≠ .item row.item.id := by
  induction items generalizing origin with
  | nil => simp [runRows]
  | cons first rest ih =>
    intro row member
    rcases List.mem_cons.mp member with rfl | tail
    · cases origin with
      | start => simp
      | item id =>
        intro same
        have equal : id = first.id := Origin.item.inj same
        exact outside (List.mem_cons.mpr (Or.inl equal))
    · exact ih (.item first.id) (List.nodup_cons.mp unique).2 (List.nodup_cons.mp unique).1 row tail

private theorem run_origin_outside (rows : Table) (forest : Forest) (origin : Origin)
    (items : List Item) (coupled : ParentEdges rows forest)
    (apart : List.Disjoint (rows.map (fun row => row.item.id)) (items.map Item.id))
    (present : NotionCorePhysicalReplay.Present origin forest) : Outside origin (items.map Item.id) := by
  cases origin with
  | start => trivial
  | item id =>
      intro new
      change id ∈ NotionCoreParentCoupling.forestIds forest at present
      rw [← NotionCoreParentCoupling.forestRows_ids .start forest] at present
      have old := (coupled.map (fun row => row.item.id)).mem_iff.mpr present
      exact List.disjoint_left.mp apart old new

/-- The checked integration loop accepts and appends a fresh physical run.
Its no-self-origin checks follow from actual origin presence and fresh IDs. -/
theorem integrate_run_success (state : State) (inst : Nat) (origin : Origin)
    (first : Item) (rest : List Item) (forest : Forest)
    (coupled : ParentEdges (getInstance state inst).rows forest)
    (newUnique : ((first :: rest).map Item.id).Nodup)
    (apart : List.Disjoint ((getInstance state inst).rows.map (fun row => row.item.id)) ((first :: rest).map Item.id))
    (present : NotionCorePhysicalReplay.Present origin forest) :
    integrateRows (getInstance state inst).rows (runRows origin (first :: rest)) =
      some ((getInstance state inst).rows ++ runRows origin (first :: rest)) := by
  apply NotionCoreMachineRows.integrateRows_fresh
  · simpa only [NotionCoreParentMap.Unique,NotionCoreParentCoupling.runRows_ids] using newUnique
  · simpa only [NotionCoreParentCoupling.runRows_ids] using apart
  · exact runRows_nonself origin (first :: rest) newUnique
      (run_origin_outside _ forest origin (first :: rest) coupled apart present)

/-- Exact actual physical splice after checked row integration and putInstance.
The next origin tree and its successful insertion are derived, not supplied. -/
theorem integrate_run_physical (state : State) (inst : Nat) (origin : Origin)
    (first : Item) (rest : List Item) (forest : Forest)
    (coupled : ParentEdges (getInstance state inst).rows forest)
    (unique : NotionCoreParentMap.Unique (getInstance state inst).rows)
    (ordered : OrderedForest forest)
    (newUnique : ((first :: rest).map Item.id).Nodup)
    (apart : List.Disjoint ((getInstance state inst).rows.map (fun row => row.item.id)) ((first :: rest).map Item.id))
    (ready : NotionCoreOriginTree.Ready origin (NotionCoreOriginTree.runTree first rest) forest)
    (present : NotionCorePhysicalReplay.Present origin forest) :
    ∃ rows, integrateRows (getInstance state inst).rows (runRows origin (first :: rest)) = some rows ∧
      physical (putInstance state inst {getInstance state inst with rows := rows}) inst =
        NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
          (NotionCorePhysicalReplay.originAddress inst origin)
          ((first :: rest).map (NotionCorePhysicalReplay.atom inst)) (physical state inst) := by
  have treePhysical := NotionCorePhysicalReplay.tree_insert_physical inst origin
    (NotionCoreOriginTree.runTree first rest) forest ready present
  obtain ⟨next,inserted,nextPhysical⟩ := Option.map_eq_some_iff.mp treePhysical
  have nextTraversal := (NotionCoreParentCoupling.appended_run_traversal
    (getInstance state inst).rows forest next origin first rest coupled unique ordered newUnique apart ready inserted).2
  have oldTraversal := NotionCoreParentCoupling.edges_traversal _ forest coupled unique ordered
  have oldPhysical : physical state inst = NotionCorePhysicalReplay.augmented inst forest := by
    simp only [physical,traversal_correct,oldTraversal,NotionCorePhysicalReplay.augmented]
  refine ⟨(getInstance state inst).rows ++ runRows origin (first :: rest),
    integrate_run_success state inst origin first rest forest coupled newUnique apart present,?_⟩
  rw [physical,NotionCoreMachineTables.getInstance_put]
  simp only [if_true,traversal_correct]
  rw [nextTraversal]
  change NotionCorePhysicalReplay.augmented inst next = _
  rw [oldPhysical]
  simpa only [NotionCoreOriginTree.runTree_preorder] using nextPhysical

/-- Singleton source split-marker integration is the same proved raw splice.
Tree splitting and detach/move follow this physical insertion in the source. -/
theorem integrate_marker_physical (state : State) (inst : Nat) (origin : Origin)
    (id : Id) (forest : Forest)
    (coupled : ParentEdges (getInstance state inst).rows forest)
    (unique : NotionCoreParentMap.Unique (getInstance state inst).rows)
    (ordered : OrderedForest forest)
    (fresh : id ∉ (getInstance state inst).rows.map (fun row => row.item.id))
    (ready : NotionCoreOriginTree.Ready origin (.node ⟨id,.split⟩ .nil) forest)
    (present : NotionCorePhysicalReplay.Present origin forest) :
    ∃ rows, integrate (getInstance state inst).rows ⟨⟨id,.split⟩,origin⟩ = some rows ∧
      physical (putInstance state inst {getInstance state inst with rows := rows}) inst =
        NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
          (NotionCorePhysicalReplay.originAddress inst origin)
          [NotionCorePhysicalReplay.atom inst ⟨id,.split⟩] (physical state inst) := by
  have apart : List.Disjoint ((getInstance state inst).rows.map (fun row => row.item.id)) [id] :=
    List.disjoint_left.mpr (by intro old member selected; simp only [List.mem_singleton] at selected; subst old; exact fresh member)
  obtain ⟨rows,integrated,physicalEq⟩ := integrate_run_physical state inst origin ⟨id,.split⟩ [] forest
    coupled unique ordered (by simp) apart ready present
  refine ⟨rows,?_,physicalEq⟩
  simpa [integrateRows,runRows] using integrated

theorem textItems_head_id (firstId : Id) (atoms : List Nat) (deleted : Id → Bool)
    (first : Item) (rest : List Item)
    (decoded : NotionCorePayload.textItems firstId atoms deleted = first :: rest) : first.id = firstId := by
  have ids := NotionCorePayload.textItems_ids firstId atoms deleted
  rw [decoded,List.map_cons] at ids
  cases atoms with
  | nil => simp [NotionCorePayload.textItems] at decoded
  | cons value tail =>
      simp only [List.length_cons,List.range_succ_eq_map,List.map_cons] at ids
      simpa [NotionCorePayload.offsetId] using (List.cons.inj ids).1

theorem textItems_nonempty (firstId : Id) (atoms : List Nat) (deleted : Id → Bool)
    (nonempty : atoms ≠ []) : NotionCorePayload.textItems firstId atoms deleted ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  simp [NotionCorePayload.textItems] at length
  exact nonempty (by simpa using length)

/-- Actual nonempty text-payload dispatch succeeds and has the proved splice.
`decoded` identifies the payload's literal allocated run, including pending
birth tombstones; it is not an output-state or rendered-value equation. -/
theorem insert_text_physical (state : State) (block inst : NotionCorePayload.BlockKey)
    (firstId : Id) (origin : Origin) (atoms : List Nat) (first : Item) (rest : List Item)
    (decoded : NotionCorePayload.textItems firstId atoms
      (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)) = first :: rest)
    (forest : Forest) (coupled : ParentEdges (getInstance state (blockName inst)).rows forest)
    (unique : NotionCoreParentMap.Unique (getInstance state (blockName inst)).rows)
    (ordered : OrderedForest forest) (newUnique : ((first :: rest).map Item.id).Nodup)
    (apart : List.Disjoint ((getInstance state (blockName inst)).rows.map (fun row => row.item.id)) ((first :: rest).map Item.id))
    (ready : NotionCoreOriginTree.Ready origin (NotionCoreOriginTree.runTree first rest) forest)
    (present : NotionCorePhysicalReplay.Present origin forest) :
    ∃ next, applyOperation state (.insert block inst firstId origin atoms) = some next ∧
      physical next (blockName inst) = NotionCorePartition.spliceAfterBy NotionCoreSource.Atom.address
        (NotionCorePhysicalReplay.originAddress (blockName inst) origin)
        ((first :: rest).map (NotionCorePhysicalReplay.atom (blockName inst))) (physical state (blockName inst)) := by
  obtain ⟨rows,integrated,physicalEq⟩ := integrate_run_physical state (blockName inst) origin first rest forest
    coupled unique ordered newUnique apart ready present
  refine ⟨putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows},?_,physicalEq⟩
  simp [applyOperation,decoded,integrated]

mutual
private theorem ordered_tree_model (rows : Table) (parent : Origin) (tree : Tree)
    (model : NotionCoreParentMap.TreeModel rows parent tree) : NotionCoreParentCoupling.OrderedTree tree := by
  cases tree with
  | node item children =>
    cases model with
    | node found childModel => exact ordered_forest_model rows (.item item.id) children childModel
termination_by (sizeOf tree,0)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.left; omega
private theorem ordered_trees_model (rows : Table) (parent : Origin) (forest : Forest)
    (models : NotionCoreParentMap.TreesModel rows parent forest)
    (ordered : forest.roots.Pairwise NotionCoreSourceInvariant.Desc) : OrderedForest forest := by
  cases forest with
  | nil => trivial
  | cons tree rest =>
    cases models with
    | cons head tail =>
      exact ⟨ordered,ordered_tree_model rows parent tree head,
        ordered_trees_model rows parent rest tail (List.pairwise_cons.mp ordered).2⟩
termination_by (sizeOf forest,0)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.left; omega
theorem ordered_forest_model (rows : Table) (parent : Origin) (forest : Forest)
    (model : NotionCoreParentMap.ForestModel rows parent forest) : OrderedForest forest := by
  cases model with
  | model adjacency ordered trees => exact ordered_trees_model rows parent forest trees ordered
termination_by (sizeOf forest,1)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.right; omega
end

theorem extraction_ordered (rows : Table) (unique : NotionCoreParentMap.Unique rows)
    (increasing : NotionCoreParentMap.Increasing rows) :
    OrderedForest (NotionCoreParentMap.extract (NotionCoreParentMap.maximumCounter rows) rows .start) :=
  ordered_forest_model rows .start _ (NotionCoreParentMap.extract_raw_model rows unique increasing)

private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[65]⟩
private def x : Id := ⟨3,[66]⟩
private def y : Id := ⟨4,[66]⟩
private def old : State :=
  ⟨[(0,⟨[⟨⟨a,.text 97 true⟩,.start⟩,⟨⟨b,.text 98 false⟩,.item a⟩],[a,y]⟩)],
    [⟨0,NotionCoreSliceForest.freshTitle 0⟩],[0]⟩
private def expectedText : List NotionCoreSource.Atom :=
  [NotionCorePhysicalReplay.start 0,NotionCorePhysicalReplay.atom 0 ⟨a,.text 97 true⟩,
   NotionCorePhysicalReplay.atom 0 ⟨x,.text 88 false⟩,NotionCorePhysicalReplay.atom 0 ⟨y,.text 89 true⟩,
   NotionCorePhysicalReplay.atom 0 ⟨b,.text 98 false⟩]

/-- PASS+FAIL: actual text dispatch splices after the hidden parent, before
its existing child; pending deletion hides the second new atom. -/
theorem text_splice_control :
    (applyOperation old (.insert .initial .initial x (.item a) [88,89])).map
      (fun next => physical next 0) = some expectedText ∧
    (applyOperation old (.insert .initial .initial x (.item a) [88,89])).map
      (fun next => physical next 0) ≠ some (physical old 0) := by decide

/-- PASS+FAIL: literal singleton-marker integration uses the same physical
position and keeps the hidden parent and its old live child. -/
theorem marker_splice_control :
    let updated := putInstance old 0
      {getInstance old 0 with rows := (getInstance old 0).rows ++ [⟨⟨x,.split⟩,.item a⟩]}
    integrate (getInstance old 0).rows ⟨⟨x,.split⟩,.item a⟩ =
      some ((getInstance old 0).rows ++ [⟨⟨x,.split⟩,.item a⟩]) ∧
    physical updated 0 = [NotionCorePhysicalReplay.start 0,
      NotionCorePhysicalReplay.atom 0 ⟨a,.text 97 true⟩,
      NotionCorePhysicalReplay.atom 0 ⟨x,.split⟩,
      NotionCorePhysicalReplay.atom 0 ⟨b,.text 98 false⟩] ∧
    physical updated 0 ≠ [NotionCorePhysicalReplay.start 0,NotionCorePhysicalReplay.atom 0 ⟨x,.split⟩] := by decide

#print axioms integrate_run_physical
#print axioms integrate_marker_physical
#print axioms insert_text_physical
#print axioms extraction_ordered
end Sal.MRDTs.Instances.NotionCoreMachineSplice
