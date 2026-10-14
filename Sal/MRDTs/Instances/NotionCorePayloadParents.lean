import Sal.MRDTs.Instances.NotionCorePayloadNetwork
import Sal.MRDTs.Instances.NotionCoreParentCoupling

/-! Derive child dominance from actual typed payload parent links.
The falsifier is an old child whose source ID sorts above the next insertion.
Internal run children require the observed whole-provider clock bound, not
merely transaction-first replay ordering. No child classification is supplied
by the caller: it follows from the expanded payload's literal runRows.
-/
namespace Sal.MRDTs.Instances.NotionCorePayloadParents
open NotionRunAllocation (Id Run Before)
open NotionCoreOriginTree (Origin Item Kind Tree Forest)
open NotionCoreParentMap (Row Table)
open NotionCorePayload
open NotionCorePayloadNetwork (Entry)

def payloadOrigin : Payload → Origin
  | .insert _ _ origin _ | .split _ _ origin => origin
  | .bootstrap _ | .create _ | .erase _ _ _ => .start

def parentAt (first : Id) (origin : Origin) (offset : Nat) : Origin :=
  if offset = 0 then origin else .item (offsetId first (offset - 1))

theorem range_row_parent (first : Id) (origin : Origin) (kind : Nat → Kind)
    (count lower : Nat) (row : Row)
    (member : row ∈ NotionCoreParentMap.runRows (parentAt first origin lower)
      ((List.range' lower count).map fun index => (⟨offsetId first index, kind index⟩ : Item))) :
    ∃ offset, lower ≤ offset ∧ offset < lower + count ∧
      row.item.id = offsetId first offset ∧ row.origin = parentAt first origin offset := by
  induction count generalizing lower with
  | zero => simp [List.range', NotionCoreParentMap.runRows] at member
  | succ count ih =>
    simp only [List.range'_succ, List.map_cons, NotionCoreParentMap.runRows, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨lower, le_rfl, by omega, rfl, rfl⟩
    · have member' : row ∈ NotionCoreParentMap.runRows (parentAt first origin (lower + 1))
          ((List.range' (lower + 1) count).map fun index => (⟨offsetId first index, kind index⟩ : Item)) := by
        simpa [parentAt] using member
      obtain ⟨offset, above, within, id, parent⟩ := ih (lower + 1) member'
      exact ⟨offset, by omega, by omega, id, parent⟩

theorem text_row_parent (first : Id) (origin : Origin) (atoms : List Nat) (deleted : Id → Bool)
    (row : Row) (member : row ∈ NotionCoreParentMap.runRows origin (textItems first atoms deleted)) :
    ∃ offset, offset < atoms.length ∧ row.item.id = offsetId first offset ∧
      row.origin = parentAt first origin offset := by
  have member' : row ∈ NotionCoreParentMap.runRows (parentAt first origin 0)
      ((List.range' 0 atoms.length).map fun index =>
        (⟨offsetId first index, .text atoms[index]! (deleted (offsetId first index))⟩ : Item)) := by
    simpa [textItems, parentAt, List.range_eq_range'] using member
  obtain ⟨offset, _, within, id, parent⟩ := range_row_parent first origin _ atoms.length 0 row member'
  exact ⟨offset, by simpa using within, id, parent⟩

/-- Every generated parent row has either the payload's external origin or
the preceding ID of that same run. Metadata phases produce no such row. -/
theorem birth_parent (tx : Transaction) (deleted : BlockKey → Id → Bool)
    (birth : Birth) (member : birth ∈ births tx deleted) :
    ∃ offset, offset < tx.payload.itemCount ∧ birth.2.item.id = offsetId tx.id offset ∧
      birth.2.origin = parentAt tx.id (payloadOrigin tx.payload) offset := by
  cases tx with
  | mk id payload =>
    cases payload with
    | bootstrap atoms =>
      simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_nil, List.mem_map] at member
      obtain ⟨row, present, rfl⟩ := member
      exact text_row_parent id .start atoms _ row present
    | insert block inst origin atoms =>
      simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_map] at member
      obtain ⟨row, present, rfl⟩ := member
      exact text_row_parent id origin atoms _ row present
    | split block inst origin =>
      simp only [births, operations, Operation.births, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_nil, List.mem_singleton] at member
      subst birth
      exact ⟨0, by simp [Payload.itemCount], by simp [offsetId], by simp [parentAt, payloadOrigin]⟩
    | create afterBlock => simp [births, operations, Operation.births] at member
    | erase block inst targets => simp [births, operations, Operation.births] at member

theorem external_reference (payload : Payload) (id : Id) (origin : payloadOrigin payload = .item id) :
    id ∈ payload.references := by
  cases payload <;> simp_all [payloadOrigin, Payload.references, originReference]

/-- The complete provider width, rather than a transaction-global maximum,
places every existing child before the new first item. Parent relationships
are extracted from the actual old payload's births. -/
theorem replay_child_before_version {state : NotionCorePayloadNetwork.State}
    (reachable : NotionCorePayloadNetwork.Reach state) (version : List Run)
    {entry old : Entry} (member : entry ∈ state.entries) (oldMember : old ∈ state.entries)
    (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      version = pre ++ reservation entry.tx :: suffix)
    (earlier : reservation old.tx ∈ pre)
    (deleted : BlockKey → Id → Bool) (birth : Birth) (born : birth ∈ births old.tx deleted)
    (parent : birth.2.origin = payloadOrigin entry.tx.payload) :
    Before birth.2.item.id entry.tx.id := by
  obtain ⟨offset, within, id, origin⟩ := birth_parent old.tx deleted birth born
  have reachable' := NotionCorePayloadNetwork.forget_reachable reachable
  have member' : entry.record ∈ (NotionCorePayloadNetwork.forget state).records :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  have oldMember' : old.record ∈ (NotionCorePayloadNetwork.forget state).records :=
    List.mem_map.mpr ⟨old, oldMember, rfl⟩
  have published := NotionCoreIssuance.record_published reachable' oldMember'
  have within' : offset < (reservation old.tx).length := by
    simp only [reservation, Payload.width]
    omega
  have reference : 0 < offset → (reservation old.tx).at (offset - 1) ∈ entry.record.references := by
    intro positive
    have eq : payloadOrigin entry.tx.payload = .item (offsetId old.tx.id (offset - 1)) := by
      rw [← parent, origin, parentAt, if_neg (by omega)]
    exact external_reference entry.tx.payload _ eq
  have before := NotionCoreIssuance.replay_child_dominance reachable' member' pre suffix
    (position ▸ NotionCoreIssuance.replay_ordered reachable' _) earlier published within' reference
  simpa only [id, reservation, Run.at, offsetId, NotionCorePayloadNetwork.Entry.record, record] using before

theorem replay_child_before {state : NotionCorePayloadNetwork.State}
    (reachable : NotionCorePayloadNetwork.Reach state) (peer : NotionRunAllocation.Session)
    {entry old : Entry} (member : entry ∈ state.entries) (oldMember : old ∈ state.entries)
    (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      (state.allocation.peers peer).received = pre ++ reservation entry.tx :: suffix)
    (earlier : reservation old.tx ∈ pre)
    (deleted : BlockKey → Id → Bool) (birth : Birth) (born : birth ∈ births old.tx deleted)
    (parent : birth.2.origin = payloadOrigin entry.tx.payload) :
    Before birth.2.item.id entry.tx.id :=
  replay_child_before_version reachable _ member oldMember pre suffix position earlier deleted birth born parent

/-- A finite table view of the prefix's actual typed births, restricted to
one instance. Archive enumeration need not be replay order: child traversal
sorts by source IDs. Tombstones may vary with the replay's pending-delete set. -/
def prefixRows (entries : List Entry) (pre : List Run) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) : Table :=
  (entries.filter (fun entry => reservation entry.tx ∈ pre)).flatMap fun entry =>
    (births entry.tx deleted).filterMap fun birth => if birth.1 = inst then some birth.2 else none

theorem prefix_row_member (entries : List Entry) (pre : List Run) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) (row : Row) :
    row ∈ prefixRows entries pre inst deleted ↔
      ∃ entry ∈ entries, reservation entry.tx ∈ pre ∧ (inst, row) ∈ births entry.tx deleted := by
  simp only [prefixRows, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
    List.mem_filterMap]
  constructor
  · rintro ⟨entry, ⟨present, earlier⟩, birth, born, selected⟩
    split at selected
    · rename_i same
      have rowEq := Option.some.inj selected
      have pair : birth = (inst, row) := Prod.ext same rowEq
      exact ⟨entry, present, earlier, pair ▸ born⟩
    · contradiction
  · rintro ⟨entry, present, earlier, born⟩
    exact ⟨entry, ⟨present, earlier⟩, (inst, row), born, by simp⟩

theorem root_edge (parent : Origin) (forest : Forest) (id : Id) (member : id ∈ forest.roots) :
    ∃ row ∈ NotionCoreParentMap.forestRows parent forest, row.item.id = id ∧ row.origin = parent := by
  cases forest with
  | nil => simp [Forest.roots] at member
  | cons tree rest =>
    rcases List.mem_cons.mp member with rfl | member
    · cases tree with
      | node item children =>
        exact ⟨⟨item, parent⟩, by simp [NotionCoreParentMap.forestRows, NotionCoreParentMap.treeRows], rfl, rfl⟩
    · obtain ⟨row, present, same, origin⟩ := root_edge parent rest id member
      exact ⟨row, List.mem_append_right _ present, same, origin⟩

mutual
theorem tree_dominates_of_edges (target fresh : Id) (parent : Origin) (tree : Tree)
    (dominated : ∀ row ∈ NotionCoreParentMap.treeRows parent tree,
      row.origin = .item target → Before row.item.id fresh) :
    NotionCoreOriginTree.DominatesTree target fresh tree := by
  cases tree with
  | node item children =>
    constructor
    · intro same child present
      obtain ⟨row, member, id, origin⟩ := root_edge (.item item.id) children child present
      rw [← id]
      exact dominated row (List.mem_cons_of_mem _ member) (by simpa [same] using origin)
    · exact forest_dominates_of_edges target fresh (.item item.id) children
        (fun row member origin => dominated row (List.mem_cons_of_mem _ member) origin)
theorem forest_dominates_of_edges (target fresh : Id) (parent : Origin) (forest : Forest)
    (dominated : ∀ row ∈ NotionCoreParentMap.forestRows parent forest,
      row.origin = .item target → Before row.item.id fresh) :
    NotionCoreOriginTree.DominatesForest target fresh forest := by
  cases forest with
  | nil => trivial
  | cons tree rest =>
    exact ⟨tree_dominates_of_edges target fresh parent tree
      (fun row member origin => dominated row (List.mem_append_left _ member) origin),
      forest_dominates_of_edges target fresh parent rest
      (fun row member origin => dominated row (List.mem_append_right _ member) origin)⟩
end

/-- The insertion readiness predicate is derived for the actual prefix table
and an edge-coupled tree. Internal-child provenance is not an extra assumption. -/
theorem prefix_ready_version {state : NotionCorePayloadNetwork.State}
    (reachable : NotionCorePayloadNetwork.Reach state) (version : List Run)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      version = pre ++ reservation entry.tx :: suffix)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) (forest : Forest) (fresh : Tree)
    (first : fresh.item.id = entry.tx.id)
    (coupled : NotionCoreParentMap.ParentEdges (prefixRows state.entries pre inst deleted) forest) :
    NotionCoreOriginTree.Ready (payloadOrigin entry.tx.payload) fresh forest := by
  have children : ∀ row ∈ NotionCoreParentMap.forestRows .start forest,
      row.origin = payloadOrigin entry.tx.payload → Before row.item.id fresh.item.id := by
    intro row inside parent
    have raw := coupled.mem_iff.mpr inside
    obtain ⟨old, oldMember, earlier, born⟩ := (prefix_row_member _ _ _ _ _).mp raw
    rw [first]
    exact replay_child_before_version reachable version member oldMember pre suffix position earlier deleted
      (inst, row) born parent
  cases originEq : payloadOrigin entry.tx.payload with
  | start =>
    intro child present
    obtain ⟨row, inside, id, origin⟩ := root_edge .start forest child present
    rw [← id]
    exact children row inside (origin.trans originEq.symm)
  | item target =>
    exact forest_dominates_of_edges target fresh.item.id .start forest
      (fun row inside origin => children row inside (origin.trans originEq.symm))

theorem prefix_ready {state : NotionCorePayloadNetwork.State}
    (reachable : NotionCorePayloadNetwork.Reach state) (peer : NotionRunAllocation.Session)
    {entry : Entry} (member : entry ∈ state.entries) (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget state)
      (state.allocation.peers peer).received = pre ++ reservation entry.tx :: suffix)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) (forest : Forest) (fresh : Tree)
    (first : fresh.item.id = entry.tx.id)
    (coupled : NotionCoreParentMap.ParentEdges (prefixRows state.entries pre inst deleted) forest) :
    NotionCoreOriginTree.Ready (payloadOrigin entry.tx.payload) fresh forest :=
  prefix_ready_version reachable _ member pre suffix position inst deleted forest fresh first coupled

private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[65]⟩
private def x : Id := ⟨3,[66]⟩
private def twoAtoms : Transaction := bootstrap [97,98]
private def splitTx : Transaction := ⟨x, .split .initial .initial (.item a)⟩

/-- PASS+FAIL: the second atom points to the first atom, not to the payload's
external START origin. That distinction drives internal-child clock bounds. -/
theorem internal_parent_control :
    (births twoAtoms (fun _ _ => false)).map (fun birth => (birth.2.item.id, birth.2.origin)) =
      [(a, .start), (b, .item a)] ∧
    (births twoAtoms (fun _ _ => false)).map (fun birth => (birth.2.item.id, birth.2.origin)) ≠
      [(a, .start), (b, .start)] := by decide

/-- Split creates one marker with the selected external origin; its metadata
create and move phases produce no extra parent row. -/
theorem split_parent_control :
    (births splitTx (fun _ _ => false)).map (fun birth => (birth.2.item.id, birth.2.origin)) =
      [(x, .item a)] ∧
    (births splitTx (fun _ _ => false)).map (fun birth => (birth.2.item.id, birth.2.origin)) ≠
      [(x, .item b)] := by decide

/-- This table view filters both version membership and text instance. A
metadata-only reservation does not create a spurious START child. -/
theorem prefix_table_control :
    let metadata : Transaction := ⟨⟨1,[67]⟩, .create none⟩
    let entries : List Entry := [⟨splitTx, [reservation twoAtoms]⟩, ⟨metadata, []⟩, ⟨twoAtoms, []⟩]
    let pre := [reservation twoAtoms, reservation metadata]
    let rows := prefixRows entries pre .initial (fun _ _ => false)
    rows.map (fun row => (row.item.id, row.origin)) = [(a,.start), (b,.item a)] ∧
    rows.map (fun row => row.item.id) ≠ [x,a,b] ∧
    prefixRows entries pre (.issued x) (fun _ _ => false) = [] := by decide

#print axioms replay_child_before_version
#print axioms prefix_ready_version
#print axioms birth_parent
#print axioms replay_child_before
#print axioms prefix_ready
end Sal.MRDTs.Instances.NotionCorePayloadParents
