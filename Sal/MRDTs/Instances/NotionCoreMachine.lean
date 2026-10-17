import Sal.MRDTs.Instances.NotionCorePayload
import Sal.MRDTs.Instances.NotionCoreParentErase
import Sal.MRDTs.Instances.NotionCoreDisplayOrder
import Sal.MRDTs.Instances.NotionCorePhysicalReplay

/-! Combined typed core interpreter. No search-label validation or source JS
codec/decoder equivalence is claimed. Traversal fuel is sufficient on the closed,
unique increasing parent maps proved separately; malformed cycles are outside
that operational boundary. Operation lists commit only on complete success. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Sal.MRDTs.Instances.NotionCoreMachine
open NotionCorePayload (BlockKey Transaction Operation)
open NotionRunAllocation (Id)
open NotionCoreParentMap (Table Row)
open NotionCoreSliceForest (Forest Ref)

def blockName : BlockKey → Nat
  | .initial => 0
  | .issued id => 1 + Encodable.encode (id.counter, id.session)

theorem blockName_injective : Function.Injective blockName := by
  intro a b h
  cases a with
  | initial =>
    cases b with
    | initial => rfl
    | issued id => simp [blockName, Nat.add_comm] at h
  | issued ai =>
    cases b with
    | initial => simp [blockName, Nat.add_comm] at h
    | issued bi =>
      have e := Encodable.encode_injective (Nat.add_left_cancel h)
      have hc := congrArg Prod.fst e
      have hs := congrArg Prod.snd e
      cases ai; cases bi
      simp_all

structure Instance where
  rows : Table := []
  pending : List Id := []
  deriving DecidableEq, Repr
structure State where
  instances : List (Nat × Instance) := []
  forest : Forest := []
  display : List Nat := []
  deriving DecidableEq, Repr

def getInstance (state : State) (inst : Nat) : Instance :=
  ((state.instances.find? fun p => p.1 == inst).map Prod.snd).getD {}
def putInstance (state : State) (inst : Nat) (value : Instance) : State :=
  if state.instances.any (fun p => p.1 == inst) then
    {state with instances := state.instances.map fun p => if p.1 == inst then (inst,value) else p}
  else {state with instances := state.instances ++ [(inst,value)]}

/-- Structurally recursive evaluation of the same total sibling order. The
library merge sort uses an opaque termination proof; this evaluator permits
kernel reduction of combined controls, with equality proved below. -/
def children (rows : Table) (origin : NotionCoreOriginTree.Origin) : List Id :=
  (NotionCoreParentMap.childIds rows origin).insertionSort NotionCoreSourceInvariant.Desc

theorem children_correct (rows : Table) (origin : NotionCoreOriginTree.Origin) :
    children rows origin = NotionCoreParentMap.sortedChildren rows origin := by
  symm
  exact List.mergeSort_eq_insertionSort NotionCoreSourceInvariant.Desc _

def traversal : Nat → Table → NotionCoreOriginTree.Origin → List NotionCoreOriginTree.Item
  | 0, _, _ => []
  | fuel + 1, rows, origin => (children rows origin).flatMap fun id =>
      match NotionCoreParentMap.lookup rows id with
      | none => []
      | some row => row.item :: traversal fuel rows (.item id)

theorem traversal_correct (fuel : Nat) (rows : Table) (origin : NotionCoreOriginTree.Origin) :
    traversal fuel rows origin = NotionCoreParentMap.traverse fuel rows origin := by
  induction fuel generalizing origin with
  | zero => rfl
  | succ fuel ih =>
      simp only [traversal, NotionCoreParentMap.traverse, children_correct]
      congr 1
      funext id
      cases NotionCoreParentMap.lookup rows id <;> simp only [ih]

def physical (state : State) (inst : Nat) : List NotionCoreSource.Atom :=
  NotionCorePhysicalReplay.physical inst
    (traversal (getInstance state inst).rows.length (getInstance state inst).rows .start)

def validBounds (state : State) (slice : Ref) : Bool :=
  let ids := (physical state slice.start.1).map NotionCoreSource.Atom.address
  (state.instances.any fun entry => entry.1 == slice.start.1) && ids.contains slice.start && match slice.stop with
    | none => decide (ids.idxOf slice.start < ids.length)
    | some stop => ids.contains stop && decide (ids.idxOf slice.start < ids.idxOf stop)
def validForestBounds (state : State) : Bool :=
  state.forest.all fun b => (NotionCoreSliceForest.preorderTree b.title).all (validBounds state)

def sameContent : NotionCoreOriginTree.Kind → NotionCoreOriginTree.Kind → Prop
  | .text v _, .text w _ => v = w
  | .split, .split => True
  | _, _ => False
instance (a b : NotionCoreOriginTree.Kind) : Decidable (sameContent a b) := by
  cases a <;> cases b <;> simp [sameContent] <;> infer_instance

def integrate (rows : Table) (row : Row) : Option Table :=
  match NotionCoreParentMap.lookup rows row.item.id with
  | some old => if old.origin = row.origin ∧ old.item.id = row.item.id ∧ sameContent old.item.kind row.item.kind then some rows else none
  | none => if row.origin = .item row.item.id then none else some (rows ++ [row])
def integrateRows : Table → List Row → Option Table
  | rows, [] => some rows
  | rows, row::rest => do integrateRows (← integrate rows row) rest

def applyOperation (state : State) : Operation → Option State
  | .create block afterBlock =>
    let bid := blockName block
    if bid ∈ state.display then some state else
    let withInst := if state.instances.any (fun p => p.1 == bid) then state
      else putInstance state bid {}
    let forest := if withInst.forest.any (fun b => b.id == bid) then withInst.forest
      else withInst.forest ++ [⟨bid, NotionCoreSliceForest.freshTitle bid⟩]
    some {instances := withInst.instances, forest := forest, display := NotionCoreDisplayOrder.insert (state.display.filter (· != bid)) bid (afterBlock.map blockName)}
  | .insert _ inst first origin atoms => do
    let key := blockName inst
    let current := getInstance state key
    let items := NotionCorePayload.textItems first atoms (fun id => decide (id ∈ current.pending))
    let rows ← integrateRows current.rows (NotionCoreParentMap.runRows origin items)
    pure (putInstance state key {current with rows := rows})
  | .erase _ inst targets =>
    let key := blockName inst
    let current := getInstance state key
    some (putInstance state key {rows := NotionCoreParentErase.erase targets current.rows, pending := current.pending ++ targets})
  | .marker _ inst id origin => do
    let key := blockName inst
    let current := getInstance state key
    let rows ← integrate current.rows ⟨⟨id,.split⟩,origin⟩
    let updated := putInstance state key {current with rows := rows}
    let forest ← NotionCoreSliceForest.splitForest (physical updated)
      (NotionCorePhysicalReplay.address key id) updated.forest
    let final := {updated with forest := forest}
    if validForestBounds final then pure final else none
  | .moveInto _ inst marker target => do
    let bid := blockName target
    if !(state.forest.any fun b => b.id == bid) then none else do
      let (forest,child) ← NotionCoreSliceForest.detachForest
        (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest
      pure {state with forest := NotionCoreSliceForest.appendToBlock bid child forest}
  | .merge source target =>
    some {state with forest := NotionCoreSliceForest.mergeForest state.forest (blockName source) (blockName target)}

/-- A block name that names no forest block and no display entry, tombstones
included: the names for which create is not a no-op. -/
def FreshBlock (state : State) (bid : Nat) : Prop :=
  (∀ old ∈ state.forest, old.id ≠ bid) ∧ bid ∉ state.display

def applyOperations : State → List Operation → Option State
  | state, [] => some state
  | state, op::rest => do applyOperations (← applyOperation state op) rest

def applyTransaction (state : State) (tx : Transaction) : Option State :=
  applyOperations state (NotionCorePayload.operations tx)
def replay : State → List Transaction → Option State
  | state, [] => some state
  | state, tx::rest => do replay (← applyTransaction state tx) rest

/-- Explicit source boundary checks before interval extraction; neither missing
endpoint nor reversed bounds is silently interpreted as an empty interval. -/
def sliceAtoms (state : State) (slice : Ref) : Option (List NotionCoreSource.Atom) := do
  let atoms := physical state slice.start.1
  let ids := atoms.map NotionCoreSource.Atom.address
  if !(state.instances.any fun entry => entry.1 == slice.start.1) || !(ids.contains slice.start) then none else do
    let stopIndex ← match slice.stop with
      | none => some ids.length
      | some stop => if ids.contains stop then some (ids.idxOf stop) else none
    if ids.idxOf slice.start >= stopIndex then none else
      some (NotionCorePartition.extract atoms slice.start slice.stop)
def atomText (atom : NotionCoreSource.Atom) : List Nat := match atom.kind with
  | .text value false => [value]
  | _ => []
def treeAtoms (state : State) (tree : NotionCoreSliceForest.Tree) : Option (List NotionCoreSource.Atom) := do
  let slices ← (NotionCoreSliceForest.preorderTree tree).mapM (sliceAtoms state)
  pure slices.flatten
def blockText (state : State) (bid : Nat) : Option (List Nat) := do
  let block ← state.forest.find? (fun b => b.id == bid)
  let atoms ← treeAtoms state block.title
  pure (atoms.flatMap atomText)
/-- A merged-away block keeps its display position as a tombstone; only
display entries whose block is still in the forest are rendered. -/
def visible (state : State) : List Nat :=
  state.display.filter fun bid => state.forest.any fun b => b.id == bid
def render (state : State) : Option (List (Nat × List Nat)) :=
  (visible state).mapM fun bid => do pure (bid, ← blockText state bid)

private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨4,[66]⟩
private def c : Id := ⟨4,[67]⟩
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]

/-- Bootstrap is one atomic create+insert operation list. -/
theorem bootstrap_control :
    (applyTransaction {} seed >>= render) = some [(0,[97,98])] ∧
    (applyTransaction {} seed >>= render) ≠ some [] := by
  decide +kernel

/-- Tombstone origins remain physically searchable for subsequent insertion. -/
theorem hidden_origin_control :
    (replay {} [seed, ⟨⟨3,[65]⟩,.erase .initial [(.initial,[a])]⟩,
      ⟨b,.insert .initial .initial (.item a) [88]⟩] >>= render) = some [(0,[88,98])] ∧
    (replay {} [seed, ⟨⟨3,[65]⟩,.erase .initial [(.initial,[a])]⟩,
      ⟨b,.insert .initial .initial (.item a) [88]⟩] >>= render) ≠ some [(0,[98,88])] := by
  decide +kernel

/-- Source split marker before concurrent insertion routes that insertion left. -/
theorem split_insert_control :
    (replay {} [seed, ⟨b,.split .initial .initial (.item a)⟩,
      ⟨c,.insert .initial .initial (.item a) [88]⟩] >>= render) =
      some [(0,[97,88]),(blockName (.issued b),[98])] ∧
    (replay {} [seed, ⟨b,.split .initial .initial (.item a)⟩,
      ⟨c,.insert .initial .initial (.item a) [88]⟩] >>= render) ≠
      some [(0,[97]),(blockName (.issued b),[88,98])] := by
  decide +kernel

theorem conflict_control : integrateRows [] [⟨⟨a,.text 97 false⟩,.start⟩,
    ⟨⟨a,.text 98 false⟩,.start⟩] = none ∧
    integrateRows [] [⟨⟨a,.text 97 false⟩,.start⟩,
    ⟨⟨a,.text 97 false⟩,.start⟩] ≠ none := by
  decide +kernel

/-- Forest enumeration remains map insertion order, display insertion is separate. -/
theorem map_display_control :
    (replay {} [seed, ⟨b,.create none⟩]).map (fun s => (s.forest.map (·.id),s.display)) =
      some ([0,blockName (.issued b)],[blockName (.issued b),0]) ∧
    (replay {} [seed, ⟨b,.create none⟩]).map (fun s => s.display) ≠
      some [0,blockName (.issued b)] := by
  decide +kernel

/-- Duplicate delivery compares payload content, preserving the old tombstone. -/
theorem duplicate_tombstone_control :
    integrate [⟨⟨a,.text 97 true⟩,.start⟩] ⟨⟨a,.text 97 false⟩,.start⟩ =
      some [⟨⟨a,.text 97 true⟩,.start⟩] ∧
    integrate [⟨⟨a,.text 97 true⟩,.start⟩] ⟨⟨a,.text 97 false⟩,.start⟩ ≠
      some [⟨⟨a,.text 97 false⟩,.start⟩] := by decide +kernel

/-- Recreating an existing block does not apply its new placement request. -/
theorem existing_create_control :
    (replay {} [seed, ⟨b,.create none⟩] >>= fun state =>
      applyOperation state (.create .initial none)).map (·.display) =
        some [blockName (.issued b),0] ∧
    (replay {} [seed, ⟨b,.create none⟩] >>= fun state =>
      applyOperation state (.create .initial none)).map (·.display) ≠
        some [0,blockName (.issued b)] := by decide +kernel

private def d : Id := ⟨5,[66]⟩

/-- PASS+FAIL: merging the split destination back into its source renders the
whole text in the source and hides the merged block, which stays in the
display order as a tombstone. -/
theorem merge_back_control :
    (replay {} [seed, ⟨b,.split .initial .initial (.item a)⟩,
      ⟨d,.merge (.issued b) .initial⟩] >>= render) = some [(0,[97,98])] ∧
    (replay {} [seed, ⟨b,.split .initial .initial (.item a)⟩,
      ⟨d,.merge (.issued b) .initial⟩]).map (·.display) = some [0,blockName (.issued b)] ∧
    (replay {} [seed, ⟨b,.split .initial .initial (.item a)⟩,
      ⟨d,.merge (.issued b) .initial⟩] >>= render) ≠ some [(0,[97])] ∧
    (replay {} [seed, ⟨b,.split .initial .initial (.item a)⟩,
      ⟨d,.merge (.issued b) .initial⟩] >>= render) ≠
      some [(0,[97]),(blockName (.issued b),[98])] := by
  decide +kernel

/-- A create after a merged-away block lands at its tombstone, not at the front. -/
theorem create_after_tombstone_control :
    (replay {} [seed, ⟨b,.create none⟩, ⟨c,.merge (.issued b) .initial⟩,
      ⟨d,.create (some (.issued b))⟩]).map (·.display) =
      some [blockName (.issued b),blockName (.issued d),0] ∧
    (replay {} [seed, ⟨b,.create none⟩, ⟨c,.merge (.issued b) .initial⟩,
      ⟨d,.create (some (.issued b))⟩]).map (·.display) ≠
      some [blockName (.issued d),blockName (.issued b),0] := by
  decide +kernel

/-- A create naming a merged-away block is a no-op: the tombstone keeps its
display position and the block is not revived in the forest. -/
theorem tombstone_create_control :
    (replay {} [seed, ⟨b,.create none⟩, ⟨c,.merge (.issued b) .initial⟩] >>= fun state =>
      applyOperation state (.create (.issued b) none)).map (fun s => (s.display,s.forest.map (·.id))) =
        some ([blockName (.issued b),0],[0]) ∧
    (replay {} [seed, ⟨b,.create none⟩, ⟨c,.merge (.issued b) .initial⟩] >>= fun state =>
      applyOperation state (.create (.issued b) none)).map (fun s => (s.display,s.forest.map (·.id))) ≠
        some ([blockName (.issued b),0],[0,blockName (.issued b)]) := by
  decide +kernel

#print axioms merge_back_control
#print axioms tombstone_create_control
#print axioms duplicate_tombstone_control
#print axioms existing_create_control
#print axioms traversal_correct
#print axioms blockName_injective
#print axioms bootstrap_control
#print axioms hidden_origin_control
#print axioms split_insert_control
#print axioms map_display_control

end Sal.MRDTs.Instances.NotionCoreMachine
