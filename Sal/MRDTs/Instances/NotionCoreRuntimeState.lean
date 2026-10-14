import Sal.MRDTs.Instances.NotionCoreRuntimeTypes
import Sal.MRDTs.Instances.NotionCoreStructuralDisplay
import Sal.MRDTs.Instances.NotionCoreStructuralCuts

/-! Native executable primary stores and retained origin buckets. Receipt and
merge are atomic pure batches. Conflicting immutable keys are explicitly
rejected; full transaction identity and allocator metadata live in the original
client/protocol sidecar. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeState
open NotionCoreRuntimeTypes (ItemKey OriginKey)
open NotionCorePayload (BlockKey Transaction)
open NotionCoreParentMap (Row Table)
open NotionCoreOriginTree (Origin)
open NotionRunAllocation (Id)
open NotionCoreStructuralFacts (Fact decodeList)

structure State where
  births : Std.HashMap ItemKey Row := ∅
  erased : Std.HashSet ItemKey := ∅
  cuts : Std.HashMap ItemKey BlockKey := ∅
  created : Std.HashMap BlockKey (Option BlockKey) := ∅
  children : Std.HashMap OriginKey (List Id) := ∅
  counts : Std.HashMap BlockKey Nat := ∅
  deriving Repr

def empty : State := {}
def birthAt (s : State) (inst : BlockKey) (id : Id) : Option Row := s.births[(inst,id)]?
def tombstone (s : State) (inst : BlockKey) (row : Row) : Row :=
  {row with item := {row.item with kind := match row.item.kind with
    | .text value deleted => .text value (deleted || s.erased.contains (inst,row.item.id))
    | .split => .split}}
def lookupAt (s : State) (inst : BlockKey) (id : Id) : Option Row :=
  (birthAt s inst id).map (tombstone s inst)
def childrenAt (s : State) (inst : BlockKey) (origin : Origin) : List Id :=
  (s.children[(inst,origin)]?).getD []
def countAt (s : State) (inst : BlockKey) : Nat := (s.counts[inst]?).getD 0
def birthsAt (s : State) (inst : BlockKey) : Table :=
  s.births.toList.filterMap fun p => if p.1.1 = inst then some p.2 else none
def targetsAt (s : State) (inst : BlockKey) : List Id :=
  s.erased.toList.filterMap fun p => if p.1 = inst then some p.2 else none
/-- Tombstones are projected on read; parent links/buckets remain retained. -/
def rowsAt (s : State) (inst : BlockKey) : Table :=
  NotionCoreParentErase.erase (targetsAt s inst) (birthsAt s inst)
def creatorLinks (s : State) : List NotionCoreStructuralDisplay.Link := s.created.toList

def factsList (s : State) : List Fact :=
  s.births.toList.map (fun p => .birth p.1.1 p.2) ++
  s.erased.toList.map (fun p => .erased p.1 p.2) ++
  s.cuts.toList.map (fun p => .cut p.1.1 p.1.2 p.2) ++
  s.created.toList.map (fun p => .created p.1 p.2)
/-- Computable abstraction enumerates executable maps, never Finset.toList. -/
def abstract (s : State) : Finset Fact := (factsList s).toFinset

def insertFact (s : State) (fact : Fact) : Except String State := match fact with
  | .birth inst row =>
      match s.births[(inst,row.item.id)]? with
      | some old => if old = row then .ok s else .error "conflicting birth"
      | none =>
          .ok {s with births := s.births.insert (inst,row.item.id) row, children := s.children.insert (inst,row.origin) ((childrenAt s inst row.origin).orderedInsert NotionCoreSourceInvariant.Desc row.item.id), counts := s.counts.insert inst (countAt s inst + 1)}
  | .erased inst id => .ok {s with erased := s.erased.insert (inst,id)}
  | .cut inst id target =>
      match s.cuts[(inst,id)]? with
      | some old => if old = target then .ok s else .error "conflicting cut"
      | none => .ok {s with cuts := s.cuts.insert (inst,id) target}
  | .created block afterBlock =>
      match s.created[block]? with
      | some old => if old = afterBlock then .ok s else .error "conflicting creation"
      | none => .ok {s with created := s.created.insert block afterBlock}

def receive (s : State) (tx : Transaction) : Except String State :=
  (decodeList tx).foldlM insertFact s
def merge (left right : State) : Except String State :=
  (factsList right).foldlM insertFact left

/-- Primary birth keys are exactly the IDs stored in the corresponding rows. -/
def RowKeys (s : State) : Prop :=
  ∀ (inst : BlockKey) (id : Id) (row : Row), s.births[(inst,id)]? = some row → row.item.id = id
/-- Exact retained adjacency; bucket values are not a query-result cache. -/
def Buckets (s : State) : Prop :=
  ∀ inst origin, childrenAt s inst origin = NotionCoreParentMap.sortedChildren (birthsAt s inst) origin

def Counts (s : State) : Prop := ∀ inst, countAt s inst = (birthsAt s inst).length
def Valid (s : State) : Prop := RowKeys s ∧ Buckets s ∧ Counts s

end Sal.MRDTs.Instances.NotionCoreRuntimeState
