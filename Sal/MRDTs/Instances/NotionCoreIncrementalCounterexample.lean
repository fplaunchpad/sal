import Sal.MRDTs.Instances.NotionCoreMachinePartitionSplit
import Sal.MRDTs.Instances.NotionCoreMachineNetwork

/-! Direct immutable cut records, and a restricted frozen-endpoint obstruction.
A cut stores only its start identity and owner. Stops are derived from physical
boundary order. This is a structural reconstruction theorem, not yet a complete
honest-protocol refinement or a lower bound against all direct representations. -/
namespace Sal.MRDTs.Instances.NotionCoreIncrementalCounterexample
open NotionCoreSpec (Address)
open NotionCoreSource (Atom)
open NotionCorePartition (Entry Cell flatten)
open NotionCoreSliceForest (Ref)
open NotionCoreMachine

def cutRecord (owned : Nat × Ref) : Entry := ⟨owned.1, owned.2.start⟩
def cutRecords (forest : NotionCoreSliceForest.Forest) : List Entry :=
  (NotionCoreForestRefs.ownedRefs forest).map cutRecord

def boundaryAt (records : List Entry) (address : Address) : Option Entry :=
  records.find? (fun entry => entry.start == address)
def orderedRecords (physical : List Atom) (records : List Entry) : List Entry :=
  physical.filterMap (fun atom => boundaryAt records atom.address)
def reconstructCells (physical : List Atom) (records : List Entry) : List Cell :=
  NotionCorePartition.scanCells physical (orderedRecords physical records)

private theorem boundaryAt_present (records : List Entry) (entry : Entry)
    (member : entry ∈ records)
    (unique : ∀ other ∈ records, other.start = entry.start → other = entry) :
    boundaryAt records entry.start = some entry := by
  induction records with
  | nil => simp at member
  | cons head rest ih =>
    by_cases hit : head.start = entry.start
    · have same := unique head (by simp) hit
      simp [boundaryAt, same]
    · have inside : entry ∈ rest := (List.mem_cons.mp member).resolve_left
        (fun same => hit (same ▸ rfl))
      simpa [boundaryAt, hit] using ih inside
        (fun other member same => unique other (by simp [member]) same)

private theorem scan_factor (cells : List Cell) (records : List Entry)
    (starts : ∀ cell ∈ cells, boundaryAt records cell.slice.start = some cell.entry)
    (interiors : ∀ cell ∈ cells, ∀ atom ∈ cell.slice.atoms, boundaryAt records atom.address = none) :
    orderedRecords (flatten cells) records = cells.map Cell.entry := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    have empty : cell.slice.atoms.filterMap (fun atom => boundaryAt records atom.address) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      exact interiors cell (by simp)
    simp only [orderedRecords, flatten, List.flatMap_cons, Cell.physical,
      List.filterMap_append, List.filterMap_cons, NotionCorePartition.boundary]
    rw [starts cell (by simp), empty]
    simpa [orderedRecords, flatten] using congrArg (cell.entry :: ·)
      (ih (fun c hc => starts c (by simp [hc]))
        (fun c hc => interiors c (by simp [hc])))

/-- The cells with every stop set to the next cell's start, the stop that
endpoint scanning assigns. Physical atoms, entries and interval references
are those of the input cells. -/
def chainCells : List Cell → List Cell
  | [] => []
  | cell :: rest =>
    ⟨cell.owner, ⟨cell.slice.start, cell.slice.atoms, rest.head?.map (fun next => next.slice.start)⟩⟩ ::
      chainCells rest

private theorem chainCells_head (cells : List Cell) :
    (chainCells cells).head?.map (fun next => next.slice.start) =
      cells.head?.map (fun next => next.slice.start) := by
  cases cells <;> rfl

theorem chainCells_flatten (cells : List Cell) : flatten (chainCells cells) = flatten cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [chainCells, flatten, List.flatMap_cons, Cell.physical] at ih ⊢
    rw [ih]

theorem chainCells_entries (cells : List Cell) : (chainCells cells).map Cell.entry = cells.map Cell.entry := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [chainCells, Cell.entry, ih]

theorem chainCells_refs (cells : List Cell) :
    NotionCoreMachinePartition.cellRefs (chainCells cells) = NotionCoreMachinePartition.cellRefs cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [chainCells, NotionCoreMachinePartition.cellRefs, ih, chainCells_head]

theorem chainCells_chained (cells : List Cell) : NotionCorePartition.Chained (chainCells cells) := by
  induction cells with
  | nil => trivial
  | cons cell rest ih => exact ⟨(chainCells_head rest).symm, ih⟩

/-- Every stored instance factors into cells whose stops are the next cells'
starts. -/
theorem partitioned_chained (state : NotionCoreMachine.State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (inst : Nat) (existsInstance : ∃ entry ∈ state.instances, entry.1 = inst) :
    ∃ cells, physical state inst = flatten cells ∧
      ((NotionCoreForestRefs.ownedRefs state.forest).filter (fun owned => owned.2.start.1 == inst)).Perm
        (NotionCoreMachinePartition.cellRefs cells) ∧ NotionCorePartition.Chained cells := by
  obtain ⟨cells,physicalEq,records⟩ := partitioned.partitions inst existsInstance
  exact ⟨chainCells cells, by rw [chainCells_flatten]; exact physicalEq, by rw [chainCells_refs]; exact records,
    chainCells_chained cells⟩

/-- Unordered owner/start records recover exact interval cells by one physical
boundary scan followed by existing endpoint extraction. The input contains no
stops and no stored assignment of text atoms to owners; the recovered stops are
the next cells' starts. -/
theorem reconstructCells_correct (cells : List Cell) (records : List Entry)
    (recordsEq : records.Perm (cells.map Cell.entry))
    (unique : ((flatten cells).map Atom.address).Nodup) (chained : NotionCorePartition.Chained cells) :
    reconstructCells (flatten cells) records = cells := by
  have atStart : ∀ cell ∈ cells, boundaryAt records cell.slice.start = some cell.entry := by
    intro cell member
    apply boundaryAt_present records cell.entry
    · exact recordsEq.mem_iff.mpr (List.mem_map.mpr ⟨cell, member, rfl⟩)
    · intro other inside same
      obtain ⟨otherCell, otherMember, rfl⟩ := List.mem_map.mp (recordsEq.mem_iff.mp inside)
      have equal : otherCell = cell := NotionCorePartition.unique_cell (origin := otherCell.slice.start) unique otherMember member
        (by simp [Cell.physical, NotionCorePartition.boundary])
        (by simp only [Cell.entry] at same; simp [Cell.physical, NotionCorePartition.boundary, same])
      cases equal
      rfl
  have absent : ∀ cell ∈ cells, ∀ atom ∈ cell.slice.atoms, boundaryAt records atom.address = none := by
    intro cell member atom inside
    apply List.find?_eq_none.mpr
    intro entry present hit
    obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp (recordsEq.mem_iff.mp present)
    have same : other.slice.start = atom.address := by simpa [Cell.entry] using hit
    have equal : other = cell := NotionCorePartition.unique_cell (origin := atom.address) unique otherMember member
      (by simp [Cell.physical, NotionCorePartition.boundary, same])
      (by simp only [Cell.physical, List.map_cons, List.mem_cons, List.mem_map]; exact Or.inr ⟨atom, inside, rfl⟩)
    subst other
    have component : (cell.slice.start :: cell.slice.atoms.map Atom.address).Nodup := by
      have mapped : (cells.flatMap (fun c => c.slice.start :: c.slice.atoms.map Atom.address)).Nodup := by
        simpa [flatten, Cell.physical, NotionCorePartition.boundary, List.map_flatMap,
          Function.comp_def] using unique
      exact (List.nodup_flatMap.mp mapped).1 cell member
    exact (List.nodup_cons.mp component).1 (List.mem_map.mpr ⟨atom, inside, same.symm⟩)
  unfold reconstructCells
  rw [scan_factor cells records atStart absent]
  exact NotionCorePartition.extraction_correct (state := ⟨flatten cells, cells.map Cell.entry⟩) ⟨rfl, rfl, unique⟩
    chained

/-- The actual split rewrite inserts the marker's record behind the fresh
destination's title record; changing an old stop leaves its start unchanged.
Records of the moved suffix keep their starts and change owner to the
destination. Fresh title roots are already included in the input forest. -/
theorem atomicSplit_cutRecords (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest : NotionCoreSliceForest.Forest)
    (chains : ∀ block ∈ forest, NotionCoreSliceForest.Chain block.title)
    (fresh : NotionCoreSliceForest.FreshMarker forest marker)
    (freshTarget : target ∉ forest.map NotionCoreSliceForest.Block.id)
    (empty : physical target = NotionCoreSliceForest.emptyPhysical target)
    (witness : ∃ block ∈ forest, ∃ ref ∈ NotionCoreSliceForest.preorderTree block.title,
      NotionCoreSliceForest.contains physical ref marker = true) :
    ∃ (result : NotionCoreSliceForest.Forest) (before : List Entry) (owner : Nat) (pre : List Ref)
      (ref : Ref) (post : List Ref) (after : List Entry),
      NotionCoreSliceForest.atomicSplit physical marker target forest = some result ∧
      cutRecords (forest ++ [⟨target,NotionCoreSliceForest.freshTitle target⟩]) =
        before ++ (pre ++ ref :: post).map (fun ref : Ref => (⟨owner,ref.start⟩ : Entry)) ++ after ++
          [⟨target,(target,.start)⟩] ∧
      cutRecords result = before ++ (pre ++ [ref]).map (fun ref : Ref => (⟨owner,ref.start⟩ : Entry)) ++ after ++
        ⟨target,(target,.start)⟩ :: ⟨target,marker⟩ :: post.map (fun ref : Ref => (⟨target,ref.start⟩ : Entry)) := by
  obtain ⟨result,executed⟩ := NotionCoreMachinePartitionSplit.atomicSplit_progress physical marker target
    forest chains fresh empty witness
  obtain ⟨before,owner,pre,ref,post,after,old,_,new⟩ :=
    NotionCoreMachinePartitionSplit.atomicSplit_refs physical marker target forest result chains fresh
      freshTarget empty executed
  refine ⟨result,before.map cutRecord,owner,pre,ref,post,after.map cutRecord,executed,?_,?_⟩
  · simp [cutRecords, old, cutRecord, NotionCoreSliceForest.titleRef, List.map_append, Function.comp_def]
  · simp [cutRecords, new, cutRecord, NotionCoreSliceForest.titleRef, NotionCoreSliceForest.leftRef,
      NotionCoreSliceForest.rightRef, List.map_append, Function.comp_def]

private theorem cellRefs_records (cells : List Cell) :
    (NotionCoreMachinePartition.cellRefs cells).map cutRecord = cells.map Cell.entry := by
  induction cells with
  | nil => rfl
  | cons cell rest ih => simp [NotionCoreMachinePartition.cellRefs, cutRecord, Cell.entry, ih]

/-- Existing physical-partition correctness transports to the new stop-free
representation. The returned cells are extracted from owner/start records alone;
forest stops play no role in the direct reconstruction computation. -/
theorem partitioned_reconstruct (state : NotionCoreMachine.State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (inst : Nat) (existsInstance : ∃ entry ∈ state.instances, entry.1 = inst) :
    ∃ cells, physical state inst = flatten cells ∧
      reconstructCells (physical state inst)
        (((NotionCoreForestRefs.ownedRefs state.forest).filter
          (fun owned => owned.2.start.1 == inst)).map cutRecord) = cells := by
  obtain ⟨cells,physicalEq,records,chained⟩ := partitioned_chained state partitioned inst existsInstance
  refine ⟨cells,physicalEq,?_⟩
  rw [physicalEq]
  apply reconstructCells_correct cells _
  · simpa [cellRefs_records] using records.map cutRecord
  · simpa [physicalEq] using unique inst
  · exact chained

private def seed : NotionCorePayload.Transaction := NotionCorePayload.bootstrap [97,98]
private def low : NotionCorePayload.Transaction :=
  ⟨⟨3,[66]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def high : NotionCorePayload.Transaction :=
  ⟨⟨3,[67]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def marker (tx : NotionCorePayload.Transaction) : Address :=
  NotionCorePhysicalReplay.address 0 tx.id
private def target (tx : NotionCorePayload.Transaction) : Nat := blockName (.issued tx.id)
private def highBranch : Option NotionCoreMachine.State := replay {} [seed,high]
private def canonical : Option NotionCoreMachine.State := replay {} [seed,low,high]
private def frozenHigh : Ref := ⟨marker high,none⟩
private def repairedHigh : Ref := ⟨marker high,some (marker low)⟩
private def concurrentNetwork : NotionCorePayloadNetwork.State :=
  NotionCorePayloadNetwork.exchange
    (NotionCorePayloadNetwork.exchange (NotionCorePayloadNetwork.seeded [97,98]) [66] [65]) [67] [65]
private def withLow : NotionCorePayloadNetwork.State :=
  NotionCorePayloadNetwork.emit concurrentNetwork [66] low.payload low
private def withBoth : NotionCorePayloadNetwork.State :=
  NotionCorePayloadNetwork.emit withLow [67] high.payload high

/-- Both splits are issued by the actual positional client from independent
whole bootstrap receipts. No fabricated marker, origin, or allocator is used. -/
theorem honestly_issuable_splits :
    NotionCoreMachineNetwork.issue concurrentNetwork [66] (.split .initial 1) = some withLow ∧
    NotionCoreMachineNetwork.issue withLow [67] (.split .initial 1) = some withBoth ∧
    NotionCoreMachineNetwork.Reach withBoth := by
  have first : NotionCoreMachineNetwork.issue concurrentNetwork [66] (.split .initial 1) = some withLow := by
    have rebuilt : NotionCoreReconstruction.reconstruct concurrentNetwork [66] = some ((replay {} [seed]).getD {}) := by decide +kernel
    have selected : NotionCoreMachineNetwork.prepareRequest ((replay {} [seed]).getD {}) (.split .initial 1) = some low.payload := by decide +kernel
    have prepared : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget concurrentNetwork) [66] low.payload = some low := by decide +kernel
    simp [NotionCoreMachineNetwork.issue, NotionCoreMachineNetwork.Request.earlyNoop, rebuilt, selected, prepared, withLow]
  have second : NotionCoreMachineNetwork.issue withLow [67] (.split .initial 1) = some withBoth := by
    have rebuilt : NotionCoreReconstruction.reconstruct withLow [67] = some ((replay {} [seed]).getD {}) := by decide +kernel
    have selected : NotionCoreMachineNetwork.prepareRequest ((replay {} [seed]).getD {}) (.split .initial 1) = some high.payload := by decide +kernel
    have prepared : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget withLow) [67] high.payload = some high := by decide +kernel
    simp [NotionCoreMachineNetwork.issue, NotionCoreMachineNetwork.Request.earlyNoop, rebuilt, selected, prepared, withBoth]
  refine ⟨first,second,?_⟩
  exact .request [67] (.split .initial 1)
    (.request [66] (.split .initial 1)
      (.exchange [67] [65] (.exchange [66] [65] (.bootstrap [97,98]))) first) second

/-- Two characters and two concurrent splits suffice: a late lower source key
requires changing an already materialized stop. Unioning branch refs freezes
high's old END and therefore duplicates b. This refutes frozen refs, not the
immutable cut representation above or every directly mergeable design. -/
theorem frozen_endpoint_control :
    (highBranch >>= fun state => sliceAtoms state frozenHigh).map (List.flatMap atomText) = some [98] ∧
    (canonical >>= render) = some [(0,[97]),(target high,[]),(target low,[98])] ∧
    (canonical >>= fun state => sliceAtoms state frozenHigh).map (List.flatMap atomText) = some [98] ∧
    (canonical >>= fun state => sliceAtoms state repairedHigh).map (List.flatMap atomText) = some [] ∧
    (canonical >>= fun state => sliceAtoms state frozenHigh).map (List.flatMap atomText) ≠ some [] ∧
    (replay {} [seed,high,low] >>= render) ≠ (canonical >>= render) := by
  decide +kernel

/-- The stop-free scanner repairs high's interval from both immutable cut starts;
its output matches canonical ownership and rejects the frozen-END answer. -/
theorem direct_cut_control :
    let records : List Entry := [⟨target low,marker low⟩,⟨0,(0,.start)⟩,⟨target high,marker high⟩]
    let cells := canonical.map fun state => reconstructCells (physical state 0) records
    cells.map (List.map fun cell => (cell.owner,cell.slice.atoms.flatMap atomText)) =
      some [(0,[97]),(target high,[]),(target low,[98])] ∧
    cells.map (List.map fun cell => (cell.owner,cell.slice.atoms.flatMap atomText)) ≠
      some [(0,[97]),(target high,[98]),(target low,[98])] := by
  decide +kernel

#print axioms partitioned_reconstruct
#print axioms honestly_issuable_splits
#print axioms frozen_endpoint_control
#print axioms direct_cut_control

#print axioms reconstructCells_correct
#print axioms atomicSplit_cutRecords
end Sal.MRDTs.Instances.NotionCoreIncrementalCounterexample
