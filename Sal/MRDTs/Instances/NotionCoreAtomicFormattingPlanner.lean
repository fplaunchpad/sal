import Sal.MRDTs.Instances.NotionCoreAtomicFormatting

/-! The unchanged maximal-run planner supplies exact visible coverage to the
shared-priority batch evaluator. Batch arbitration changes; current interval
selection does not. Coordinate/integrity premises here are structural helper
premises, to be derived by the reachable protocol bridge.
-/
namespace Sal.MRDTs.Instances.NotionCoreAtomicFormatting
open NotionCoreSpec (Address Document)
open NotionCoreOriginTree (Forest)
open NotionCoreFormattingSource (Positioned)

theorem segment_coversAt (forests : Nat → Forest) (coordinate : Address → Nat)
    (located : Nat × NotionCoreFormattingSource.MarkOp) (address : Address) :
    segmentCovers forests (Segment.ofLocated located) address.1 (coordinate address) =
      NotionCoreFormattingBridge.coversAt forests coordinate located address := by
  by_cases same : address.1 = located.1
  · simp [segmentCovers,Segment.ofLocated,Segment.operation,NotionCoreFormattingBridge.coversAt,
      same,NotionCoreFormattingSource.covers]
  · simp [segmentCovers,Segment.ofLocated,NotionCoreFormattingBridge.coversAt,same,Ne.symm same]

theorem ofFormat_coversAt (forests : Nat → Forest) (coordinate : Address → Nat)
    (priority : NotionRunAllocation.Id) (parts : List NotionCoreRichPayload.Part) (value : Bool)
    (address : Address) :
    covers forests (Batch.ofFormat priority parts value) address.1 (coordinate address) =
      (NotionCoreRichPayload.emit priority value parts).any
        (fun operation => NotionCoreFormattingBridge.coversAt forests coordinate operation address) := by
  simp only [covers,Batch.ofFormat,List.any_map,Function.comp_def,segment_coversAt]

def planned (forests : Nat → Forest) (targets : List Address) (instances : List Nat)
    (priority : NotionRunAllocation.Id) (value : Bool) : Batch :=
  Batch.ofFormat priority (NotionCoreRichPayload.partsOf
    (NotionCoreFormattingPlanner.locatedSegments forests NotionCorePhysicalReplay.address targets instances)) value

theorem planned_coversAt (forests : Nat → Forest) (coordinate : Address → Nat)
    (targets : List Address) (instances : List Nat) (priority : NotionRunAllocation.Id) (value : Bool)
    (address : Address) :
    covers forests (planned forests targets instances priority value) address.1 (coordinate address) =
      (NotionCoreFormattingPlanner.plan forests NotionCorePhysicalReplay.address targets instances
        priority.session priority.counter value).any
          (fun operation => NotionCoreFormattingBridge.coversAt forests coordinate operation address) := by
  rw [planned,ofFormat_coversAt,NotionCoreRichPayload.emit_planner]
  rfl

theorem planned_exact_at (forests : Nat → Forest) (coordinate : Address → Nat)
    (targets : List Address) (instances : List Nat) (priority : NotionRunAllocation.Id) (value : Bool)
    (address : Address) (instancePresent : address.1 ∈ instances)
    (unique : NotionCoreFormattingPlanner.UniqueIds (forests address.1))
    (positioned : Positioned) (member : positioned ∈ NotionCoreFormattingPlanner.visible (forests address.1))
    (identity : NotionCorePhysicalReplay.address address.1 positioned.item.id = address)
    (position : coordinate address = positioned.entry) :
    covers forests (planned forests targets instances priority value) address.1 (coordinate address) =
      targets.contains address := by
  rw [planned_coversAt]
  exact NotionCoreFormattingPlanner.plan_exact_at forests NotionCorePhysicalReplay.address coordinate
    targets instances priority.session priority.counter value address instancePresent unique positioned member identity position

theorem planned_exact_coverage (doc : Document) (forests : Nat → Forest) (coordinate : Address → Nat)
    (targets : List Address) (instances : List Nat) (priority : NotionRunAllocation.Id) (value : Bool)
    (related : NotionCoreFormattingPlanner.DisplayCoordinates doc forests
      NotionCorePhysicalReplay.address coordinate instances) :
    ∀ block ∈ doc, block.alive = true → ∀ slot ∈ block.slots, slot.visible = true →
      covers forests (planned forests targets instances priority value) slot.address.1 (coordinate slot.address) =
        targets.contains slot.address := by
  intro block member alive slot retained visible
  rw [planned_coversAt]
  exact NotionCoreFormattingPlanner.plan_exact_coverage doc forests NotionCorePhysicalReplay.address
    coordinate targets instances priority.session priority.counter value related block member alive slot retained visible

#print axioms planned_exact_at
#print axioms planned_exact_coverage
end Sal.MRDTs.Instances.NotionCoreAtomicFormatting
