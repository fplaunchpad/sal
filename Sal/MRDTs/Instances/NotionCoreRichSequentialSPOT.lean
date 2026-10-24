import Sal.MRDTs.Instances.NotionCoreRichSequentialDocument

/-! Hand-derived controls for the independent direct-state rich semantics.
No source renderer, annotation list, priority or transaction replay is used.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 2048
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.SPOT
open NotionCoreSpec

private def a : Slot := character 0 (0,1) 97
private def b : Slot := character 0 (0,2) 98
private def c : Slot := character 0 (0,3) 99
private def x : Slot := character 0 (1,10) 120
private def otherX : Slot := character 1 (1,10) 120
private def seed : Command := .core [.create 0 0 none,.insert (0,.start) [a,b,c]]
private def boldB : Command := .format [⟨0,.before (0,2),.before (0,3)⟩] true
private def boldBC : Command := .format [⟨0,.before (0,2),.finish⟩] true
private def boldC : Command := .format [⟨0,.before (0,3),.finish⟩] true
private def insertAfterA : Command := .core [.insert (0,.event (0,1)) [x]]
private def insertAfterB : Command := .core [.insert (0,.event (0,2)) [x]]
private def insertAfterC : Command := .core [.insert (0,.event (0,3)) [x]]
private def deleteB : Command := .core [.delete [(0,.event (0,2))]]
private def divide : Command := .core [.create 1 1 (some 0),.split (0,.event (0,2)) (1,5) 1]
private def insertThroughMarker : Command := .core [.insert (0,.event (1,5)) [x]]
private def insertThroughRoot : Command := .core [.insert (1,.start) [otherX]]
private def mergeBack : Command := .core [.merge 1 (0,.close (1,5))]

private def output (commands : List Command) : Option (List (Nat × List (Nat × Bool))) :=
  (execute {} commands >>= render).map fun doc =>
    doc.map fun (bid,chars) => (bid,chars.map fun ch => (ch.value,ch.bold))

/-- Before a selected item's left boundary stays plain; the right boundary
inherits. The two negative controls exclude symmetric boundary growth. -/
theorem left_right_boundary_control :
    output [seed,boldB,insertAfterA] = some [(0,[(97,false),(120,false),(98,true),(99,false)])] ∧
    output [seed,boldB,insertAfterA] ≠ some [(0,[(97,false),(120,true),(98,true),(99,false)])] ∧
    output [seed,boldB,insertAfterB] = some [(0,[(97,false),(98,true),(120,true),(99,false)])] ∧
    output [seed,boldB,insertAfterB] ≠ some [(0,[(97,false),(98,true),(120,false),(99,false)])] := by decide +kernel

/-- Interior insertion and END inherit without giving new identities an
arbitrary initial mark or freezing the original selected-ID set. -/
theorem interior_and_end_control :
    output [seed,boldBC,insertAfterB] = some [(0,[(97,false),(98,true),(120,true),(99,true)])] ∧
    output [seed,boldBC,insertAfterB] ≠ some [(0,[(97,false),(98,true),(120,false),(99,true)])] ∧
    output [seed,boldC,insertAfterC] = some [(0,[(97,false),(98,false),(99,true),(120,true)])] ∧
    output [seed,boldC,insertAfterC] ≠ some [(0,[(97,false),(98,false),(99,true),(120,false)])] := by decide +kernel

/-- Deletion retains the physical boundary. Inserting before the deleted
start differs from inserting through that retained tombstone. -/
theorem tombstone_boundary_control :
    output [seed,boldB,deleteB,insertAfterA] = some [(0,[(97,false),(120,false),(99,false)])] ∧
    output [seed,boldB,deleteB,insertAfterA] ≠ some [(0,[(97,false),(120,true),(99,false)])] ∧
    output [seed,boldB,deleteB,insertAfterB] = some [(0,[(97,false),(120,true),(99,false)])] ∧
    output [seed,boldB,deleteB,insertAfterB] ≠ some [(0,[(97,false),(120,false),(99,false)])] := by decide +kernel

/-- Splitting births a physical marker whose gaps inherit; corrected merging
moves displayed slices while retaining the marks of the underlying instance. -/
theorem split_merge_inheritance_control :
    output [seed,boldBC,divide,insertThroughMarker] =
      some [(0,[(97,false),(98,true)]),(1,[(120,true),(99,true)])] ∧
    output [seed,boldBC,divide,insertThroughMarker] ≠
      some [(0,[(97,false),(98,true)]),(1,[(120,false),(99,true)])] ∧
    output [seed,boldBC,divide,insertThroughMarker,mergeBack] =
      some [(0,[(97,false),(98,true),(120,true),(99,true)])] ∧
    output [seed,boldBC,divide,insertThroughMarker,mergeBack] ≠
      some [(0,[(97,false),(98,true)]),(1,[(120,true),(99,true)])] := by decide +kernel

/-- The new empty root and the moved marker occupy the same visible zero gap,
but name distinct physical instance/origins and have different inheritance.
A plain-text gap abstraction alone must not choose between these routes. -/
theorem root_marker_distinction_control :
    output [seed,boldBC,divide,insertThroughRoot] =
      some [(0,[(97,false),(98,true)]),(1,[(120,false),(99,true)])] ∧
    output [seed,boldBC,divide,insertThroughRoot] ≠ output [seed,boldBC,divide,insertThroughMarker] := by decide +kernel

/-- One issuance verdict covers all selected identities. Receiving an already
chosen add does not toggle again against a changed current rich state. -/
theorem issued_boolean_control :
    ((execute {} [seed,boldB]).bind fun state =>
      issueFormat state [(0,.event (0,2)),(0,.event (0,3))] [⟨0,.before (0,2),.finish⟩]) =
      some (.format [⟨0,.before (0,2),.finish⟩] true) ∧
    ((execute {} [seed,boldBC]).bind fun state =>
      issueFormat state [(0,.event (0,2)),(0,.event (0,3))] [⟨0,.before (0,2),.finish⟩]) =
      some (.format [⟨0,.before (0,2),.finish⟩] false) ∧
    output [seed,boldBC,boldBC] = output [seed,boldBC] ∧
    output [seed,boldBC,boldBC] ≠ output [seed] := by decide +kernel

#print axioms split_merge_inheritance_control
#print axioms issued_boolean_control
end Sal.MRDTs.Instances.NotionCoreRichSequential.SPOT
