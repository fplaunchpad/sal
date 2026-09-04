import Sal.MRDTs.Instances.AegisSheet

/-!
# AegisSheet retention proof-oriented tests

Finite executions of the current model that fix what a representation must
retain about removed rows and columns, and how the current undo rule interacts
with removal. Expected values are hand-derived from the published policies:
range endpoints resolve through a dead identifier's last position, a
concurrent write or move defeats a removal and places the row at its latest
position, and an undo is an ordinary cell event.

Every block has a PASS half establishing the intended observation on a legal
trace and a FAIL half pinning the tempting wrong answer: eager re-anchoring,
remove-wins, and the no-revival reading of undo.
-/

namespace Sal.MRDTs.Instances.AegisSheet.RetentionSPOT

open Sal.MRDTs.Foundation

/-! ## Range resolution reads a removed endpoint's last position

Rows `r0`, `r1`, `r2` at positions `10`, `20`, `30`, one column, and a range
anchored at `(r0, r2)`. Removing `r0` directly and moving it to `25` before
removing it leave the same live sheet but resolve the range differently. -/

def rowA : Event := axisEvent 1 0 ∅ .insert .row r0 none (some 10)
def rowB : Event := axisEvent 2 0 {1} .insert .row r1 none (some 20)
def rowC : Event := axisEvent 3 0 {1, 2} .insert .row r2 none (some 30)
def colA : Event := axisEvent 4 0 {1, 2, 3} .insert .column c0 none (some 10)
def spanSpec : RangeSpec := ⟨r0, r2, c0, c0⟩
def addSpan : Event := rangeEvent 5 0 {1, 2, 3, 4} 40 none (some spanSpec) ∅
def sheet : Finset Event := {rowA, rowB, rowC, colA, addSpan}

def removeFirst : Event :=
  axisEvent 6 0 {1, 2, 3, 4, 5} .remove .row r0 (some 10) none
def moveFirst : Event :=
  axisEvent 6 0 {1, 2, 3, 4, 5} .move .row r0 (some 10) (some 25)
def removeMoved : Event :=
  axisEvent 7 0 {1, 2, 3, 4, 5, 6} .remove .row r0 (some 25) none

def worldPlain : Finset Event := insert removeFirst sheet
def worldMoved : Finset Event := insert removeMoved (insert moveFirst sheet)

/-- Both histories are legal at every step. -/
example : applicableB removeFirst sheet = true := by native_decide
example : applicableB moveFirst sheet = true := by native_decide
example : applicableB removeMoved (insert moveFirst sheet) = true := by native_decide

/-- The live sheets coincide: same live rows, same positions, same range. -/
example : liveAxisIds worldPlain .row = liveAxisIds worldMoved .row := by native_decide
example : axisPositions worldPlain .row r1 = axisPositions worldMoved .row r1 := by
  native_decide
example : axisPositions worldPlain .row r2 = axisPositions worldMoved .row r2 := by
  native_decide
example : rangeValues worldPlain 40 = rangeValues worldMoved 40 := by native_decide

/-- PASS: the removed first endpoint attaches to the next live row below its
last position, which differs between the two histories. -/
example : resolveRange worldPlain spanSpec = some ⟨r1, r2, c0, c0⟩ := by native_decide
example : resolveRange worldMoved spanSpec = some ⟨r2, r2, c0, c0⟩ := by native_decide

/-- FAIL: a representation that forgets the removed row's last position
cannot answer both. -/
theorem dead_position_load_bearing_for_ranges :
    resolveRange worldPlain spanSpec ≠ resolveRange worldMoved spanSpec := by
  native_decide

/-! ## Eager re-anchoring disagrees with lazy resolution

Branch A removes `r0`; branch B concurrently inserts `r3` at position `15`,
between the dead endpoint and its former successor. -/

def r3 : StableId := 13
def spanInsert : Event := axisEvent 7 2 {1, 2, 3, 4, 5} .insert .row r3 none (some 15)
def spanMerged : Finset Event := insert spanInsert (insert removeFirst sheet)

example : applicableB spanInsert sheet = true := by native_decide

/-- PASS: lazy resolution picks the concurrently inserted row. -/
example : resolveRange spanMerged spanSpec = some ⟨r3, r2, c0, c0⟩ := by native_decide

/-- FAIL: rewriting the range to `r1` when `r0` was removed is not the
published semantics. -/
theorem eager_reanchoring_refuted :
    resolveRange spanMerged spanSpec ≠ some ⟨r1, r2, c0, c0⟩ := by native_decide

/-! ## Update-wins revival reads the removed row's last position

From the shared base (row `r0` at `10`, column `c0`, one cell write), branch
A either moves `r0` to `52` and removes it, or removes it in place. Both
branch states show the row dead. A concurrent write on branch B revives it,
at `52` in the first case and at `10` in the second. -/

def moveAway : Event := axisEvent 4 1 {1, 2, 3} .move .row r0 (some 10) (some 52)
def removeAfterMove : Event :=
  axisEvent 5 1 {1, 2, 3, 4} .remove .row r0 (some 52) none
def removeInPlace : Event := axisEvent 4 1 {1, 2, 3} .remove .row r0 (some 10) none
def branchMoved : Finset Event := insert removeAfterMove (insert moveAway base)
def branchPlain : Finset Event := insert removeInPlace base
def revivingEdit : Event := cellEvent 6 2 {1, 2, 3} r0 c0 {0} {7} {3}
def mergedMoved : Finset Event := insert revivingEdit branchMoved
def mergedPlain : Finset Event := insert revivingEdit branchPlain

example : applicableB moveAway base = true := by native_decide
example : applicableB removeAfterMove (insert moveAway base) = true := by native_decide
example : applicableB removeInPlace base = true := by native_decide
example : applicableB revivingEdit base = true := by native_decide

/-- Both branch states have the same live sheet: the row is dead. -/
example : axisLive branchMoved .row r0 = false := by native_decide
example : axisLive branchPlain .row r0 = false := by native_decide
example : liveAxisIds branchMoved .row = liveAxisIds branchPlain .row := by native_decide
example : cellValues branchMoved r0 c0 = cellValues branchPlain r0 c0 := by native_decide

/-- PASS: the concurrent write revives the row in both merges, at the
position the removing branch alone knew. -/
example : axisLive mergedMoved .row r0 = true := by native_decide
example : axisLive mergedPlain .row r0 = true := by native_decide
example : axisPositions mergedMoved .row r0 = {52} := by native_decide
example : axisPositions mergedPlain .row r0 = {10} := by native_decide
example : cellValues mergedMoved r0 c0 = {7} := by native_decide

/-- FAIL: the two merges require different positions, although the removing
branch's live sheets were identical. -/
theorem dead_position_load_bearing_for_revival :
    axisPositions mergedMoved .row r0 ≠ axisPositions mergedPlain .row r0 := by
  native_decide

/-- FAIL: remove-wins is not the published outcome. -/
theorem remove_wins_refuted : ¬ (axisLive mergedMoved .row r0 = false) := by
  native_decide

/-! ## Undo of an earlier write revives a causally later removal

In the current model an inverse cell write is a cell event and therefore a
keep token. Removing the row and then undoing an older write into it is legal
on one replica and makes the row live again with an empty cell. This block
documents the current semantics; decision D1 of the materialised-merge note
restricts the inverse to live axes. -/

def removeRow : Event := axisEvent 4 0 {1, 2, 3} .remove .row r0 (some 10) none
def removedBase : Finset Event := insert removeRow base
def undoOldWrite : Event := undoCellEvent 5 0 {1, 2, 3, 4} baseCell
def revivedByUndo : Finset Event := insert undoOldWrite removedBase

example : applicableB removeRow base = true := by native_decide
/-- The undo is legal: own event, target observed, exact inverse. -/
example : applicableB undoOldWrite removedBase = true := by native_decide

/-- PASS: before the undo the row is dead; after it the row is live at its
last position with no cell content. -/
example : axisLive removedBase .row r0 = false := by native_decide
example : axisLive revivedByUndo .row r0 = true := by native_decide
example : axisPositions revivedByUndo .row r0 = {10} := by native_decide
example : cellValues revivedByUndo r0 c0 = ∅ := by native_decide

/-- FAIL: the no-revival reading of undo does not describe the current
model. -/
theorem undo_revives_later_removal : ¬ (axisLive revivedByUndo .row r0 = false) := by
  native_decide

#print axioms dead_position_load_bearing_for_ranges
#print axioms eager_reanchoring_refuted
#print axioms dead_position_load_bearing_for_revival
#print axioms remove_wins_refuted
#print axioms undo_revives_later_removal

end Sal.MRDTs.Instances.AegisSheet.RetentionSPOT
