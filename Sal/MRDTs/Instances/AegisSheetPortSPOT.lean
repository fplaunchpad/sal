import Sal.MRDTs.Instances.AegisSheetMaterialisedConverse
import Sal.MRDTs.Instances.AegisSheetMaterialisedRetirement

/-! Executable fixtures, separated from the production proof dependencies.
The legacy matrix fixtures test raw updates, not issuance equivalence. -/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised
open Sal.MRDTs.Foundation

/-! ## Fixtures: the union model's published-matrix cases replayed through
three-way merges

Every state below is built by `mupdate` from the empty sheet, and concurrent
operations are combined with `mmerge` at their common base. Expected values
are the hand-derived ones of the union-model SPOTs. -/

def mAxis (time replica : Nat) (kind : AxisUpdateKind) (axis : Axis) (id : StableId)
    (before after : Option Position) (kills : Finset Timestamp) : MEvent :=
  (time, replica, ⟨.direct (.axis ⟨kind, axis, id, before, after⟩), kills⟩)

def mCell (time replica : Nat) (row column : StableId) (before after : Finset CellValue)
    (overwrites : Finset Nat) : MEvent :=
  (time, replica, ⟨.direct (.cell ⟨row, column, before, after, overwrites⟩), ∅⟩)

def mRange (time replica : Nat) (id : RangeId) (before after : Option RangeSpec)
    (overwrites : Finset Nat) : MEvent :=
  (time, replica, ⟨.direct (.range ⟨id, before, after, overwrites⟩), ∅⟩)

/-- Undo carries the inverse action; an inverse that removes an axis names
the tokens it kills. -/
def mUndo (time replica : Nat) (target : Timestamp) (inverse : Action)
    (kills : Finset Timestamp) : MEvent :=
  (time, replica, ⟨.undo target inverse, kills⟩)

def mfold (es : List MEvent) : MState := es.foldl mupdate MState.empty

def base : MState := mfold
  [mAxis 1 0 .insert .row r0 none (some 10) ∅,
   mAxis 2 0 .insert .column c0 none (some 10) ∅,
   mCell 3 0 r0 c0 ∅ {0} ∅]

/-- Table 3: a concurrent edit defeats row removal and preserves its value. -/
def removeR0 : MEvent := mAxis 4 1 .remove .row r0 (some 10) none {1, 3}
def editR0 : MEvent := mCell 5 2 r0 c0 {0} {1} {3}
def editRemove : MState := mmerge base (mupdate base removeR0) (mupdate base editR0)

example : mLive editRemove .row r0 = true := by native_decide
example : mCellValues editRemove r0 c0 = {1} := by native_decide
/-- FAIL control: remove-wins is not the published outcome. -/
example : ¬ (mLive editRemove .row r0 = false) := by native_decide

/-- A causally later removal wins: it names the edit's token. -/
def laterRemove : MEvent := mAxis 6 1 .remove .row r0 (some 10) none {1, 3, 5}
example : mLive (mupdate (mupdate base editR0) laterRemove) .row r0 = false := by
  native_decide

/-- Table 3: concurrent writes retain both values. -/
def editA : MEvent := mCell 4 1 r0 c0 {0} {1} {3}
def editB : MEvent := mCell 5 2 r0 c0 {0} {2} {3}
def conflict : MState := mmerge base (mupdate base editA) (mupdate base editB)
example : mCellValues conflict r0 c0 = {1, 2} := by native_decide
example : ¬ (mCellValues conflict r0 c0 = {2}) := by native_decide

/-- Table 4: undoing one side of a conflict restores the old value without
overwriting the concurrent remote edit. -/
def undoA : MEvent := mUndo 6 1 4 (.cell ⟨r0, c0, {1}, {0}, {4}⟩) ∅
example : mCellValues (mupdate conflict undoA) r0 c0 = {0, 2} := by native_decide
example : ¬ (mCellValues (mupdate conflict undoA) r0 c0 = {0}) := by native_decide

/-- Table 3: a move defeats concurrent removal and chooses its new position. -/
def moveR0 : MEvent := mAxis 5 2 .move .row r0 (some 10) (some 30) ∅
def moveRemove : MState := mmerge base (mupdate base removeR0) (mupdate base moveR0)
example : mLive moveRemove .row r0 = true := by native_decide
example : mPositions moveRemove .row r0 = {30} := by native_decide

/-- Concurrent move and edit preserve both effects. -/
def moveEdit : MState := mmerge base (mupdate base editR0) (mupdate base moveR0)
example : mPositions moveEdit .row r0 = {30} := by native_decide
example : mCellValues moveEdit r0 c0 = {1} := by native_decide

/-- Concurrent moves use the later timestamp and never duplicate the id. -/
def moveEarlier : MEvent := mAxis 4 1 .move .row r0 (some 10) (some 20) ∅
def twoMoves : MState := mmerge base (mupdate base moveEarlier) (mupdate base moveR0)
example : mPositions twoMoves .row r0 = {30} := by native_decide
example : (mLiveIds twoMoves .row).card = 1 := by native_decide

/-- An insertion keeps its minted gap position when its left neighbour moves. -/
def insertR1 : MEvent := mAxis 4 1 .insert .row r1 none (some 15) ∅
def insertMove : MState := mmerge base (mupdate base insertR1) (mupdate base moveR0)
example : mPositions insertMove .row r1 = {15} := by native_decide
example : mPositions insertMove .row r0 = {30} := by native_decide
example : (mLiveIds insertMove .row).card = 2 := by native_decide

/-- Two concurrent inserts at one gap keep both stable ids. -/
def insertR12 : MEvent := mAxis 5 2 .insert .row 12 none (some 15) ∅
example : (mLiveIds (mmerge base (mupdate base insertR1) (mupdate base insertR12)) .row).card = 3 := by
  native_decide

/-- An adjacent insertion survives while the original row is removed. -/
def insertRemove : MState :=
  mmerge base (mupdate base insertR1) (mupdate base (mAxis 5 2 .remove .row r0 (some 10) none {1, 3}))
example : mLive insertRemove .row r0 = false := by native_decide
example : mLive insertRemove .row r1 = true := by native_decide

/-- Undoing an insert removes only the inserted stable id. -/
def undoInsertR1 : MEvent :=
  mUndo 6 1 4 (.axis ⟨.restore, .row, r1, some 15, none⟩) {4}
example : mLive (mupdate (mupdate base insertR1) undoInsertR1) .row r1 = false := by
  native_decide
example : mLive (mupdate (mupdate base insertR1) undoInsertR1) .row r0 = true := by
  native_decide

/-- Undoing a remove restores its previous stable position. -/
def undoRemoveR0 : MEvent :=
  mUndo 6 1 4 (.axis ⟨.restore, .row, r0, none, some 10⟩) ∅
example : mLive (mupdate (mupdate base removeR0) undoRemoveR0) .row r0 = true := by
  native_decide
example : mPositions (mupdate (mupdate base removeR0) undoRemoveR0) .row r0 = {10} := by
  native_decide

/-- Two concurrent removals agree on absence. -/
example : mLive (mmerge base (mupdate base removeR0)
    (mupdate base (mAxis 5 2 .remove .row r0 (some 10) none {1, 3}))) .row r0 = false := by
  native_decide

/-- Undoing a move restores its old position and retains a concurrent edit. -/
def moveBy1 : MEvent := mAxis 4 1 .move .row r0 (some 10) (some 30) ∅
def editBy2 : MEvent := mCell 5 2 r0 c0 {0} {2} {3}
def undoMoveBy1 : MEvent := mUndo 6 1 4 (.axis ⟨.restore, .row, r0, some 30, some 10⟩) ∅
def undoMove : MState := mupdate (mmerge base (mupdate base moveBy1) (mupdate base editBy2)) undoMoveBy1
example : mPositions undoMove .row r0 = {10} := by native_decide
example : mCellValues undoMove r0 c0 = {2} := by native_decide

/-- Table 4: undoing a move restores the moved stable id without changing a
concurrent insertion's stable position. -/
def insertR1At20 : MEvent := mAxis 5 2 .insert .row r1 none (some 20) ∅
def table4MoveInsertUndo : MState :=
  mupdate (mmerge base (mupdate base moveBy1) (mupdate base insertR1At20)) undoMoveBy1
example : mPositions table4MoveInsertUndo .row r0 = {10} := by native_decide
example : mPositions table4MoveInsertUndo .row r1 = {20} := by native_decide

/-- Table 4: undoing one of two concurrent moves restores the original stable
position. -/
def moveBy2 : MEvent := mAxis 5 2 .move .row r0 (some 10) (some 40) ∅
example : mPositions (mupdate (mmerge base (mupdate base moveBy1) (mupdate base moveBy2))
    undoMoveBy1) .row r0 = {10} := by native_decide

/-! ### Figure 1 ranges -/

def rangedBase : MState := mfold
  [mAxis 1 0 .insert .row r0 none (some 10) ∅,
   mAxis 2 0 .insert .column c0 none (some 10) ∅,
   mCell 3 0 r0 c0 ∅ {0} ∅,
   mAxis 4 0 .insert .row r1 none (some 20) ∅,
   mAxis 5 0 .insert .column c1 none (some 20) ∅,
   mRange 6 0 30 none (some rangeSpec) ∅]

example : mRangeValues rangedBase 30 = {rangeSpec} := by native_decide
example : mResolveRange rangedBase rangeSpec = some ⟨r0, r1, c0, c1⟩ := by native_decide

/-- Removing the first border attaches it to the next live row. -/
example : mResolveRange (mupdate rangedBase
    (mAxis 7 1 .remove .row r0 (some 10) none {1, 3})) rangeSpec = some ⟨r1, r1, c0, c1⟩ := by
  native_decide

/-- Moving the last endpoint before the first crosses the range. -/
example : mResolveRange (mupdate rangedBase
    (mAxis 7 1 .move .row r1 (some 20) (some 5) ∅)) rangeSpec = none := by native_decide

/-- Removing an interior row preserves both anchored endpoints. -/
def wideBase : MState := mfold
  [mAxis 1 0 .insert .row r0 none (some 10) ∅,
   mAxis 2 0 .insert .column c0 none (some 10) ∅,
   mCell 3 0 r0 c0 ∅ {0} ∅,
   mAxis 4 0 .insert .row r1 none (some 20) ∅,
   mAxis 5 0 .insert .column c1 none (some 20) ∅,
   mAxis 6 0 .insert .row r2 none (some 30) ∅,
   mRange 7 0 31 none (some wideRangeSpec) ∅]
def interiorDeleted : MState := mupdate wideBase (mAxis 8 1 .remove .row r1 (some 20) none {4})
example : mResolveRange interiorDeleted wideRangeSpec = some ⟨r0, r2, c0, c1⟩ := by native_decide
example : (mLiveIds interiorDeleted .row).card = 2 := by native_decide

/-- The retention witness: the removed endpoint's last position decides the
resolution (Counterexample 5.1 of the materialised-merge note). -/
def spanBase : MState := mfold
  [mAxis 1 0 .insert .row r0 none (some 10) ∅,
   mAxis 2 0 .insert .row r1 none (some 20) ∅,
   mAxis 3 0 .insert .row r2 none (some 30) ∅,
   mAxis 4 0 .insert .column c0 none (some 10) ∅,
   mRange 5 0 40 none (some ⟨r0, r2, c0, c0⟩) ∅]
def spanPlain : MState := mupdate spanBase (mAxis 6 0 .remove .row r0 (some 10) none {1})
def spanMoved : MState := mupdate (mupdate spanBase (mAxis 6 0 .move .row r0 (some 10) (some 25) ∅))
  (mAxis 7 0 .remove .row r0 (some 25) none {1, 6})
example : mLiveIds spanPlain .row = mLiveIds spanMoved .row := by native_decide
example : mResolveRange spanPlain ⟨r0, r2, c0, c0⟩ = some ⟨r1, r2, c0, c0⟩ := by native_decide
example : mResolveRange spanMoved ⟨r0, r2, c0, c0⟩ = some ⟨r2, r2, c0, c0⟩ := by native_decide

/-- Range removal followed by a fresh recreation is visible again. -/
example : mRangeValues (mupdate (mupdate rangedBase (mRange 7 0 30 (some rangeSpec) none {6}))
    (mRange 8 0 30 none (some rangeSpec) {7})) 30 = {rangeSpec} := by native_decide

/-! ### Purge under D2 -/

/-- A purge deletes the covered versions; a write concurrent with it and below
its cutoff survives and revives the axis. -/
def purged : MState := mupdate (mupdate base removeR0)
  (4, 0, ⟨.direct (.purge ⟨4, {(r0, c0)}, {(3, (r0, c0))}, {0, 1, 2}⟩), ∅⟩)
example : (purged.cells.filter fun v => v.1 = r0 ∧ v.2.1 = c0) = ∅ := by native_decide
def concurrentLowWrite : MEvent := mCell 4 2 r0 c0 {0} {9} {3}
def purgeVsWrite : MState := mmerge base purged (mupdate base concurrentLowWrite)
example : mLive purgeVsWrite .row r0 = true := by native_decide
example : mCellValues purgeVsWrite r0 c0 = {9} := by native_decide

/-! ### Canonical state agrees with the fold on a fixture -/

def refBase : Finset Event := {baseRow, baseColumn, baseCell}
example : canon refBase = base := by native_decide
example : canon (insert concurrentEdit (insert concurrentRemove refBase)) = editRemove := by
  native_decide

/-! ## Validation-round regressions (kernel reduction, no native tactic) -/
namespace Audit
def ins : Event := axisEvent 1 0 ∅ .insert .row 10 none (some 10)
def mov : Event := axisEvent 2 1 {1} .move .row 10 (some 10) (some 20)
def rem : Event := axisEvent 3 0 {1} .remove .row 10 (some 10) none
def past : Finset Event := {ins}
def merged : Finset Event := {ins, mov, rem}
def ms := mmerge (canon past) (mupdate (canon past) (toM past mov))
  (mupdate (canon past) (toM past rem))

theorem three_event_issuance : applicable ins ∅ ∧ applicable mov past ∧ applicable rem past := by decide
example : axisTokenRemoved merged .row 10 1 = true ∧
    axisTokenRemoved merged .row 10 2 = false := by decide
example : liveAxisTokens merged .row 10 = {2} := by decide
example : ms.tokens = {(Axis.row, 10, 2)} := by decide
example : mupdate (canon ({ins, mov} : Finset Event)) (toM past rem) = ms := by decide
theorem three_event_merge : ms = canon merged := by decide

def ua : Event := cellEvent 4 1 {1,2,3} r0 c0 {0} {1} {3}
def ub : Event := cellEvent 5 2 {1,2,3} r0 c0 {0} {2} {3}
def undoPast : Finset Event := {baseRow, baseColumn, baseCell, ua, ub}
def un : Event := (6, 1, ⟨{1,2,3,4,5}, .undo 4 (.cell ⟨r0,c0,{1},{0},{4}⟩)⟩)
theorem union_accepts_selective_undo : applicable un undoPast := by decide
theorem port_rejects_selective_undo : ¬ mApplicable (toM undoPast un) (canon undoPast) := by decide

def dead := mupdate (canon past) (toM past rem)
def reins := mAxis 4 0 .insert .row 10 none (some 30) ∅
theorem retirement_rejects_reuse : ¬ mApplicable reins (retire dead) ∧ ¬ mApplicable reins dead := by decide

/-- Mutation control: testing only known would admit reuse after collection. -/
theorem known_only_freshness_refuted :
    (Axis.row, 10) ∉ (retire dead).known ∧ (Axis.row, 10) ∈ dead.known := by decide

def freshInsert := mAxis 4 0 .insert .row 11 none (some 30) ∅
theorem fresh_insert_accepted : mApplicable freshInsert (retire dead) := by decide
example : (retire dead).pos = dead.pos := rfl

def forged := mUndo 4 0 999 (.axis ⟨.restore, .row, 99, none, some 99⟩) ∅
example : mApplicable forged MState.empty := by decide
example : ¬ applicable (liftAt ∅ forged) ∅ := by decide

def insOther : Event := axisEvent 1 1 ∅ .insert .row 10 none (some 10)
theorem same_state_different_undo_authority :
    canon ({ins} : Finset Event) = canon ({insOther} : Finset Event) ∧
    validUndo {ins} 0 1 (inverseFor ins) = true ∧
    validUndo {insOther} 0 1 (inverseFor ins) = false := by decide

def badPurge : Purge := ⟨0, ∅, {(3, (r0,c0))}, ∅⟩
def livePurge : MEvent := (4, 7, ⟨.direct (.purge badPurge), ∅⟩)
theorem port_rejects_live_invalid_purge :
    ¬ mApplicable livePurge (canon ({baseRow,baseColumn,baseCell} : Finset Event)) ∧
    purgeApplicable {baseRow,baseColumn,baseCell} 7 badPurge = false := by decide


def goodPurge : Purge := ⟨3, {(r0,c0)}, {(3,(r0,c0))}, ∅⟩
def deadCell := mupdate base removeR0
def purgeByAnyReplica : MEvent := (6, 7, ⟨.direct (.purge goodPurge), ∅⟩)
theorem valid_dead_purge_accepted : mApplicable purgeByAnyReplica deadCell := by decide

def liveValidPurge : MEvent := (6, 7, ⟨.direct (.purge goodPurge), ∅⟩)
theorem valid_live_purge_rejected : ¬ mApplicable liveValidPurge base := by decide

#print axioms retirement_rejects_reuse
#print axioms known_only_freshness_refuted
#print axioms valid_dead_purge_accepted

/- Bounded guard regression: five fixture states, 32 payloads, seven event
forms. The known-only negative control above must fail independently. -/
#eval show IO Unit from do
  let states := [MState.empty, base, deadCell, conflict, purgeVsWrite]
  let mut checked := 0
  for s in states do
    for i in List.range 32 do
      let events := [mAxis 1000 0 .insert .row i none (some i) ∅,
        mAxis 1000 0 .move .row r0 (some 10) (some i) ∅,
        mAxis 1000 0 .remove .row r0 (some 10) none {i},
        mCell 1000 0 r0 c0 {0} {i} {3},
        mRange 1000 0 i none none ∅,
        mUndo 1000 0 i (.axis ⟨.restore, .row, i, none, some i⟩) ∅,
        purgeByAnyReplica]
      for e in events do
        unless decide (mApplicable e (retire s)) == decide (mApplicable e s) do
          throw (IO.userError "retirement changed issuance")
        checked := checked + 1
  IO.println s!"Retirement issuance regression: {checked} comparisons passed."

end Audit

end Sal.MRDTs.Instances.AegisSheet.Materialised
