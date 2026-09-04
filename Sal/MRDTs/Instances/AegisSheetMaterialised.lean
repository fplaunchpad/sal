import Sal.MRDTs.Instances.AegisSheet

/-!
# AegisSheet with a materialised state and a three-way merge

A second encoding of the AegisSheet intent model. The state holds live keep
tokens, one latest-position register per axis identifier, active cell
versions, and active range versions. Updates delete what they supersede: a
removal names the tokens it kills, a write names the versions it overwrites,
a purge names the versions it covers. Merge is componentwise: the
observed-remove rule `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)` for sets and
last-writer-wins for registers. Nothing carries a causal timestamp set; the
merge base supplies what an event's causal past supplied in the union model.

Purge follows decision D2: a marker masks exactly the versions it covered, so
a write concurrent with the marker survives.

This file contains the executable signature, the canonical state of a
reference event set, the fixture suite of the union model replayed through
three-way merges, and the statements of the theorems the port owes. The
statements are `Prop`-valued definitions with no proofs.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs.Foundation

/-! ## Operations and state -/

/-- An operation: a command and, for a removal, the live keep tokens the
issuer observed for the removed identifier. -/
structure MOp where
  command : Command
  kills : Finset Timestamp
deriving DecidableEq

abbrev MEvent := Op MOp

def MEvent.action (e : MEvent) : Action := e.2.2.command.effect

abbrev TokenEntry := Axis × StableId × Timestamp
abbrev PosEntry := Axis × StableId × Timestamp × Position
abbrev CellEntry := StableId × StableId × Timestamp × Finset CellValue
abbrev RangeEntry := RangeId × Timestamp × Option RangeSpec

structure MState where
  known : Finset (Axis × StableId)
  tokens : Finset TokenEntry
  pos : Finset PosEntry
  cells : Finset CellEntry
  ranges : Finset RangeEntry
deriving DecidableEq

def MState.empty : MState := ⟨∅, ∅, ∅, ∅, ∅⟩

def posKey (x : PosEntry) : Axis × StableId := (x.1, x.2.1)
def posTs (x : PosEntry) : Timestamp := x.2.2.1
def posVal (x : PosEntry) : Position := x.2.2.2

/-- Install a position candidate unless a later candidate for the same
identifier is already present. -/
def posInsert (pos : Finset PosEntry) (axis : Axis) (id : StableId)
    (t : Timestamp) (p : Position) : Finset PosEntry :=
  if ∃ x ∈ pos, posKey x = (axis, id) ∧ t < posTs x then pos
  else insert (axis, id, t, p) (pos.filter fun x => posKey x ≠ (axis, id))

/-- Last-writer-wins over the three inputs, one entry per identifier. -/
def posMerge (l a b : Finset PosEntry) : Finset PosEntry :=
  (l ∪ a ∪ b).filter fun x => ∀ y ∈ l ∪ a ∪ b, posKey y = posKey x → posTs y ≤ posTs x

def mvr {α : Type} [DecidableEq α] (l a b : Finset α) : Finset α :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

def mupdate (s : MState) (e : MEvent) : MState :=
  match e.action with
  | .axis u =>
      match u.after with
      | some p =>
          { s with known := insert (u.axis, u.id) s.known
                   tokens := insert (u.axis, u.id, e.1) s.tokens
                   pos := posInsert s.pos u.axis u.id e.1 p }
      | none =>
          { s with known := insert (u.axis, u.id) s.known
                   tokens := s.tokens.filter fun x =>
                     ¬ (x.1 = u.axis ∧ x.2.1 = u.id ∧ x.2.2 ∈ e.2.2.kills) }
  | .cell u =>
      { s with tokens := insert (Axis.row, u.row, e.1)
                 (insert (Axis.column, u.column, e.1) s.tokens)
               cells := insert (u.row, u.column, e.1, u.after)
                 (s.cells.filter fun v =>
                   ¬ (v.1 = u.row ∧ v.2.1 = u.column ∧ v.2.2.1 ∈ u.overwrites)) }
  | .range u =>
      { s with ranges := insert (u.id, e.1, u.after)
                 (s.ranges.filter fun v => ¬ (v.1 = u.id ∧ v.2.1 ∈ u.overwrites)) }
  | .purge m =>
      { s with cells := s.cells.filter fun v => (v.2.2.1, (v.1, v.2.1)) ∉ m.covered }

def mmerge (l a b : MState) : MState :=
  ⟨l.known ∪ a.known ∪ b.known,
   mvr l.tokens a.tokens b.tokens,
   posMerge l.pos a.pos b.pos,
   mvr l.cells a.cells b.cells,
   mvr l.ranges a.ranges b.ranges⟩

/-! ## Observation -/

def mLive (s : MState) (axis : Axis) (id : StableId) : Bool :=
  decide ((axis, id) ∈ s.known) && decide (∃ x ∈ s.tokens, x.1 = axis ∧ x.2.1 = id)

def mLiveIds (s : MState) (axis : Axis) : Finset StableId :=
  (s.known.filter fun k => k.1 = axis ∧ mLive s axis k.2 = true).image Prod.snd

def mPositions (s : MState) (axis : Axis) (id : StableId) : Finset Position :=
  (s.pos.filter fun x => posKey x = (axis, id)).image posVal

def mCellValues (s : MState) (row column : StableId) : Finset CellValue :=
  if mLive s .row row && mLive s .column column then
    (s.cells.filter fun v => v.1 = row ∧ v.2.1 = column).biUnion fun v => v.2.2.2
  else ∅

def mRangeValues (s : MState) (id : RangeId) : Finset RangeSpec :=
  (s.ranges.filter fun v => v.1 = id).biUnion fun v => optionFinset v.2.2

def mview (s : MState) : View where
  rows := mLiveIds s .row
  columns := mLiveIds s .column
  rowPosition := mPositions s .row
  columnPosition := mPositions s .column
  cell := mCellValues s
  range := mRangeValues s

def mPositionOption (s : MState) (axis : Axis) (id : StableId) : Option Position :=
  let ps := mPositions s axis id
  if h : ps.Nonempty then some (ps.min' h) else none

def mLivePositions (s : MState) (axis : Axis) : Finset Position :=
  (mLiveIds s axis).biUnion fun id => mPositions s axis id

def mIdAtPosition (s : MState) (axis : Axis) (position : Position) : Option StableId :=
  minNat? ((mLiveIds s axis).filter fun id => position ∈ mPositions s axis id)

def mResolveFirst (s : MState) (axis : Axis) (endpoint : StableId) : Option StableId :=
  if mLive s axis endpoint then some endpoint else
    match mPositionOption s axis endpoint with
    | none => none
    | some oldPosition =>
        (minNat? ((mLivePositions s axis).filter
          fun candidate => decide (oldPosition < candidate))).bind
            (mIdAtPosition s axis)

def mResolveLast (s : MState) (axis : Axis) (endpoint : StableId) : Option StableId :=
  if mLive s axis endpoint then some endpoint else
    match mPositionOption s axis endpoint with
    | none => none
    | some oldPosition =>
        (maxNat? ((mLivePositions s axis).filter
          fun candidate => decide (candidate < oldPosition))).bind
            (mIdAtPosition s axis)

def mResolveRange (s : MState) (spec : RangeSpec) : Option ResolvedRange := do
  let firstRow ← mResolveFirst s .row spec.firstRow
  let lastRow ← mResolveLast s .row spec.lastRow
  let firstColumn ← mResolveFirst s .column spec.firstColumn
  let lastColumn ← mResolveLast s .column spec.lastColumn
  let firstRowPosition ← mPositionOption s .row firstRow
  let lastRowPosition ← mPositionOption s .row lastRow
  let firstColumnPosition ← mPositionOption s .column firstColumn
  let lastColumnPosition ← mPositionOption s .column lastColumn
  if firstRowPosition ≤ lastRowPosition &&
      firstColumnPosition ≤ lastColumnPosition then
    some ⟨firstRow, lastRow, firstColumn, lastColumn⟩
  else none

/-! ## The signature -/

def M : MRDTSig where
  State := MState
  dec_state := inferInstance
  init := MState.empty
  AppOp := MOp
  dec_op := inferInstance
  Query := Unit
  Value := View
  update := mupdate
  query s _ := mview s
  merge := mmerge

theorem M_rc_either : ∀ o₁ o₂ : Op M.AppOp,
    M.toUpdateSig.replayOrder o₁ o₂ = RcRes.Either := fun _ _ => rfl

/-! ## Canonical state of a reference event set

`canon E` is the materialised state a union-model history `E` denotes. It is
the representation relation between the two encodings: `known`, tokens,
registers, and versions are each read off `E` with the declarative
definitions of the union model, except that overwriting by a purge follows
decision D2 (a marker masks exactly the versions it covered). -/

/-- D2 overwriting: named by a later write, or covered by a marker. -/
def cellOverwrittenD2 (events : Finset Event) (candidate : Event) : Bool :=
  Finset.fold (· || ·) false (fun later =>
      match later.action with
      | .cell u => decide (candidate.1 ∈ u.overwrites)
      | .purge marker => match cellUpdate? candidate with
          | some update =>
              decide ((candidate.1, (update.row, update.column)) ∈ marker.covered)
          | none => false
      | _ => false) events

def axisKeys (events : Finset Event) : Finset (Axis × StableId) :=
  events.biUnion fun e =>
    match e.action with
    | .axis u => {(u.axis, u.id)}
    | .cell u => {(Axis.row, u.row), (Axis.column, u.column)}
    | _ => ∅

def canonKnown (events : Finset Event) : Finset (Axis × StableId) :=
  events.biUnion fun e =>
    match axisUpdate? e with
    | some u => {(u.axis, u.id)}
    | none => ∅

def canonTokens (events : Finset Event) : Finset TokenEntry :=
  (axisKeys events).biUnion fun k =>
    (liveAxisTokens events k.1 k.2).image fun t => (k.1, k.2, t)

def canonPos (events : Finset Event) : Finset PosEntry :=
  events.biUnion fun e =>
    match axisUpdate? e with
    | some u =>
        match u.after with
        | some p =>
            if laterAxisCandidate events u.axis u.id e then ∅
            else {(u.axis, u.id, e.1, p)}
        | none => ∅
    | none => ∅

def canonCells (events : Finset Event) : Finset CellEntry :=
  events.biUnion fun e =>
    match cellUpdate? e with
    | some u => if cellOverwrittenD2 events e then ∅ else {(u.row, u.column, e.1, u.after)}
    | none => ∅

def canonRanges (events : Finset Event) : Finset RangeEntry :=
  events.biUnion fun e =>
    match rangeUpdate? e with
    | some u => if rangeOverwritten events e then ∅ else {(u.id, e.1, u.after)}
    | none => ∅

def canon (events : Finset Event) : MState :=
  ⟨canonKnown events, canonTokens events, canonPos events, canonCells events,
   canonRanges events⟩

/-- The live keep tokens a removal issued at `events` kills. -/
def killsOf (events : Finset Event) (e : Event) : Finset Timestamp :=
  match e.action with
  | .axis u => if u.after.isNone then liveAxisTokens events u.axis u.id else ∅
  | _ => ∅

/-- Erase a union-model event to a materialised operation at its issuing
state: drop the causal timestamp set, attach the killed tokens. -/
def toM (events : Finset Event) (e : Event) : MEvent :=
  (e.1, e.2.1, ⟨e.2.2.command, killsOf events e⟩)

/-! ## Owed theorems, as statements

Each is a `Prop`; none is proved here. They are the mechanization targets
listed in `docs/aegissheet-materialised/plan.md`. -/

/-- Observation equivalence on purge-free histories, against the union
model's `view`. With purges the reference is the D2 view. -/
def ObservationEquivalence : Prop :=
  ∀ events : Finset Event, (∀ e ∈ events, purge? e = none) →
    mview (canon events) = view events

/-- Representation is preserved by an honest update. -/
def UpdatePreservesCanon : Prop :=
  ∀ (events : Finset Event) (e : Event), applicable e events →
    mupdate (canon events) (toM events e) = canon (insert e events)

/-- Honesty of a replay context for the materialised signature: every named
token, overwritten version, and covered version was issued `vis`-before the
operation naming it. -/
structure Honest (C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig) : Prop where
  kills_seen : ∀ e ∈ C.events, ∀ u : AxisUpdate,
    MEvent.action e = Action.axis u → u.after = none →
    ∀ t ∈ e.2.2.kills, ∃ k ∈ C.events, k.1 = t ∧ C.vis k e ∧
      ((∃ v : AxisUpdate, MEvent.action k = Action.axis v ∧
          v.axis = u.axis ∧ v.id = u.id ∧ v.after.isSome) ∨
       (∃ w : CellUpdate, MEvent.action k = Action.cell w ∧
          (match u.axis with | .row => w.row | .column => w.column) = u.id))
  overwrites_seen : ∀ e ∈ C.events, ∀ u : CellUpdate,
    MEvent.action e = Action.cell u →
    ∀ t ∈ u.overwrites, ∃ k ∈ C.events, k.1 = t ∧ C.vis k e ∧
      ∃ w : CellUpdate, MEvent.action k = Action.cell w ∧ w.row = u.row ∧ w.column = u.column
  range_overwrites_seen : ∀ e ∈ C.events, ∀ u : RangeUpdate,
    MEvent.action e = Action.range u →
    ∀ t ∈ u.overwrites, ∃ k ∈ C.events, k.1 = t ∧ C.vis k e ∧
      ∃ w : RangeUpdate, MEvent.action k = Action.range w ∧ w.id = u.id
  covered_seen : ∀ e ∈ C.events, ∀ m : Purge,
    MEvent.action e = Action.purge m →
    ∀ entry ∈ m.covered, ∃ k ∈ C.events, k.1 = entry.1 ∧ C.vis k e ∧
      ∃ w : CellUpdate, MEvent.action k = Action.cell w ∧ (w.row, w.column) = entry.2

/-- The merge obligation, restricted to honest contexts. -/
def JoinTarget : Prop := JoinOn M Honest

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

end Sal.MRDTs.Instances.AegisSheet.Materialised
