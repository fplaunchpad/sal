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

This file contains the executable signature and canonical state of a
reference event set. The companion modules prove Join, replay adequacy,
state/replay correspondence, and retirement. Executable fixtures live in
`AegisSheetPortSPOT.lean`, outside the proof dependencies.
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

/-! ## Interfaces proved by the companion modules

These `Prop` definitions name the statements proved by `Equivalence`,
`Update`, and `Join`; see `docs/aegissheet-materialised/plan.md`. -/

/-- Observation equivalence on purge-free histories, against the union
model's `view`. With purges the reference is the D2 view. -/
def ObservationEquivalence : Prop :=
  ∀ events : Finset Event, (∀ e ∈ events, purge? e = none) →
    mview (canon events) = view events

/-- A union-model history is honest when every causal summary lies within its
timestamps, timestamps identify events, every event's metadata is valid against
it, and every purged entry names a cell event at the covered coordinate. Every
history reached by applicable insertions from the empty history is honest. -/
structure HonestHistory (E : Finset Event) : Prop where
  seen_sub : ∀ r ∈ E, r.seen ⊆ eventTimes E
  ts_unique : ∀ a ∈ E, ∀ b ∈ E, a.1 = b.1 → a = b
  valid : ∀ r ∈ E, metadataValidB E r = true
  covered_valid : ∀ r ∈ E, ∀ m : Purge, r.action = .purge m → ∀ entry ∈ m.covered,
    ∃ c ∈ E, ∃ w : CellUpdate, c.action = .cell w ∧ c.1 = entry.1 ∧ (w.row, w.column) = entry.2

/-- Representation is preserved by an applicable update of an honest history. -/
def UpdatePreservesCanon : Prop :=
  ∀ (events : Finset Event) (e : Event), HonestHistory events → applicable e events →
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

end Sal.MRDTs.Instances.AegisSheet.Materialised
