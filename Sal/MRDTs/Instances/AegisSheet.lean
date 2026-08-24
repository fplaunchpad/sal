import Sal.MRDTs.Instances.FinsetStore

/-!
# AegisSheet intent model

This module formalizes the conflict policies in Tables 3 and 4 of the PaPoC
2026 AegisSheet paper. The replicated carrier is a finite set of causally
annotated actions. Merge is union. The query is declarative: concurrent cell
writes remain visible, a cell write or move defeats a concurrent axis removal,
and the latest move fixes an axis position without duplicating its stable id.

The model is an executable semantic reference. It is not yet an equivalence
proof for Bismuth's Scala `ReplicatedUniqueList` implementation.
-/

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.AegisSheet

open Sal.MRDTs.Foundation
open Classical

abbrev StableId := Nat
abbrev Position := Nat
abbrev CellValue := Nat
abbrev RangeId := Nat

inductive Axis where
  | row
  | column
deriving DecidableEq, Repr

inductive AxisUpdateKind where
  | insert
  | move
  | remove
  | restore
deriving DecidableEq, Repr

structure AxisUpdate where
  kind : AxisUpdateKind
  axis : Axis
  id : StableId
  before : Option Position
  after : Option Position
deriving DecidableEq, Repr

structure CellUpdate where
  row : StableId
  column : StableId
  before : Finset CellValue
  after : Finset CellValue
  /-- Version timestamps removed by this write. Selective undo removes only
  the target write, not concurrent remote writes. -/
  overwrites : Finset Timestamp
deriving DecidableEq

structure RangeSpec where
  firstRow : StableId
  lastRow : StableId
  firstColumn : StableId
  lastColumn : StableId
deriving DecidableEq, Repr

structure RangeUpdate where
  id : RangeId
  before : Option RangeSpec
  after : Option RangeSpec
  overwrites : Finset Timestamp
deriving DecidableEq

abbrev Coordinate := StableId × StableId

/-- A purge is a replicated semantic marker. The generic distributed frontier
protocol supplies `acknowledgements`; the marker permanently masks old cell
versions at the named coordinates. -/
structure Purge where
  cutoff : Timestamp
  coordinates : Finset Coordinate
  /-- A reclaimed payload retains its timestamp-to-coordinate mapping. The
  timestamp remains in the causal summary, and the coordinate preserves the
  payload's observed-remove keep tokens for its row and column. -/
  covered : Finset (Timestamp × Coordinate)
  acknowledgements : Finset Replica
deriving DecidableEq

/-- Executable intrinsic well-formedness check for a replicated purge marker.
Every compact timestamp-to-coordinate entry must lie inside the marker's
semantic mask. -/
def Purge.validB (marker : Purge) : Bool :=
  Finset.fold (· && ·) true (fun entry =>
    decide (entry.2 ∈ marker.coordinates ∧ entry.1 ≤ marker.cutoff))
    marker.covered

def Purge.Valid (marker : Purge) : Prop := marker.validB = true

inductive Action where
  | axis (update : AxisUpdate)
  | cell (update : CellUpdate)
  | range (update : RangeUpdate)
  | purge (marker : Purge)
deriving DecidableEq

/-- Undo emits a checked inverse action. `target` names the local action being
undone; it does not erase history. -/
inductive Command where
  | direct (action : Action)
  | undo (target : Timestamp) (inverse : Action)
deriving DecidableEq

structure SheetOp where
  /-- Exact issuer-head timestamps. This separates visibility from numeric
  timestamp order. -/
  seen : Finset Timestamp
  command : Command
deriving DecidableEq

abbrev Event := Op SheetOp

def Command.effect : Command → Action
  | .direct action => action
  | .undo _ inverse => inverse

def Event.action (e : Event) : Action := e.2.2.command.effect
def Event.seen (e : Event) : Finset Timestamp := e.2.2.seen

def invertAction : Action → Action
  | .axis u => .axis {
      kind := .restore
      axis := u.axis
      id := u.id
      before := u.after
      after := u.before }
  | .cell u => .cell {
      row := u.row
      column := u.column
      before := u.after
      after := u.before
      overwrites := ∅ }
  | .range u => .range {
      id := u.id
      before := u.after
      after := u.before
      overwrites := ∅ }
  | .purge marker => .purge marker

/-- Selective undo removes the target version only. The replacement values in
`invertAction` remain concurrent with unrelated remote writes. -/
def inverseFor (target : Event) : Action :=
  match invertAction target.action with
  | .cell u => .cell { u with overwrites := {target.1} }
  | .range u => .range { u with overwrites := {target.1} }
  | other => other

def purge? (e : Event) : Option Purge :=
  match e.action with
  | .purge marker => some marker
  | _ => none

def eventTimes (events : Finset Event) : Finset Timestamp :=
  events.image (fun e => e.1) ∪
    events.biUnion (fun e => match purge? e with
      | some marker => marker.covered.image Prod.fst
      | none => ∅)

def axisUpdate? (e : Event) : Option AxisUpdate :=
  match e.action with
  | .axis u => some u
  | _ => none

def cellUpdate? (e : Event) : Option CellUpdate :=
  match e.action with
  | .cell u => some u
  | _ => none

def rangeUpdate? (e : Event) : Option RangeUpdate :=
  match e.action with
  | .range u => some u
  | _ => none

/-- Metadata needed after payload collection. Every overwritten cell or range
version must name an earlier version of the same stable coordinate or range
identity. Purge markers must keep their compact timestamp-to-coordinate map
inside the semantic cutoff mask. -/
def metadataValidB (events : Finset Event) (e : Event) : Bool :=
  match cellUpdate? e with
  | some update =>
      Finset.fold (· && ·) true (fun overwritten =>
        decide (overwritten < e.1) &&
        Finset.fold (· || ·) false (fun prior =>
          match cellUpdate? prior with
          | some priorUpdate => decide (prior.1 = overwritten ∧
              priorUpdate.row = update.row ∧
              priorUpdate.column = update.column)
          | none => false) events) update.overwrites
  | none => match rangeUpdate? e with
      | some update =>
          Finset.fold (· && ·) true (fun overwritten =>
            decide (overwritten < e.1) &&
            Finset.fold (· || ·) false (fun prior =>
              match rangeUpdate? prior with
              | some priorUpdate => decide (prior.1 = overwritten ∧
                  priorUpdate.id = update.id)
              | none => false) events) update.overwrites
      | none => match purge? e with
          | some marker => marker.validB
          | none => true

def keepsAxis (axis : Axis) (id : StableId) (e : Event) : Bool :=
  match e.action with
  | .axis u => decide (u.axis = axis ∧ u.id = id ∧ u.after.isSome)
  | .cell u => match axis with
      | .row => decide (u.row = id)
      | .column => decide (u.column = id)
  | .range _ | .purge _ => false

def removesAxis (axis : Axis) (id : StableId) (e : Event) : Bool :=
  match e.action with
  | .axis u => decide (u.axis = axis ∧ u.id = id ∧ u.after = none)
  | _ => false

def axisKnown (events : Finset Event) (axis : Axis) (id : StableId) : Bool :=
  Finset.fold (· || ·) false (fun e =>
      match axisUpdate? e with
      | some u => decide (u.axis = axis ∧ u.id = id)
      | none => false) events

/-- A removal wins only when it observed every keep for that stable id. A
concurrent edit, move, or later restore therefore defeats it. -/
def effectiveRemoval (events : Finset Event) (axis : Axis)
    (id : StableId) (remove : Event) : Bool :=
  removesAxis axis id remove &&
    Finset.fold (· && ·) true (fun keep =>
      !keepsAxis axis id keep || decide (keep.1 ∈ remove.seen)) events

def axisKeepTimes (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset Timestamp :=
  (events.filter fun e => keepsAxis axis id e).image (fun e => e.1) ∪
    events.biUnion (fun e => match purge? e with
      | some marker =>
          marker.covered.biUnion fun entry =>
            if match axis with
              | .row => entry.2.1 == id
              | .column => entry.2.2 == id
            then {entry.1} else ∅
      | none => ∅)

def axisTokenRemoved (events : Finset Event) (axis : Axis)
    (id : StableId) (token : Timestamp) : Bool :=
  Finset.fold (· || ·) false (fun remove =>
    removesAxis axis id remove && decide (token ∈ remove.seen)) events

def liveAxisTokens (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset Timestamp :=
  (axisKeepTimes events axis id).filter fun token =>
    !axisTokenRemoved events axis id token

def finsetNonemptyB {α : Type} [DecidableEq α] (values : Finset α) : Bool :=
  Finset.fold (· || ·) false (fun _ => true) values

def axisLive (events : Finset Event) (axis : Axis) (id : StableId) : Bool :=
  axisKnown events axis id &&
    finsetNonemptyB (liveAxisTokens events axis id)

def axisIds (events : Finset Event) (axis : Axis) : Finset StableId :=
  events.biUnion (fun e =>
    match axisUpdate? e with
    | some u => if u.axis = axis then {u.id} else ∅
    | none => ∅)

def liveAxisIds (events : Finset Event) (axis : Axis) : Finset StableId :=
  (axisIds events axis).filter fun id => axisLive events axis id

def axisCandidate (axis : Axis) (id : StableId) (e : Event) : Bool :=
  match axisUpdate? e with
  | some u => decide (u.axis = axis ∧ u.id = id ∧ u.after.isSome)
  | none => false

def laterAxisCandidate (events : Finset Event) (axis : Axis)
    (id : StableId) (candidate : Event) : Bool :=
  Finset.fold (· || ·) false (fun later =>
    axisCandidate axis id later && decide (candidate.1 < later.1)) events

def axisPositions (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset Position :=
  (events.filter fun e =>
      axisCandidate axis id e && !laterAxisCandidate events axis id e).biUnion
    (fun e => match axisUpdate? e with
      | some u => match u.after with | some p => {p} | none => ∅
      | none => ∅)

def optionFinset {α : Type} [DecidableEq α] : Option α → Finset α
  | some value => {value}
  | none => ∅

def cellMatches (row column : StableId) (e : Event) : Bool :=
  match cellUpdate? e with
  | some u => decide (u.row = row ∧ u.column = column)
  | none => false

def cellOverwritten (events : Finset Event) (candidate : Event) : Bool :=
  Finset.fold (· || ·) false (fun later =>
      match later.action with
      | .cell u => decide (candidate.1 ∈ u.overwrites)
      | .purge marker => match cellUpdate? candidate with
          | some update =>
              decide ((update.row, update.column) ∈ marker.coordinates ∧
                candidate.1 ≤ marker.cutoff)
          | none => false
      | _ => false) events

def activeCellTimes (events : Finset Event) (row column : StableId) :
    Finset Timestamp :=
  (events.filter fun e =>
    cellMatches row column e && !cellOverwritten events e).image (fun e => e.1)

def rawCellValues (events : Finset Event) (row column : StableId) :
    Finset CellValue :=
  (events.filter fun e =>
    cellMatches row column e && !cellOverwritten events e).biUnion
      (fun e => match cellUpdate? e with | some u => u.after | none => ∅)

def cellValues (events : Finset Event) (row column : StableId) :
    Finset CellValue :=
  if axisLive events .row row && axisLive events .column column
  then rawCellValues events row column else ∅

def rangeMatches (id : RangeId) (e : Event) : Bool :=
  match rangeUpdate? e with
  | some u => decide (u.id = id)
  | none => false

def rangeOverwritten (events : Finset Event) (candidate : Event) : Bool :=
  Finset.fold (· || ·) false (fun later =>
      match rangeUpdate? later with
      | some u => decide (candidate.1 ∈ u.overwrites)
      | none => false) events

def activeRangeTimes (events : Finset Event) (id : RangeId) :
    Finset Timestamp :=
  (events.filter fun e =>
    rangeMatches id e && !rangeOverwritten events e).image (fun e => e.1)

def rangeValues (events : Finset Event) (id : RangeId) : Finset RangeSpec :=
  (events.filter fun e =>
    rangeMatches id e && !rangeOverwritten events e).biUnion
      (fun e => match rangeUpdate? e with
        | some u => optionFinset u.after
        | none => ∅)

structure View where
  rows : Finset StableId
  columns : Finset StableId
  rowPosition : StableId → Finset Position
  columnPosition : StableId → Finset Position
  cell : StableId → StableId → Finset CellValue
  range : RangeId → Finset RangeSpec

def view (events : Finset Event) : View where
  rows := liveAxisIds events .row
  columns := liveAxisIds events .column
  rowPosition := axisPositions events .row
  columnPosition := axisPositions events .column
  cell := cellValues events
  range := rangeValues events

/-! ## Anchored range observation -/

def positionOption (events : Finset Event) (axis : Axis)
    (id : StableId) : Option Position :=
  let positions := axisPositions events axis id
  if h : positions.Nonempty then some (positions.min' h) else none

def livePositions (events : Finset Event) (axis : Axis) : Finset Position :=
  (liveAxisIds events axis).biUnion fun id => axisPositions events axis id

def minNat? (values : Finset Nat) : Option Nat :=
  if h : values.Nonempty then some (values.min' h) else none

def maxNat? (values : Finset Nat) : Option Nat :=
  if h : values.Nonempty then some (values.max' h) else none

def idAtPosition (events : Finset Event) (axis : Axis)
    (position : Position) : Option StableId :=
  minNat? ((liveAxisIds events axis).filter fun id =>
    decide (position ∈ axisPositions events axis id))

/-- A deleted first endpoint attaches to its next live successor. -/
def resolveFirst (events : Finset Event) (axis : Axis)
    (endpoint : StableId) : Option StableId :=
  if axisLive events axis endpoint then some endpoint else
    match positionOption events axis endpoint with
    | none => none
    | some oldPosition =>
        (minNat? ((livePositions events axis).filter
          fun candidate => decide (oldPosition < candidate))).bind
            (idAtPosition events axis)

/-- A deleted last endpoint attaches to its previous live predecessor. -/
def resolveLast (events : Finset Event) (axis : Axis)
    (endpoint : StableId) : Option StableId :=
  if axisLive events axis endpoint then some endpoint else
    match positionOption events axis endpoint with
    | none => none
    | some oldPosition =>
        (maxNat? ((livePositions events axis).filter
          fun candidate => decide (candidate < oldPosition))).bind
            (idAtPosition events axis)

structure ResolvedRange where
  firstRow : StableId
  lastRow : StableId
  firstColumn : StableId
  lastColumn : StableId
deriving DecidableEq, Repr

def resolveRange (events : Finset Event) (spec : RangeSpec) :
    Option ResolvedRange := do
  let firstRow ← resolveFirst events .row spec.firstRow
  let lastRow ← resolveLast events .row spec.lastRow
  let firstColumn ← resolveFirst events .column spec.firstColumn
  let lastColumn ← resolveLast events .column spec.lastColumn
  let firstRowPosition ← positionOption events .row firstRow
  let lastRowPosition ← positionOption events .row lastRow
  let firstColumnPosition ← positionOption events .column firstColumn
  let lastColumnPosition ← positionOption events .column lastColumn
  if firstRowPosition ≤ lastRowPosition &&
      firstColumnPosition ≤ lastColumnPosition then
    some ⟨firstRow, lastRow, firstColumn, lastColumn⟩
  else none

/-! ## Raw MRDT and certificates -/

def D : MRDTSig where
  State := Finset Event
  dec_state := inferInstance
  init := ∅
  AppOp := SheetOp
  dec_op := inferInstance
  Query := Unit
  Value := View
  update s e := insert e s
  merge := (· ∪ ·)
  query s _ := view s
  mergeL _ a b := a ∪ b
  merge_init_slice _ _ := rfl

theorem all_comm (a b : Event) : D.toCRDTSig.commutes a b := by
  intro s
  apply Finset.ext
  intro x
  simp [D, or_left_comm]

theorem updateVCs : UpdateVCs D.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b _ _
    constructor
    · intro h
      exact absurd (all_comm a b) h
    · rintro (h | h) <;> exact RcRes.noConfusion h
  · intro a b c _ _
    rintro ⟨h, _⟩
    exact RcRes.noConfusion h
  · intro s a b c π _ _ _ h _
    exact RcRes.noConfusion h

theorem coreVCs3 : CoreVCs3 D := by
  refine ⟨updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b; apply Finset.ext; intro x; simp [D, or_comm]
  · intro s; apply Finset.ext; intro x; simp [D]
  · intro l a b e; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]
  · intro a e π₀ π₂ _ _; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]

theorem deltaVCs3 : DeltaVCs3 D := by
  constructor
  · intro m x₀ x₁ x₂ c; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]
  · intro l m x c y; apply Finset.ext; intro z
    simp [D, or_assoc, or_left_comm, or_comm]

theorem join : JoinLemma3 D :=
  join_lemma3_of_cd' coreVCs3 deltaVCs3
    (cdVC3_of_all_comm coreVCs3 all_comm)

def currentAxisPositions (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset Position :=
  if axisLive events axis id then axisPositions events axis id else ∅

def requiredRoster : Finset Replica := {0, 1, 2}

def purgeApplicable (events : Finset Event) (issuer : Replica)
    (marker : Purge) : Bool :=
  decide (issuer = 0) &&
  decide (requiredRoster ⊆ marker.acknowledgements) &&
  marker.validB &&
  Finset.fold (· && ·) true (fun entry =>
    Finset.fold (· || ·) false (fun event =>
      match cellUpdate? event with
      | some update => decide (event.1 = entry.1 ∧
          (update.row, update.column) = entry.2 ∧
          entry.2 ∈ marker.coordinates ∧
          event.1 ≤ marker.cutoff)
      | none => false) events) marker.covered &&
  Finset.fold (· && ·) true (fun coordinate =>
    !axisLive events .row coordinate.1 ||
      !axisLive events .column coordinate.2) marker.coordinates

def directApplicable (events : Finset Event) (issuer : Replica) : Action → Bool
  | .axis u => match u.kind with
      | .insert =>
          !axisKnown events u.axis u.id && u.before.isNone && u.after.isSome
      | .move =>
          decide (currentAxisPositions events u.axis u.id = optionFinset u.before) &&
          u.before.isSome && u.after.isSome
      | .remove =>
          decide (currentAxisPositions events u.axis u.id = optionFinset u.before) &&
          u.before.isSome && u.after.isNone
      | .restore => false
  | .cell u =>
      axisLive events .row u.row && axisLive events .column u.column &&
      decide (cellValues events u.row u.column = u.before) &&
      decide (activeCellTimes events u.row u.column = u.overwrites)
  | .range u =>
      decide (rangeValues events u.id = optionFinset u.before) &&
      decide (activeRangeTimes events u.id = u.overwrites)
  | .purge marker => purgeApplicable events issuer marker

def validUndo (events : Finset Event) (issuer : Replica)
    (target : Timestamp) (inverse : Action) : Bool :=
  Finset.fold (· || ·) false (fun prior =>
    match prior.action with
    | .purge _ => false
    | _ => decide (prior.1 = target ∧ prior.2.1 = issuer ∧ inverse = inverseFor prior)) events

def applicableB (e : Event) (events : Finset Event) : Bool :=
  !(decide (e.1 ∈ eventTimes events)) &&
  decide (e.seen = eventTimes events) &&
  metadataValidB events e &&
  match e.2.2.command with
  | .direct action => directApplicable events e.2.1 action
  | .undo target inverse =>
      decide (target ∈ e.seen) && validUndo events e.2.1 target inverse

/-- The issuer's Lamport timestamp is strictly above every direct or compact
causal timestamp in its materialized origin state. Freshness alone is not
enough to justify chronological merged-history witnesses. -/
def clockedB (e : Event) (events : Finset Event) : Bool :=
  Finset.fold (· && ·) true
    (fun timestamp => decide (timestamp < e.1)) (eventTimes events)

def ClockedAt (e : Event) (events : Finset Event) : Prop :=
  clockedB e events = true

theorem foldAnd_eq_true_iff {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → Bool) :
    Finset.fold (· && ·) true f s = true ↔
      ∀ x ∈ s, f x = true := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s fresh ih =>
      rw [Finset.fold_insert fresh]
      simp [ih]

theorem ClockedAt.lt {e : Event} {events : Finset Event}
    (h : ClockedAt e events) :
    ∀ timestamp ∈ eventTimes events, timestamp < e.1 := by
  unfold ClockedAt clockedB at h
  rw [foldAnd_eq_true_iff] at h
  intro timestamp member
  simpa using h timestamp member

def applicable (e : Event) (events : Finset Event) : Prop :=
  applicableB e events = true ∧ ClockedAt e events

instance (e : Event) (events : Finset Event) :
    Decidable (applicable e events) := by
  unfold applicable ClockedAt
  infer_instance

def generation : Issuance D where
  CanIssue := applicable

def convergence : ConvergenceCertificate D generation where
  soundV := fun h => isRALinearizable_of_join
    (ra_of_mintCertifiedV (fun _ _ => join _) h)

theorem applySeq_eq_toFinset (ops : List Event) :
    applySeq D.toCRDTSig D.init ops = ops.toFinset := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      rw [applySeq_append_single]
      simpa [D] using congrArg (fun s : Finset Event => insert e s) ih

def safeState (events : Finset Event) : Prop :=
  ∀ row column, cellValues events row column ≠ ∅ →
    axisLive events .row row = true ∧ axisLive events .column column = true

theorem every_state_safe (events : Finset Event) : safeState events := by
  intro row column h
  unfold cellValues at h
  split at h
  · rename_i yes
    simpa [Bool.and_eq_true] using yes
  · simp at h

def safety : SafetyCertificate D (canonicalVirtualLCA D) generation where
  Safe := safeState
  Observable := safeState
  preservationV := by
    intro C _ v s E _
    exact every_state_safe s
  consequence := fun _ h => h

/-! ## External intent oracle

The first argument is operation 1 (the operation undone in Table 4); the
second is the concurrent operation 2. These enums keep every published matrix
cell named even when two cells share the same implementation fixture.
-/

inductive MatrixOp where
  | editCell
  | insertAxis
  | removeAxis
  | moveAxis
deriving DecidableEq, Repr

inductive MergeOutcome where
  | conflict
  | notApplicable
  | editDefeatsRemove
  | moveAndEdit
  | createBoth
  | insertAndRemove
  | insertAtOldPositionAndMove
  | remove
  | moveWins
  | lastMoveWins
deriving DecidableEq, Repr

def publishedMergeOutcome : MatrixOp → MatrixOp → MergeOutcome
  | .editCell, .editCell => .conflict
  | .editCell, .insertAxis => .notApplicable
  | .editCell, .removeAxis => .editDefeatsRemove
  | .editCell, .moveAxis => .moveAndEdit
  | .insertAxis, .editCell => .notApplicable
  | .insertAxis, .insertAxis => .createBoth
  | .insertAxis, .removeAxis => .insertAndRemove
  | .insertAxis, .moveAxis => .insertAtOldPositionAndMove
  | .removeAxis, .editCell => .editDefeatsRemove
  | .removeAxis, .insertAxis => .insertAndRemove
  | .removeAxis, .removeAxis => .remove
  | .removeAxis, .moveAxis => .moveWins
  | .moveAxis, .editCell => .moveAndEdit
  | .moveAxis, .insertAxis => .insertAtOldPositionAndMove
  | .moveAxis, .removeAxis => .moveWins
  | .moveAxis, .moveAxis => .lastMoveWins

inductive UndoOutcome where
  | conflictWithInitial
  | notApplicable
  | removeAlreadyCancelled
  | revertEditKeepMove
  | revertInsert
  | revertRemove
  | revertMoveKeepConcurrent
  | revertEdit
  | revertBoth
  | removeAlreadyCancelledByMove
deriving DecidableEq, Repr

def publishedUndoOutcome : MatrixOp → MatrixOp → UndoOutcome
  | .editCell, .editCell => .conflictWithInitial
  | .editCell, .insertAxis => .notApplicable
  | .editCell, .removeAxis => .revertEdit
  | .editCell, .moveAxis => .revertEditKeepMove
  | .insertAxis, .editCell => .notApplicable
  | .insertAxis, .insertAxis => .revertInsert
  | .insertAxis, .removeAxis => .revertInsert
  | .insertAxis, .moveAxis => .revertInsert
  | .removeAxis, .editCell => .removeAlreadyCancelled
  | .removeAxis, .insertAxis => .revertRemove
  | .removeAxis, .removeAxis => .revertBoth
  | .removeAxis, .moveAxis => .removeAlreadyCancelledByMove
  | .moveAxis, .editCell => .revertMoveKeepConcurrent
  | .moveAxis, .insertAxis => .revertMoveKeepConcurrent
  | .moveAxis, .removeAxis => .revertBoth
  | .moveAxis, .moveAxis => .revertBoth

def allMatrixOps : List MatrixOp :=
  [.editCell, .insertAxis, .removeAxis, .moveAxis]

example : (allMatrixOps.flatMap fun first =>
    allMatrixOps.map fun second => publishedMergeOutcome first second).length = 16 := by
  native_decide

example : (allMatrixOps.flatMap fun first =>
    allMatrixOps.map fun second => publishedUndoOutcome first second).length = 16 := by
  native_decide

/-! ## Published-matrix SPOTs -/

def axisEvent (time replica : Nat) (seen : Finset Nat)
    (kind : AxisUpdateKind) (axis : Axis) (id : StableId)
    (before after : Option Position) : Event :=
  (time, replica, ⟨seen, .direct (.axis ⟨kind, axis, id, before, after⟩)⟩)

def cellEvent (time replica : Nat) (seen : Finset Nat)
    (row column : StableId) (before after : Finset CellValue)
    (overwrites : Finset Nat) : Event :=
  (time, replica, ⟨seen, .direct (.cell ⟨row, column, before, after, overwrites⟩)⟩)

def undoCellEvent (time replica : Nat) (seen : Finset Nat)
    (target : Event) : Event :=
  (time, replica, ⟨seen, .undo target.1 (inverseFor target)⟩)

def undoAxisEvent (time replica : Nat) (seen : Finset Nat)
    (target : Event) : Event :=
  (time, replica, ⟨seen, .undo target.1 (inverseFor target)⟩)

def rangeEvent (time replica : Nat) (seen : Finset Nat) (id : RangeId)
    (before after : Option RangeSpec) (overwrites : Finset Nat) : Event :=
  (time, replica, ⟨seen, .direct (.range ⟨id, before, after, overwrites⟩)⟩)

def purgeEvent (time replica : Nat) (seen : Finset Nat) (cutoff : Nat)
    (coordinates : Finset Coordinate)
    (covered : Finset (Timestamp × Coordinate))
    (acknowledgements : Finset Replica) : Event :=
  (time, replica,
    ⟨seen, .direct (.purge ⟨cutoff, coordinates, covered, acknowledgements⟩)⟩)

def r0 : StableId := 10
def r1 : StableId := 11
def c0 : StableId := 20
def c1 : StableId := 21

def baseRow : Event := axisEvent 1 0 ∅ .insert .row r0 none (some 10)
def baseColumn : Event := axisEvent 2 0 {1} .insert .column c0 none (some 10)
def baseCell : Event := cellEvent 3 0 {1, 2} r0 c0 ∅ {0} ∅
def base : Finset Event := {baseRow, baseColumn, baseCell}

/-- Table 3: a concurrent edit defeats row removal and preserves its value. -/
def concurrentRemove : Event := axisEvent 4 1 {1, 2, 3} .remove .row r0 (some 10) none
def concurrentEdit : Event := cellEvent 5 2 {1, 2, 3} r0 c0 {0} {1} {3}
def editRemoveState : Finset Event := insert concurrentEdit (insert concurrentRemove base)

example : axisLive editRemoveState .row r0 = true := by native_decide
example : cellValues editRemoveState r0 c0 = {1} := by native_decide
example : applicableB concurrentRemove base = true := by native_decide
example : applicableB concurrentEdit base = true := by native_decide
/-- FAIL control: delete-wins is not the published outcome. -/
example : ¬ (axisLive editRemoveState .row r0 = false) := by native_decide

/-- FAIL control: an issuer cannot claim a head context it did not observe. -/
def dishonestEdit : Event := cellEvent 5 2 ∅ r0 c0 {0} {1} {3}
example : applicableB dishonestEdit base = false := by native_decide

/-- A causally later removal does win; update-wins is not unconditional. -/
def laterRemove : Event := axisEvent 6 1 {1, 2, 3, 5} .remove .row r0 (some 10) none
def laterRemoveState : Finset Event := insert laterRemove (insert concurrentEdit base)
example : axisLive laterRemoveState .row r0 = false := by native_decide

/-- Table 3: concurrent writes retain both values. -/
def editA : Event := cellEvent 4 1 {1, 2, 3} r0 c0 {0} {1} {3}
def editB : Event := cellEvent 5 2 {1, 2, 3} r0 c0 {0} {2} {3}
def conflictState : Finset Event := insert editA (insert editB base)
example : cellValues conflictState r0 c0 = {1, 2} := by native_decide
example : ¬ (cellValues conflictState r0 c0 = {2}) := by native_decide

/-- Table 4: undoing one side of a conflict restores the old value without
overwriting the concurrent remote edit. -/
def undoA : Event := undoCellEvent 6 1 {1, 2, 3, 4, 5} editA
def undoConflictState : Finset Event := insert undoA conflictState
example : cellValues undoConflictState r0 c0 = {0, 2} := by native_decide
example : ¬ (cellValues undoConflictState r0 c0 = {0}) := by native_decide
example : applicableB undoA conflictState = true := by native_decide

/-- FAIL control: a replica cannot undo another replica's event. -/
def remoteUndoA : Event := undoCellEvent 6 2 {1, 2, 3, 4, 5} editA
example : applicableB remoteUndoA conflictState = false := by native_decide

/-- Table 3: a move defeats concurrent removal and chooses its new position. -/
def moveRow : Event := axisEvent 5 2 {1, 2, 3} .move .row r0 (some 10) (some 30)
def moveRemoveState : Finset Event := insert moveRow (insert concurrentRemove base)
example : axisLive moveRemoveState .row r0 = true := by native_decide
example : axisPositions moveRemoveState .row r0 = {30} := by native_decide

/-- Concurrent move and edit preserve both effects. -/
def moveEditState : Finset Event := insert moveRow (insert concurrentEdit base)
example : axisPositions moveEditState .row r0 = {30} := by native_decide
example : cellValues moveEditState r0 c0 = {1} := by native_decide

/-- Concurrent moves use the later timestamp and never duplicate the id. -/
def moveRowEarlier : Event := axisEvent 4 1 {1, 2, 3} .move .row r0 (some 10) (some 20)
def twoMoveState : Finset Event := insert moveRowEarlier (insert moveRow base)
example : axisPositions twoMoveState .row r0 = {30} := by native_decide
example : (liveAxisIds twoMoveState .row).card = 1 := by native_decide

/-- An insertion keeps its minted gap position when its left neighbor moves. -/
def insertedRow : Event := axisEvent 4 1 {1, 2, 3} .insert .row r1 none (some 15)
def insertMoveState : Finset Event := insert insertedRow (insert moveRow base)
example : axisPositions insertMoveState .row r1 = {15} := by native_decide
example : axisPositions insertMoveState .row r0 = {30} := by native_decide
example : (liveAxisIds insertMoveState .row).card = 2 := by native_decide

/-- Two concurrent inserts at one gap keep both stable ids. -/
def insertedRow2 : Event := axisEvent 5 2 {1, 2, 3} .insert .row 12 none (some 15)
def twoInsertState : Finset Event := insert insertedRow (insert insertedRow2 base)
example : (liveAxisIds twoInsertState .row).card = 3 := by native_decide

/-- An adjacent insertion survives while the original row is removed. -/
def insertRemoveState : Finset Event := insert insertedRow (insert concurrentRemove base)
example : axisLive insertRemoveState .row r0 = false := by native_decide
example : axisLive insertRemoveState .row r1 = true := by native_decide

/-- Undoing insert removes only the inserted stable id. -/
def undoInsertedRow : Event := undoAxisEvent 6 1 {1, 2, 3, 4} insertedRow
def undoInsertState : Finset Event := insert undoInsertedRow (insert insertedRow base)
example : axisLive undoInsertState .row r1 = false := by native_decide
example : axisLive undoInsertState .row r0 = true := by native_decide
example : applicableB undoInsertedRow (insert insertedRow base) = true := by native_decide

/-- Undoing a remove restores its previous stable position. -/
def undoRemove : Event := undoAxisEvent 6 1 {1, 2, 3, 4} concurrentRemove
def undoRemoveState : Finset Event := insert undoRemove (insert concurrentRemove base)
example : axisLive undoRemoveState .row r0 = true := by native_decide
example : axisPositions undoRemoveState .row r0 = {10} := by native_decide

/-- Undoing a remove that a concurrent edit already cancelled is observationally
idempotent. -/
def cancelledRemoveState : Finset Event := insert concurrentEdit (insert concurrentRemove base)
def undoCancelledRemove : Event :=
  undoAxisEvent 6 1 {1, 2, 3, 4, 5} concurrentRemove
def undoCancelledRemoveState : Finset Event :=
  insert undoCancelledRemove cancelledRemoveState
example : axisLive cancelledRemoveState .row r0 =
    axisLive undoCancelledRemoveState .row r0 := by native_decide
example : cellValues cancelledRemoveState r0 c0 =
    cellValues undoCancelledRemoveState r0 c0 := by native_decide

/-- Two concurrent removals agree on absence. -/
def concurrentRemove2 : Event :=
  axisEvent 5 2 {1, 2, 3} .remove .row r0 (some 10) none
def twoRemoveState : Finset Event := insert concurrentRemove2 (insert concurrentRemove base)
example : axisLive twoRemoveState .row r0 = false := by native_decide

/-- Undoing a move restores its old position and retains a concurrent edit. -/
def moveByReplica1 : Event := axisEvent 4 1 {1, 2, 3} .move .row r0 (some 10) (some 30)
def editByReplica2 : Event := cellEvent 5 2 {1, 2, 3} r0 c0 {0} {2} {3}
def undoMove : Event := undoAxisEvent 6 1 {1, 2, 3, 4, 5} moveByReplica1
def undoMoveState : Finset Event :=
  insert undoMove (insert editByReplica2 (insert moveByReplica1 base))
example : axisPositions undoMoveState .row r0 = {10} := by native_decide
example : cellValues undoMoveState r0 c0 = {2} := by native_decide

/-- Table 4: undoing a move restores the moved stable id without changing a
concurrent insertion's stable position. This is the case that the audited
Scala index-based undo closure gets wrong. -/
def table4Move : Event :=
  axisEvent 4 1 {1, 2, 3} .move .row r0 (some 10) (some 30)
def table4ConcurrentInsert : Event :=
  axisEvent 5 2 {1, 2, 3} .insert .row r1 none (some 20)
def table4UndoMove : Event :=
  undoAxisEvent 6 1 {1, 2, 3, 4, 5} table4Move
def table4MoveInsertUndoState : Finset Event :=
  insert table4UndoMove
    (insert table4ConcurrentInsert (insert table4Move base))
example : axisPositions table4MoveInsertUndoState .row r0 = {10} := by native_decide
example : axisPositions table4MoveInsertUndoState .row r1 = {20} := by native_decide

/-- Table 4: undoing one of two concurrent moves restores the original stable
position rather than applying an inverse to whichever row occupies an old
numeric index. -/
def table4ConcurrentMove : Event :=
  axisEvent 5 2 {1, 2, 3} .move .row r0 (some 10) (some 40)
def table4MoveMoveUndoState : Finset Event :=
  insert table4UndoMove (insert table4ConcurrentMove (insert table4Move base))
example : axisPositions table4MoveMoveUndoState .row r0 = {10} := by native_decide

/-! ## Figure 1 range fixtures -/

def secondRow : Event := axisEvent 4 0 {1, 2, 3} .insert .row r1 none (some 20)
def secondColumn : Event := axisEvent 5 0 {1, 2, 3, 4} .insert .column c1 none (some 20)
def rangeSpec : RangeSpec := ⟨r0, r1, c0, c1⟩
def addRange : Event := rangeEvent 6 0 {1, 2, 3, 4, 5} 30 none (some rangeSpec) ∅
def rangedBase : Finset Event :=
  insert addRange (insert secondColumn (insert secondRow base))

example : rangeValues rangedBase 30 = {rangeSpec} := by native_decide
example : resolveRange rangedBase rangeSpec = some ⟨r0, r1, c0, c1⟩ := by native_decide

/-- Removing the first border attaches it to the next live row and shrinks the
range. -/
def removeFirstRangeRow : Event :=
  axisEvent 7 1 {1, 2, 3, 4, 5} .remove .row r0 (some 10) none
def borderDeletedRangeState : Finset Event := insert removeFirstRangeRow rangedBase
example : resolveRange borderDeletedRangeState rangeSpec =
    some ⟨r1, r1, c0, c1⟩ := by native_decide

/-- Moving the last endpoint before the first crosses the range and removes
its observation. -/
def crossLastRangeRow : Event :=
  axisEvent 7 1 {1, 2, 3, 4, 5} .move .row r1 (some 20) (some 5)
def crossedRangeState : Finset Event := insert crossLastRangeRow rangedBase
example : resolveRange crossedRangeState rangeSpec = none := by native_decide

/-- Removing an interior row preserves both anchored endpoints while the
visible rectangle shrinks. -/
def r2 : StableId := 12
def thirdRow : Event := axisEvent 6 0 {1, 2, 3, 4, 5} .insert .row r2 none (some 30)
def wideRangeSpec : RangeSpec := ⟨r0, r2, c0, c1⟩
def addWideRange : Event :=
  rangeEvent 7 0 {1, 2, 3, 4, 5, 6} 31 none (some wideRangeSpec) ∅
def wideRangeBase : Finset Event :=
  insert addWideRange (insert thirdRow (insert secondColumn (insert secondRow base)))
def removeInteriorRow : Event :=
  axisEvent 8 1 {1, 2, 3, 4, 5, 6} .remove .row r1 (some 20) none
def interiorDeletedRangeState : Finset Event := insert removeInteriorRow wideRangeBase
example : resolveRange interiorDeletedRangeState wideRangeSpec =
    some ⟨r0, r2, c0, c1⟩ := by native_decide
example : (liveAxisIds interiorDeletedRangeState .row).card = 2 := by native_decide

/-- Distinct range identities coexist even when their rectangles overlap. -/
def overlappingRangeSpec : RangeSpec := ⟨r1, r2, c0, c1⟩
def addOverlappingRange : Event :=
  rangeEvent 8 1 {1, 2, 3, 4, 5, 6, 7} 32 none
    (some overlappingRangeSpec) ∅
def overlappingRangeState : Finset Event := insert addOverlappingRange wideRangeBase
example : rangeValues overlappingRangeState 31 = {wideRangeSpec} := by native_decide
example : rangeValues overlappingRangeState 32 = {overlappingRangeSpec} := by native_decide

/-- Range removal followed by a fresh recreation is visible again. -/
def removeRange : Event := rangeEvent 7 0 {1, 2, 3, 4, 5, 6} 30
  (some rangeSpec) none {6}
def recreateRange : Event := rangeEvent 8 0 {1, 2, 3, 4, 5, 6, 7} 30
  none (some rangeSpec) {7}
def recreatedRangeState : Finset Event := insert recreateRange (insert removeRange rangedBase)
example : rangeValues recreatedRangeState 30 = {rangeSpec} := by native_decide

#print axioms join

end Sal.MRDTs.Instances.AegisSheet
