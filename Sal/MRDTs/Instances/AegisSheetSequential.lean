import Sal.MRDTs.Instances.AegisSheetGC

set_option maxHeartbeats 1000000

/-!
# Incremental AegisSheet reference machine

This module gives the in-place sequential reference that is deliberately
separate from the replicated event set. It retains observed-remove tokens for
axis liveness, timestamped position candidates, active cell versions, and
active range versions. It never replays the full event history to answer a
query.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Sequential

open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.AegisSheet

abbrev PositionVersion := Timestamp × Position
abbrev CellVersion := Timestamp × CellValue
abbrev RangeVersion := Timestamp × RangeSpec

structure State where
  knownRows : Finset StableId
  knownColumns : Finset StableId
  rowTokens : StableId → Finset Timestamp
  columnTokens : StableId → Finset Timestamp
  rowPositions : StableId → Finset PositionVersion
  columnPositions : StableId → Finset PositionVersion
  cells : StableId → StableId → Finset CellVersion
  ranges : RangeId → Finset RangeVersion
  purges : Finset Purge

@[ext] theorem State.ext {a b : State}
    (knownRows : a.knownRows = b.knownRows)
    (knownColumns : a.knownColumns = b.knownColumns)
    (rowTokens : a.rowTokens = b.rowTokens)
    (columnTokens : a.columnTokens = b.columnTokens)
    (rowPositions : a.rowPositions = b.rowPositions)
    (columnPositions : a.columnPositions = b.columnPositions)
    (cells : a.cells = b.cells)
    (ranges : a.ranges = b.ranges)
    (purges : a.purges = b.purges) : a = b := by
  cases a
  cases b
  simp_all

@[ext] theorem View.ext {a b : View}
    (rows : a.rows = b.rows)
    (columns : a.columns = b.columns)
    (rowPosition : a.rowPosition = b.rowPosition)
    (columnPosition : a.columnPosition = b.columnPosition)
    (cell : a.cell = b.cell)
    (range : a.range = b.range) : a = b := by
  cases a
  cases b
  simp_all

def empty : State where
  knownRows := ∅
  knownColumns := ∅
  rowTokens := fun _ => ∅
  columnTokens := fun _ => ∅
  rowPositions := fun _ => ∅
  columnPositions := fun _ => ∅
  cells := fun _ _ => ∅
  ranges := fun _ => ∅
  purges := ∅

def removeSeen (tokens seen : Finset Timestamp) : Finset Timestamp :=
  tokens.filter fun timestamp => decide (timestamp ∉ seen)

def addAxisKeep (state : State) (axis : Axis) (id : StableId)
    (timestamp : Timestamp) : State :=
  match axis with
  | .row => { state with
      knownRows := insert id state.knownRows
      rowTokens := Function.update state.rowTokens id
        (insert timestamp (state.rowTokens id)) }
  | .column => { state with
      knownColumns := insert id state.knownColumns
      columnTokens := Function.update state.columnTokens id
        (insert timestamp (state.columnTokens id)) }

def setAxisPosition (state : State) (axis : Axis) (id : StableId)
    (timestamp : Timestamp) (position : Position) : State :=
  match axis with
  | .row => { state with
      rowPositions := Function.update state.rowPositions id
        (insert (timestamp, position) (state.rowPositions id)) }
  | .column => { state with
      columnPositions := Function.update state.columnPositions id
        (insert (timestamp, position) (state.columnPositions id)) }

def removeAxisSeen (state : State) (axis : Axis) (id : StableId)
    (seen : Finset Timestamp) : State :=
  match axis with
  | .row => { state with
      knownRows := insert id state.knownRows
      rowTokens := Function.update state.rowTokens id
        (removeSeen (state.rowTokens id) seen) }
  | .column => { state with
      knownColumns := insert id state.knownColumns
      columnTokens := Function.update state.columnTokens id
        (removeSeen (state.columnTokens id) seen) }

def applyAxis (state : State) (event : Event) (update : AxisUpdate) : State :=
  match update.after with
  | none => removeAxisSeen state update.axis update.id event.seen
  | some position =>
      setAxisPosition (addAxisKeep state update.axis update.id event.1)
        update.axis update.id event.1 position

def addVersions (timestamp : Timestamp) (values : Finset Nat) :
    Finset (Timestamp × Nat) :=
  values.image fun value => (timestamp, value)

def applyCell (state : State) (event : Event) (update : CellUpdate) : State :=
  let kept := (state.cells update.row update.column).filter fun version =>
    decide (version.1 ∉ update.overwrites)
  let next := kept ∪ addVersions event.1 update.after
  let live := addAxisKeep
    (addAxisKeep state .row update.row event.1) .column update.column event.1
  { live with
    cells := Function.update (live.cells update.row) update.column next
      |> Function.update live.cells update.row }

def applyRange (state : State) (event : Event) (update : RangeUpdate) : State :=
  let kept := (state.ranges update.id).filter fun version =>
    decide (version.1 ∉ update.overwrites)
  let added := match update.after with
    | some spec => {(event.1, spec)}
    | none => ∅
  { state with
    ranges := Function.update state.ranges update.id (kept ∪ added) }

def applyPurge (state : State) (marker : Purge) : State :=
  { state with
      cells := fun row column =>
        (state.cells row column).filter fun version =>
          decide ((version.1, (row, column)) ∉ marker.covered)
      purges := insert marker state.purges }

def step (state : State) (event : Event) : State :=
  match event.action with
  | .axis update => applyAxis state event update
  | .cell update => applyCell state event update
  | .range update => applyRange state event update
  | .purge marker => applyPurge state marker

def spec : SequentialMachine Event where
  State := State
  init := empty
  step := step

def latestPositions (versions : Finset PositionVersion) : Finset Position :=
  match maxNat? (versions.image Prod.fst) with
  | none => ∅
  | some timestamp =>
      (versions.filter fun version => decide (version.1 = timestamp)).image Prod.snd

def visibleIds (known : Finset StableId)
    (tokens : StableId → Finset Timestamp) : Finset StableId :=
  known.filter fun id => finsetNonemptyB (tokens id)

def versionValues (versions : Finset (Timestamp × Nat)) : Finset Nat :=
  versions.image Prod.snd

def versionPurged (state : State) (row column : StableId)
    (version : CellVersion) : Bool :=
  Finset.fold (· || ·) false (fun marker =>
    decide ((row, column) ∈ marker.coordinates ∧ version.1 ≤ marker.cutoff))
    state.purges

def view (state : State) : View where
  rows := visibleIds state.knownRows state.rowTokens
  columns := visibleIds state.knownColumns state.columnTokens
  rowPosition := fun id => latestPositions (state.rowPositions id)
  columnPosition := fun id => latestPositions (state.columnPositions id)
  cell := fun row column =>
    if finsetNonemptyB (state.rowTokens row) &&
        finsetNonemptyB (state.columnTokens column) then
      versionValues ((state.cells row column).filter fun version =>
        !versionPurged state row column version)
    else ∅
  range := fun id => (state.ranges id).image Prod.snd

def run (events : List Event) : State := spec.run events

/-! ## Declarative materialization invariant -/

def storedAxisIds (events : Finset Event) (axis : Axis) : Finset StableId :=
  events.biUnion fun event =>
    match event.action with
    | .axis update => if update.axis = axis then {update.id} else ∅
    | .cell update => match axis with
        | .row => {update.row}
        | .column => {update.column}
    | .range _ | .purge _ => ∅

def rawAxisKeepTimes (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset Timestamp :=
  (events.filter fun event => keepsAxis axis id event).image (fun event => event.1)

def rawLiveAxisTokens (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset Timestamp :=
  (rawAxisKeepTimes events axis id).filter fun timestamp =>
    !axisTokenRemoved events axis id timestamp

def SeenValid (events : Finset Event) : Prop :=
  ∀ event ∈ events, event.seen ⊆ eventTimes events

def axisPositionVersions (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset PositionVersion :=
  (events.filter fun event => axisCandidate axis id event).biUnion fun event =>
    match axisUpdate? event with
    | some update => (optionFinset update.after).image fun position =>
        (event.1, position)
    | none => ∅

def cellWriteOverwritten (events : Finset Event) (candidate : Event) : Bool :=
  Finset.fold (fun a b => a || b) false (fun later =>
    match cellUpdate? later with
    | some update => decide (candidate.1 ∈ update.overwrites)
    | none => false) events

def cellStored (events : Finset Event) (row column : StableId) :
    Finset CellVersion :=
  (events.filter fun event =>
      cellMatches row column event &&
      !cellWriteOverwritten events event &&
      match cellUpdate? event with
      | some update => decide ((event.1, (update.row, update.column)) ∉
          AegisSheet.GC.markerCoveredEntries events)
      | none => false).biUnion fun event =>
        match cellUpdate? event with
        | some update => addVersions event.1 update.after
        | none => ∅

theorem cellUpdate_exists_of_matches {event : Event} {row column : StableId}
    (matched : cellMatches row column event = true) :
    ∃ update, cellUpdate? event = some update := by
  cases found : cellUpdate? event with
  | none => simp [cellMatches, found] at matched
  | some update => exact ⟨update, rfl⟩

theorem mem_cellStored_iff {events : Finset Event} {row column : StableId}
    {timestamp : Timestamp} {value : CellValue} :
    (timestamp, value) ∈ cellStored events row column ↔
      ∃ event ∈ events, ∃ update,
        cellUpdate? event = some update ∧ update.row = row ∧
        update.column = column ∧ value ∈ update.after ∧
        event.1 = timestamp ∧ cellWriteOverwritten events event = false ∧
        (event.1, (update.row, update.column)) ∉
          AegisSheet.GC.markerCoveredEntries events := by
  unfold cellStored
  simp only [Finset.mem_biUnion, Finset.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨event, filterMember, stored⟩
    have member := filterMember.1
    have matched := filterMember.2.1.1
    have active := filterMember.2.1.2
    have uncovered := filterMember.2.2
    have hasUpdate := cellUpdate_exists_of_matches matched
    let update := Classical.choose hasUpdate
    have isCell : cellUpdate? event = some update :=
      Classical.choose_spec hasUpdate
    simp only [cellMatches, isCell, decide_eq_true_eq] at matched
    simp only [isCell, decide_eq_true_eq] at uncovered
    simp [isCell, addVersions] at stored
    exact ⟨event, member, update, isCell, matched.1, matched.2,
      stored.1, stored.2, by simpa using active, uncovered⟩
  · rintro ⟨event, member, update, isCell, sameRow, sameColumn, valueMember,
      sameTime, active, uncovered⟩
    refine ⟨event, ?_, ?_⟩
    · simp only [member, cellMatches, isCell, decide_eq_true_eq,
        Bool.not_eq_true, Bool.and_self, and_self, true_and]
      exact ⟨⟨⟨sameRow, sameColumn⟩, by simpa using active⟩,
        by simpa [← sameRow, ← sameColumn] using uncovered⟩
    · simp [isCell, addVersions, valueMember, sameTime]

def rangeStored (events : Finset Event) (id : RangeId) :
    Finset RangeVersion :=
  (events.filter fun event =>
      rangeMatches id event && !rangeOverwritten events event).biUnion fun event =>
        match rangeUpdate? event with
        | some update => (optionFinset update.after).image fun rangeSpec =>
            (event.1, rangeSpec)
        | none => ∅

theorem mem_rangeStored_iff {events : Finset Event} {id : RangeId}
    {timestamp : Timestamp} {rangeSpec : RangeSpec} :
    (timestamp, rangeSpec) ∈ rangeStored events id ↔
      ∃ event ∈ events, ∃ update,
        rangeUpdate? event = some update ∧ update.id = id ∧
        update.after = some rangeSpec ∧ event.1 = timestamp ∧
        rangeOverwritten events event = false := by
  unfold rangeStored
  simp only [Finset.mem_biUnion, Finset.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨event, ⟨member, matched, active⟩, value⟩
    cases isRange : rangeUpdate? event with
    | none => simp [rangeMatches, isRange] at matched
    | some update =>
        simp only [rangeMatches, isRange, decide_eq_true_eq] at matched
        cases after : update.after with
        | none => simp [optionFinset, isRange, after] at value
        | some candidate =>
            simp only [isRange, after, optionFinset, Finset.image_singleton,
              Finset.mem_singleton] at value
            simp only [Prod.mk.injEq] at value
            exact ⟨event, member, update, isRange, matched,
              after.trans (congrArg some value.2.symm), value.1.symm,
              by simpa using active⟩
  · rintro ⟨event, member, update, isRange, sameId, after, sameTime, active⟩
    refine ⟨event, ⟨member, ?_, ?_⟩, ?_⟩
    · simp [rangeMatches, isRange, sameId]
    · simpa using active
    · simp [isRange, after, optionFinset, sameTime]

def purgeMarkers (events : Finset Event) : Finset Purge :=
  events.biUnion fun event => match purge? event with
    | some marker => {marker}
    | none => ∅

def materialize (events : Finset Event) : State where
  knownRows := storedAxisIds events .row
  knownColumns := storedAxisIds events .column
  rowTokens := rawLiveAxisTokens events .row
  columnTokens := rawLiveAxisTokens events .column
  rowPositions := axisPositionVersions events .row
  columnPositions := axisPositionVersions events .column
  cells := cellStored events
  ranges := rangeStored events
  purges := purgeMarkers events

theorem materialize_empty : materialize ∅ = empty := by
  ext <;> simp [materialize, empty, storedAxisIds, rawLiveAxisTokens,
    rawAxisKeepTimes, axisTokenRemoved, axisPositionVersions, cellStored,
    rangeStored, purgeMarkers, cellWriteOverwritten, rangeOverwritten]

theorem storedAxisIds_insert (events : Finset Event) (e : Event) (axis : Axis) :
    storedAxisIds (insert e events) axis =
      (match e.action with
       | .axis update => if update.axis = axis then {update.id} else ∅
       | .cell update => match axis with
           | .row => {update.row}
           | .column => {update.column}
       | .range _ | .purge _ => ∅) ∪ storedAxisIds events axis := by
  unfold storedAxisIds
  rw [Finset.biUnion_insert]

theorem rawAxisKeepTimes_insert (events : Finset Event) (e : Event)
    (axis : Axis) (id : StableId) :
    rawAxisKeepTimes (insert e events) axis id =
      (if keepsAxis axis id e then {e.1} else ∅) ∪
        rawAxisKeepTimes events axis id := by
  unfold rawAxisKeepTimes
  rw [Finset.filter_insert]
  by_cases keeps : keepsAxis axis id e = true <;> simp [keeps]

theorem axisTokenRemoved_insert {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (axis : Axis) (id : StableId)
    (timestamp : Timestamp) :
    axisTokenRemoved (insert e events) axis id timestamp =
      ((removesAxis axis id e && decide (timestamp ∈ e.seen)) ||
        axisTokenRemoved events axis id timestamp) := by
  unfold axisTokenRemoved
  rw [Finset.fold_insert notmem]

theorem rawLiveAxisTokens_insert {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (axis : Axis) (id : StableId) :
    rawLiveAxisTokens (insert e events) axis id =
      (((if keepsAxis axis id e then {e.1} else ∅) ∪
          rawAxisKeepTimes events axis id).filter fun timestamp =>
        !((removesAxis axis id e && decide (timestamp ∈ e.seen)) ||
          axisTokenRemoved events axis id timestamp)) := by
  unfold rawLiveAxisTokens
  rw [rawAxisKeepTimes_insert]
  apply Finset.ext
  intro timestamp
  simp only [Finset.mem_filter]
  rw [axisTokenRemoved_insert notmem]

theorem axisIds_insert (events : Finset Event) (e : Event) (axis : Axis) :
    axisIds (insert e events) axis =
      (match axisUpdate? e with
       | some update => if update.axis = axis then {update.id} else ∅
       | none => ∅) ∪ axisIds events axis := by
  unfold axisIds
  rw [Finset.biUnion_insert]
  cases axisUpdate? e <;> rfl

theorem axisPositionVersions_insert (events : Finset Event) (e : Event)
    (axis : Axis) (id : StableId) :
    axisPositionVersions (insert e events) axis id =
      (if axisCandidate axis id e then
        match axisUpdate? e with
        | some update => (optionFinset update.after).image fun position =>
            (e.1, position)
        | none => ∅
       else ∅) ∪ axisPositionVersions events axis id := by
  unfold axisPositionVersions
  rw [Finset.filter_insert]
  by_cases candidate : axisCandidate axis id e = true <;>
    simp [candidate, Finset.biUnion_insert]

theorem purgeMarkers_insert (events : Finset Event) (e : Event) :
    purgeMarkers (insert e events) =
      (match purge? e with | some marker => {marker} | none => ∅) ∪
        purgeMarkers events := by
  unfold purgeMarkers
  rw [Finset.biUnion_insert]

theorem cellWriteOverwritten_insert {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (candidate : Event) :
    cellWriteOverwritten (insert e events) candidate =
      ((match cellUpdate? e with
       | some update => decide (candidate.1 ∈ update.overwrites)
       | none => false) || cellWriteOverwritten events candidate) := by
  unfold cellWriteOverwritten
  rw [Finset.fold_insert notmem]

theorem rangeOverwritten_insert {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (candidate : Event) :
    rangeOverwritten (insert e events) candidate =
      ((match rangeUpdate? e with
       | some update => decide (candidate.1 ∈ update.overwrites)
       | none => false) || rangeOverwritten events candidate) := by
  unfold rangeOverwritten
  rw [Finset.fold_insert notmem]
  rfl

theorem eventTime_mem {events : Finset Event} {e : Event} (member : e ∈ events) :
    e.1 ∈ eventTimes events := by
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, member, rfl⟩)

theorem event_not_mem_of_fresh {events : Finset Event} {e : Event}
    (fresh : e.1 ∉ eventTimes events) : e ∉ events := by
  intro member
  exact fresh (eventTime_mem member)

theorem eventTimes_mono {small large : Finset Event} (subset : small ⊆ large) :
    eventTimes small ⊆ eventTimes large := by
  intro timestamp member
  unfold eventTimes at member ⊢
  rcases Finset.mem_union.mp member with direct | covered
  · rw [Finset.mem_image] at direct
    obtain ⟨event, eventMember, rfl⟩ := direct
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨event, subset eventMember, rfl⟩)
  · rw [Finset.mem_biUnion] at covered
    obtain ⟨event, eventMember, timestampMember⟩ := covered
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨event, subset eventMember, timestampMember⟩)

theorem seenValid_insert {events : Finset Event} {e : Event}
    (valid : SeenValid events) (seen : e.seen = eventTimes events) :
    SeenValid (insert e events) := by
  intro candidate member
  rcases Finset.mem_insert.mp member with rfl | old
  · rw [seen]
    exact eventTimes_mono (Finset.subset_insert _ events)
  · exact fun timestamp timestampMember =>
      eventTimes_mono (Finset.subset_insert e events)
        (valid candidate old timestampMember)

theorem old_remove_does_not_see_fresh {events : Finset Event} {e : Event}
    (valid : SeenValid events) (fresh : e.1 ∉ eventTimes events)
    (axis : Axis) (id : StableId) :
    axisTokenRemoved events axis id e.1 = false := by
  apply Bool.eq_false_iff.mpr
  intro removed
  unfold axisTokenRemoved at removed
  rw [AegisSheet.GC.fold_or_eq_true_iff] at removed
  obtain ⟨remove, member, yes⟩ := removed
  simp only [Bool.and_eq_true, decide_eq_true_eq] at yes
  exact fresh (valid remove member yes.2)

theorem rawLiveAxisTokens_insert_axis {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (seenValid : SeenValid events)
    (fresh : e.1 ∉ eventTimes events) {update : AxisUpdate}
    (action : e.action = .axis update) (axis : Axis) (id : StableId) :
    rawLiveAxisTokens (insert e events) axis id =
      if update.axis = axis ∧ update.id = id then
        match update.after with
        | none => removeSeen (rawLiveAxisTokens events axis id) e.seen
        | some _ => insert e.1 (rawLiveAxisTokens events axis id)
      else rawLiveAxisTokens events axis id := by
  rw [rawLiveAxisTokens_insert notmem]
  apply Finset.ext
  intro timestamp
  have freshLive := old_remove_does_not_see_fresh seenValid fresh axis id
  by_cases sameAxis : update.axis = axis
  · by_cases sameId : update.id = id
    · subst axis
      subst id
      cases after : update.after <;>
        simp [keepsAxis, removesAxis, action, after, removeSeen,
          rawLiveAxisTokens, freshLive] <;> aesop
    · simp [keepsAxis, removesAxis, action, sameAxis, sameId,
        rawLiveAxisTokens]
  · simp [keepsAxis, removesAxis, action, sameAxis, rawLiveAxisTokens]

theorem rawLiveAxisTokens_insert_cell {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (seenValid : SeenValid events)
    (fresh : e.1 ∉ eventTimes events) {update : CellUpdate}
    (action : e.action = .cell update) (axis : Axis) (id : StableId) :
    rawLiveAxisTokens (insert e events) axis id =
      if (match axis with | .row => update.row | .column => update.column) = id
      then insert e.1 (rawLiveAxisTokens events axis id)
      else rawLiveAxisTokens events axis id := by
  rw [rawLiveAxisTokens_insert notmem]
  apply Finset.ext
  intro timestamp
  have freshLive := old_remove_does_not_see_fresh seenValid fresh axis id
  cases axis with
  | row =>
      by_cases same : update.row = id
      · simp [keepsAxis, removesAxis, action, same, rawLiveAxisTokens]
        by_cases ht : timestamp = e.1 <;> simp_all
      · simp [keepsAxis, removesAxis, action, same, rawLiveAxisTokens]
  | column =>
      by_cases same : update.column = id
      · simp [keepsAxis, removesAxis, action, same, rawLiveAxisTokens]
        by_cases ht : timestamp = e.1 <;> simp_all
      · simp [keepsAxis, removesAxis, action, same, rawLiveAxisTokens]

theorem rawLiveAxisTokens_insert_neutral {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (axis : Axis) (id : StableId)
    (notKeeps : keepsAxis axis id e = false)
    (notRemoves : removesAxis axis id e = false) :
    rawLiveAxisTokens (insert e events) axis id =
      rawLiveAxisTokens events axis id := by
  rw [rawLiveAxisTokens_insert notmem]
  apply Finset.ext
  intro timestamp
  simp [notKeeps, notRemoves, rawLiveAxisTokens]

theorem rawLiveAxisTokens_insert_axis_fun {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (seenValid : SeenValid events)
    (fresh : e.1 ∉ eventTimes events) {update : AxisUpdate}
    (action : e.action = .axis update) (axis : Axis) :
    rawLiveAxisTokens (insert e events) axis =
      if update.axis = axis then
        Function.update (rawLiveAxisTokens events axis) update.id
          (match update.after with
           | none => removeSeen (rawLiveAxisTokens events axis update.id) e.seen
           | some _ => insert e.1 (rawLiveAxisTokens events axis update.id))
      else rawLiveAxisTokens events axis := by
  funext id
  rw [rawLiveAxisTokens_insert_axis notmem seenValid fresh action]
  by_cases sameAxis : update.axis = axis
  · by_cases sameId : update.id = id
    · subst id
      simp [sameAxis, Function.update]
    · have reverse : id ≠ update.id := Ne.symm sameId
      simp [sameAxis, sameId, reverse, Function.update]
  · simp [sameAxis]

theorem rawLiveAxisTokens_insert_cell_fun {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (seenValid : SeenValid events)
    (fresh : e.1 ∉ eventTimes events) {update : CellUpdate}
    (action : e.action = .cell update) (axis : Axis) :
    rawLiveAxisTokens (insert e events) axis =
      let target := match axis with | .row => update.row | .column => update.column
      Function.update (rawLiveAxisTokens events axis) target
        (insert e.1 (rawLiveAxisTokens events axis target)) := by
  funext id
  rw [rawLiveAxisTokens_insert_cell notmem seenValid fresh action]
  cases axis with
  | row =>
      by_cases same : update.row = id
      · subst id
        simp [Function.update]
      · have reverse : id ≠ update.row := Ne.symm same
        simp [same, reverse, Function.update]
  | column =>
      by_cases same : update.column = id
      · subst id
        simp [Function.update]
      · have reverse : id ≠ update.column := Ne.symm same
        simp [same, reverse, Function.update]

theorem rawLiveAxisTokens_insert_range {events : Finset Event} {e : Event}
    (notmem : e ∉ events) {update : RangeUpdate}
    (action : e.action = .range update) (axis : Axis) :
    rawLiveAxisTokens (insert e events) axis =
      rawLiveAxisTokens events axis := by
  funext id
  exact rawLiveAxisTokens_insert_neutral notmem axis id
    (by simp [keepsAxis, action]) (by simp [removesAxis, action])

theorem rawLiveAxisTokens_insert_purge {events : Finset Event} {e : Event}
    (notmem : e ∉ events) {marker : Purge}
    (action : e.action = .purge marker) (axis : Axis) :
    rawLiveAxisTokens (insert e events) axis =
      rawLiveAxisTokens events axis := by
  funext id
  exact rawLiveAxisTokens_insert_neutral notmem axis id
    (by simp [keepsAxis, action]) (by simp [removesAxis, action])

theorem axisPositionVersions_insert_axis {events : Finset Event} {e : Event}
    {update : AxisUpdate} (action : e.action = .axis update) (axis : Axis) :
    axisPositionVersions (insert e events) axis =
      match update.after with
      | none => axisPositionVersions events axis
      | some position =>
          if update.axis = axis then
            Function.update (axisPositionVersions events axis) update.id
              (insert (e.1, position)
                (axisPositionVersions events axis update.id))
          else axisPositionVersions events axis := by
  funext id
  rw [axisPositionVersions_insert]
  cases after : update.after
  · simp [axisCandidate, axisUpdate?, action, after]
  · rename_i position
    by_cases sameAxis : update.axis = axis
    · by_cases sameId : update.id = id
      · subst id
        simp [axisCandidate, axisUpdate?, action, after, sameAxis,
          Function.update, optionFinset]
      · have reverse : id ≠ update.id := Ne.symm sameId
        simp [axisCandidate, axisUpdate?, action, after, sameAxis, sameId,
          reverse, Function.update]
    · simp [axisCandidate, axisUpdate?, action, after, sameAxis]

theorem axisPositionVersions_insert_nonaxis {events : Finset Event} {e : Event}
    (nonaxis : axisUpdate? e = none) (axis : Axis) :
    axisPositionVersions (insert e events) axis =
      axisPositionVersions events axis := by
  funext id
  rw [axisPositionVersions_insert]
  simp [axisCandidate, nonaxis]

theorem cellStored_insert_neutral {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (noncell : cellUpdate? e = none)
    (nonpurge : purge? e = none) :
    cellStored (insert e events) = cellStored events := by
  funext row column
  unfold cellStored
  rw [AegisSheet.GC.markerCoveredEntries_insert]
  simp only [nonpurge, Finset.empty_union]
  have overwritten : ∀ candidate,
      cellWriteOverwritten (insert e events) candidate =
        cellWriteOverwritten events candidate := by
    intro candidate
    rw [cellWriteOverwritten_insert notmem]
    simp [noncell]
  rw [Finset.filter_insert]
  simp [cellMatches, noncell, overwritten]

theorem rangeStored_insert_neutral {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (nonrange : rangeUpdate? e = none) :
    rangeStored (insert e events) = rangeStored events := by
  funext id
  unfold rangeStored
  have overwritten : ∀ candidate,
      rangeOverwritten (insert e events) candidate =
        rangeOverwritten events candidate := by
    intro candidate
    rw [rangeOverwritten_insert notmem]
    simp [nonrange]
  rw [Finset.filter_insert]
  simp [rangeMatches, nonrange, overwritten]

theorem applicable_seen {events : Finset Event} {e : Event}
    (guard : applicable e events) : e.seen = eventTimes events := by
  rcases guard with ⟨guard, _⟩
  unfold applicableB at guard
  simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
  exact guard.1.1.2

theorem clockAfter_of_fresh_and_seen {events : Finset Event} {e : Event}
    (clock : ∀ old ∈ events, old.1 < e.1) :
    ∀ old ∈ events, old.1 < e.1 := clock

theorem cellWriteOverwritten_new_false {events : Finset Event} {e : Event}
    (valid : AegisSheet.GC.StateValid events)
    (clock : ∀ old ∈ events, old.1 < e.1) :
    cellWriteOverwritten events e = false := by
  apply Bool.eq_false_iff.mpr
  intro overwritten
  unfold cellWriteOverwritten at overwritten
  rw [AegisSheet.GC.fold_or_eq_true_iff] at overwritten
  obtain ⟨later, laterMember, yes⟩ := overwritten
  cases laterCell : cellUpdate? later with
  | none => simp [laterCell] at yes
  | some update =>
      simp only [laterCell, decide_eq_true_eq] at yes
      have before :=
        (AegisSheet.GC.metadata_cell_overwrite valid laterMember laterCell yes).1
      exact (Nat.not_lt_of_ge (Nat.le_of_lt (clock later laterMember)) before)

theorem metadata_range_overwrite {events : Finset Event}
    (valid : AegisSheet.GC.StateValid events) {later : Event}
    {update : RangeUpdate} (member : later ∈ events)
    (isRange : rangeUpdate? later = some update) {overwritten : Timestamp}
    (overwrites : overwritten ∈ update.overwrites) :
    overwritten < later.1 ∧ ∃ prior ∈ events, ∃ priorUpdate,
      rangeUpdate? prior = some priorUpdate ∧ prior.1 = overwritten ∧
        priorUpdate.id = update.id := by
  have metadata := valid later member
  unfold metadataValidB at metadata
  have noncell : cellUpdate? later = none :=
    AegisSheet.GC.cellUpdate_none_of_rangeUpdate_some isRange
  simp only [noncell, isRange] at metadata
  rw [AegisSheet.GC.fold_and_eq_true_iff] at metadata
  have one := metadata overwritten overwrites
  simp only [Bool.and_eq_true, decide_eq_true_eq] at one
  refine ⟨one.1, ?_⟩
  rw [AegisSheet.GC.fold_or_eq_true_iff] at one
  obtain ⟨prior, priorMember, priorValid⟩ := one.2
  cases priorRange : rangeUpdate? prior with
  | none => simp [priorRange] at priorValid
  | some priorUpdate =>
      simp only [priorRange, decide_eq_true_eq] at priorValid
      exact ⟨prior, priorMember, priorUpdate, priorRange, priorValid⟩

theorem rangeOverwritten_new_false {events : Finset Event} {e : Event}
    (valid : AegisSheet.GC.StateValid events)
    (clock : ∀ old ∈ events, old.1 < e.1) :
    rangeOverwritten events e = false := by
  apply Bool.eq_false_iff.mpr
  intro overwritten
  unfold rangeOverwritten at overwritten
  rw [AegisSheet.GC.fold_or_eq_true_iff] at overwritten
  obtain ⟨later, laterMember, yes⟩ := overwritten
  cases laterRange : rangeUpdate? later with
  | none => simp [laterRange] at yes
  | some update =>
      simp only [laterRange, decide_eq_true_eq] at yes
      have before := (metadata_range_overwrite valid laterMember laterRange yes).1
      exact (Nat.not_lt_of_ge (Nat.le_of_lt (clock later laterMember)) before)

theorem rangeStored_insert_range {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (valid : AegisSheet.GC.StateValid events)
    (unique : AegisSheet.GC.TimestampUnique events)
    (newMetadata : metadataValidB events e = true)
    (clock : ∀ old ∈ events, old.1 < e.1) {update : RangeUpdate}
    (action : e.action = .range update) :
    rangeStored (insert e events) =
      Function.update (rangeStored events) update.id
        (((rangeStored events update.id).filter fun version =>
            decide (version.1 ∉ update.overwrites)) ∪
          match update.after with
          | some rangeSpec => {(e.1, rangeSpec)}
          | none => ∅) := by
  have newActive := rangeOverwritten_new_false valid clock
  have overwritten : ∀ candidate,
      rangeOverwritten (insert e events) candidate =
        (decide (candidate.1 ∈ update.overwrites) ||
          rangeOverwritten events candidate) := by
    intro candidate
    rw [rangeOverwritten_insert notmem]
    simp [rangeUpdate?, action]
  funext id
  by_cases same : update.id = id
  · subst id
    apply Finset.ext
    rintro ⟨timestamp, rangeSpec⟩
    rw [mem_rangeStored_iff]
    simp only [Function.update_self, Finset.mem_union, Finset.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨candidate, member, candidateUpdate, isRange, sameId,
          after, sameTime, active⟩
      rcases Finset.mem_insert.mp member with rfl | old
      · simp [rangeUpdate?, action] at isRange
        subst candidateUpdate
        right
        cases next : update.after with
        | none => simp [next] at after
        | some nextSpec =>
            simp only [next] at after
            have valueEq := Option.some.inj after
            subst rangeSpec
            simp [next, optionFinset, sameTime]
      · left
        have activeParts : candidate.1 ∉ update.overwrites ∧
            rangeOverwritten events candidate = false := by
          rw [overwritten candidate] at active
          simpa only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
            using active
        constructor
        · rw [mem_rangeStored_iff]
          exact ⟨candidate, old, candidateUpdate, isRange, sameId, after,
            sameTime, activeParts.2⟩
        · simpa [sameTime] using activeParts.1
    · rintro (⟨oldMember, notOverwritten⟩ | added)
      · rw [mem_rangeStored_iff] at oldMember
        obtain ⟨candidate, old, candidateUpdate, isRange, sameId, after,
            sameTime, active⟩ := oldMember
        refine ⟨candidate, Finset.mem_insert_of_mem old, candidateUpdate,
          isRange, sameId, after, sameTime, ?_⟩
        rw [overwritten candidate]
        simp [active, sameTime, notOverwritten]
      · cases next : update.after with
        | none => simp [next] at added
        | some nextSpec =>
            simp only [next, Finset.mem_singleton, Prod.mk.injEq] at added
            have newValid : AegisSheet.GC.StateValid (insert e events) :=
              AegisSheet.GC.stateValid_insert valid newMetadata
            have notSelf : e.1 ∉ update.overwrites := by
              intro self
              have before := (metadata_range_overwrite newValid
                (Finset.mem_insert_self e events)
                (later := e) (update := update)
                (by simp [rangeUpdate?, action]) self).1
              exact (Nat.lt_irrefl e.1 before)
            have newActiveFull :
                rangeOverwritten (insert e events) e = false := by
              rw [overwritten e]
              simp [notSelf, newActive]
            refine ⟨e, Finset.mem_insert_self e events, update,
              by simp [rangeUpdate?, action], rfl, ?_, ?_, newActiveFull⟩
            · simpa [next] using added.2.symm
            · exact added.1.symm
  · have reverse : id ≠ update.id := Ne.symm same
    apply Finset.ext
    rintro ⟨timestamp, rangeSpec⟩
    rw [mem_rangeStored_iff]
    simp only [Function.update_of_ne reverse]
    rw [mem_rangeStored_iff]
    constructor
    · rintro ⟨candidate, member, candidateUpdate, isRange, candidateId,
          after, sameTime, active⟩
      rcases Finset.mem_insert.mp member with rfl | old
      · simp [rangeUpdate?, action] at isRange
        subst candidateUpdate
        exact False.elim (same candidateId)
      · have activeParts : candidate.1 ∉ update.overwrites ∧
            rangeOverwritten events candidate = false := by
          rw [overwritten candidate] at active
          simpa only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
            using active
        exact ⟨candidate, old, candidateUpdate, isRange, candidateId, after,
          sameTime, activeParts.2⟩
    · rintro ⟨candidate, old, candidateUpdate, isRange, candidateId,
          after, sameTime, active⟩
      have notOverwritten : candidate.1 ∉ update.overwrites := by
        intro overwrittenMember
        have newValid : AegisSheet.GC.StateValid (insert e events) :=
          AegisSheet.GC.stateValid_insert valid newMetadata
        obtain ⟨before, prior, priorMember, priorUpdate, priorRange, priorTime,
            priorId⟩ := metadata_range_overwrite newValid
              (Finset.mem_insert_self e events)
              (later := e) (update := update)
              (by simp [rangeUpdate?, action]) overwrittenMember
        have priorOld : prior ∈ events := by
          rcases Finset.mem_insert.mp priorMember with samePrior | oldPrior
          · subst prior
            exfalso
            exact Nat.lt_irrefl e.1 (priorTime.trans_lt before)
          · exact oldPrior
        have sameEvent := unique prior priorOld candidate old priorTime
        have sameUpdate : priorUpdate = candidateUpdate := by
          subst prior
          exact Option.some.inj (priorRange.symm.trans isRange)
        exact same (priorId.symm.trans (congrArg RangeUpdate.id sameUpdate) |>.trans candidateId)
      refine ⟨candidate, Finset.mem_insert_of_mem old, candidateUpdate, isRange,
        candidateId, after, sameTime, ?_⟩
      rw [overwritten candidate]
      simp [notOverwritten, active]

theorem markerCovered_time_mem_eventTimes {events : Finset Event}
    {timestamp : Timestamp} {coordinate : Coordinate}
    (covered : (timestamp, coordinate) ∈
      AegisSheet.GC.markerCoveredEntries events) :
    timestamp ∈ eventTimes events := by
  rcases coordinate with ⟨row, column⟩
  rw [AegisSheet.GC.eventTimes_eq]
  apply Finset.mem_union_right
  unfold AegisSheet.GC.markerCoveredTimes
  exact Finset.mem_image.mpr ⟨(timestamp, (row, column)), covered, rfl⟩

theorem cellStored_insert_cell {events : Finset Event} {e : Event}
    (notmem : e ∉ events) (valid : AegisSheet.GC.StateValid events)
    (unique : AegisSheet.GC.TimestampUnique events)
    (newMetadata : metadataValidB events e = true)
    (fresh : e.1 ∉ eventTimes events)
    (clock : ∀ old ∈ events, old.1 < e.1) {update : CellUpdate}
    (action : e.action = .cell update) :
    cellStored (insert e events) =
      Function.update (cellStored events) update.row
        (Function.update (cellStored events update.row) update.column
          (((cellStored events update.row update.column).filter fun version =>
              decide (version.1 ∉ update.overwrites)) ∪
            addVersions e.1 update.after)) := by
  have oldActive := cellWriteOverwritten_new_false valid clock
  have overwritten : ∀ candidate,
      cellWriteOverwritten (insert e events) candidate =
        (decide (candidate.1 ∈ update.overwrites) ||
          cellWriteOverwritten events candidate) := by
    intro candidate
    rw [cellWriteOverwritten_insert notmem]
    simp [cellUpdate?, action]
  have covered : AegisSheet.GC.markerCoveredEntries (insert e events) =
      AegisSheet.GC.markerCoveredEntries events := by
    rw [AegisSheet.GC.markerCoveredEntries_insert]
    simp [purge?, action]
  have newValid : AegisSheet.GC.StateValid (insert e events) :=
    AegisSheet.GC.stateValid_insert valid newMetadata
  have notSelfOverwritten : e.1 ∉ update.overwrites := by
    intro self
    have before := (AegisSheet.GC.metadata_cell_overwrite newValid
      (Finset.mem_insert_self e events) (later := e) (update := update)
      (by simp [cellUpdate?, action]) self).1
    exact Nat.lt_irrefl e.1 before
  have newActive : cellWriteOverwritten (insert e events) e = false := by
    rw [overwritten e]
    simp [notSelfOverwritten, oldActive]
  have newUncovered :
      (e.1, (update.row, update.column)) ∉
        AegisSheet.GC.markerCoveredEntries (insert e events) := by
    rw [covered]
    intro member
    exact fresh (markerCovered_time_mem_eventTimes member)
  funext row column
  by_cases sameRow : update.row = row
  · subst row
    by_cases sameColumn : update.column = column
    · subst column
      simp only [Function.update_self]
      apply Finset.ext
      rintro ⟨timestamp, value⟩
      rw [mem_cellStored_iff]
      simp only [Finset.mem_union, Finset.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨candidate, member, candidateUpdate, isCell, rowEq, columnEq,
          valueMember, sameTime, active, uncovered⟩
        rcases Finset.mem_insert.mp member with sameEvent | old
        · subst candidate
          have updateEq : candidateUpdate = update :=
            Option.some.inj (isCell.symm.trans (by simp [cellUpdate?, action]))
          subst candidateUpdate
          right
          simp [addVersions, valueMember, sameTime]
        · left
          have activeParts : candidate.1 ∉ update.overwrites ∧
              cellWriteOverwritten events candidate = false := by
            rw [overwritten candidate] at active
            simpa only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
              using active
          constructor
          · rw [mem_cellStored_iff]
            exact ⟨candidate, old, candidateUpdate, isCell, rowEq, columnEq,
              valueMember, sameTime, activeParts.2, by simpa [covered] using uncovered⟩
          · simpa [sameTime] using activeParts.1
      · rintro (⟨oldMember, notOverwritten⟩ | added)
        · rw [mem_cellStored_iff] at oldMember
          obtain ⟨candidate, old, candidateUpdate, isCell, rowEq, columnEq,
              valueMember, sameTime, active, uncovered⟩ := oldMember
          refine ⟨candidate, Finset.mem_insert_of_mem old, candidateUpdate,
            isCell, rowEq, columnEq, valueMember, sameTime, ?_, ?_⟩
          · rw [overwritten candidate]
            simp [active, sameTime, notOverwritten]
          · simpa [covered] using uncovered
        · simp [addVersions] at added
          refine ⟨e, Finset.mem_insert_self e events, update,
            by simp [cellUpdate?, action], rfl, rfl, added.1, added.2,
            newActive, newUncovered⟩
    · have reverseColumn : column ≠ update.column := Ne.symm sameColumn
      simp only [Function.update_self, Function.update_of_ne reverseColumn]
      apply Finset.ext
      rintro ⟨timestamp, value⟩
      rw [mem_cellStored_iff, mem_cellStored_iff]
      constructor
      · rintro ⟨candidate, member, candidateUpdate, isCell, rowEq, columnEq,
          valueMember, sameTime, active, uncovered⟩
        rcases Finset.mem_insert.mp member with sameEvent | old
        · subst candidate
          simp [cellUpdate?, action] at isCell
          subst candidateUpdate
          exact False.elim (sameColumn columnEq)
        · have activeParts : candidate.1 ∉ update.overwrites ∧
              cellWriteOverwritten events candidate = false := by
            rw [overwritten candidate] at active
            simpa only [Bool.or_eq_false_iff, decide_eq_false_iff_not] using active
          exact ⟨candidate, old, candidateUpdate, isCell, rowEq, columnEq,
            valueMember, sameTime, activeParts.2, by simpa [covered] using uncovered⟩
      · rintro ⟨candidate, old, candidateUpdate, isCell, rowEq, columnEq,
          valueMember, sameTime, active, uncovered⟩
        have notOverwritten : candidate.1 ∉ update.overwrites := by
          intro overwriteMember
          obtain ⟨_, prior, priorMember, priorUpdate, priorCell, priorTime,
              priorRow, priorColumn⟩ := AegisSheet.GC.metadata_cell_overwrite
                newValid (Finset.mem_insert_self e events) (later := e)
                (update := update) (by simp [cellUpdate?, action]) overwriteMember
          have priorOld : prior ∈ events := by
            rcases Finset.mem_insert.mp priorMember with samePrior | oldPrior
            · subst prior
              exact False.elim (Nat.lt_irrefl e.1 (priorTime.trans_lt ‹_›))
            · exact oldPrior
          have sameEvent := unique prior priorOld candidate old priorTime
          subst prior
          have updateEq : priorUpdate = candidateUpdate :=
            Option.some.inj (priorCell.symm.trans isCell)
          exact sameColumn (priorColumn.symm.trans
            (congrArg CellUpdate.column updateEq) |>.trans columnEq)
        refine ⟨candidate, Finset.mem_insert_of_mem old, candidateUpdate,
          isCell, rowEq, columnEq, valueMember, sameTime, ?_, ?_⟩
        · rw [overwritten candidate]
          simp [notOverwritten, active]
        · simpa [covered] using uncovered
  · have reverseRow : row ≠ update.row := Ne.symm sameRow
    simp only [Function.update_of_ne reverseRow]
    apply Finset.ext
    rintro ⟨timestamp, value⟩
    rw [mem_cellStored_iff, mem_cellStored_iff]
    constructor
    · rintro ⟨candidate, member, candidateUpdate, isCell, rowEq, columnEq,
        valueMember, sameTime, active, uncovered⟩
      rcases Finset.mem_insert.mp member with sameEvent | old
      · subst candidate
        simp [cellUpdate?, action] at isCell
        subst candidateUpdate
        exact False.elim (sameRow rowEq)
      · have activeParts : candidate.1 ∉ update.overwrites ∧
            cellWriteOverwritten events candidate = false := by
          rw [overwritten candidate] at active
          simpa only [Bool.or_eq_false_iff, decide_eq_false_iff_not] using active
        exact ⟨candidate, old, candidateUpdate, isCell, rowEq, columnEq,
          valueMember, sameTime, activeParts.2, by simpa [covered] using uncovered⟩
    · rintro ⟨candidate, old, candidateUpdate, isCell, rowEq, columnEq,
        valueMember, sameTime, active, uncovered⟩
      have notOverwritten : candidate.1 ∉ update.overwrites := by
        intro overwriteMember
        obtain ⟨before, prior, priorMember, priorUpdate, priorCell, priorTime,
            priorRow, priorColumn⟩ := AegisSheet.GC.metadata_cell_overwrite
              newValid (Finset.mem_insert_self e events) (later := e)
              (update := update) (by simp [cellUpdate?, action]) overwriteMember
        have priorOld : prior ∈ events := by
          rcases Finset.mem_insert.mp priorMember with samePrior | oldPrior
          · subst prior
            exact False.elim (Nat.lt_irrefl e.1 (priorTime.trans_lt before))
          · exact oldPrior
        have sameEvent := unique prior priorOld candidate old priorTime
        subst prior
        have updateEq : priorUpdate = candidateUpdate :=
          Option.some.inj (priorCell.symm.trans isCell)
        exact sameRow (priorRow.symm.trans
          (congrArg CellUpdate.row updateEq) |>.trans rowEq)
      refine ⟨candidate, Finset.mem_insert_of_mem old, candidateUpdate,
        isCell, rowEq, columnEq, valueMember, sameTime, ?_, ?_⟩
      · rw [overwritten candidate]
        simp [notOverwritten, active]
      · simpa [covered] using uncovered

theorem cellStored_insert_purge {events : Finset Event} {e : Event}
    (notmem : e ∉ events) {marker : Purge}
    (action : e.action = .purge marker) :
    cellStored (insert e events) = fun row column =>
      (cellStored events row column).filter fun version =>
        decide ((version.1, (row, column)) ∉ marker.covered) := by
  have noncell : cellUpdate? e = none := by simp [cellUpdate?, action]
  have overwritten : ∀ candidate,
      cellWriteOverwritten (insert e events) candidate =
        cellWriteOverwritten events candidate := by
    intro candidate
    rw [cellWriteOverwritten_insert notmem]
    simp [noncell]
  have covered := AegisSheet.GC.markerCoveredEntries_insert events e
  simp [purge?, action] at covered
  funext row column
  apply Finset.ext
  rintro ⟨timestamp, value⟩
  rw [mem_cellStored_iff]
  simp only [Finset.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨candidate, member, update, isCell, rowEq, columnEq, valueMember,
      sameTime, active, uncovered⟩
    rcases Finset.mem_insert.mp member with sameEvent | old
    · subst candidate
      simp [noncell] at isCell
    · constructor
      · rw [mem_cellStored_iff]
        have uncoveredParts :
            (candidate.1, (update.row, update.column)) ∉ marker.covered ∧
            (candidate.1, (update.row, update.column)) ∉
              AegisSheet.GC.markerCoveredEntries events := by
          rw [covered] at uncovered
          simpa only [Finset.mem_union, not_or] using uncovered
        exact ⟨candidate, old, update, isCell, rowEq, columnEq, valueMember,
          sameTime, by simpa [overwritten] using active, uncoveredParts.2⟩
      · rw [covered] at uncovered
        have notNew :
            (candidate.1, (update.row, update.column)) ∉ marker.covered := by
          have parts :
              (candidate.1, (update.row, update.column)) ∉ marker.covered ∧
              (candidate.1, (update.row, update.column)) ∉
                AegisSheet.GC.markerCoveredEntries events := by
            simpa only [Finset.mem_union, not_or] using uncovered
          exact parts.1
        simpa [sameTime, rowEq, columnEq] using notNew
  · rintro ⟨oldMember, notCovered⟩
    rw [mem_cellStored_iff] at oldMember
    obtain ⟨candidate, old, update, isCell, rowEq, columnEq, valueMember,
      sameTime, active, uncovered⟩ := oldMember
    refine ⟨candidate, Finset.mem_insert_of_mem old, update, isCell, rowEq,
      columnEq, valueMember, sameTime, ?_, ?_⟩
    · simpa [overwritten] using active
    · rw [covered]
      simpa only [Finset.mem_union, not_or] using
        And.intro (by simpa [sameTime, rowEq, columnEq] using notCovered) uncovered

theorem materialize_insert_of_facts {events : Finset Event} {e : Event}
    (valid : AegisSheet.GC.StateValid events)
    (unique : AegisSheet.GC.TimestampUnique events)
    (seenValid : SeenValid events)
    (fresh : e.1 ∉ eventTimes events)
    (newMetadata : metadataValidB events e = true)
    (clock : ∀ old ∈ events, old.1 < e.1) :
    step (materialize events) e = materialize (insert e events) := by
  have notmem := event_not_mem_of_fresh fresh
  cases action : e.2.2.command.effect with
  | axis update =>
      have action' : e.action = .axis update := action
      have rowTokens := rawLiveAxisTokens_insert_axis_fun notmem seenValid
        fresh action' .row
      have columnTokens := rawLiveAxisTokens_insert_axis_fun notmem seenValid
        fresh action' .column
      have rowPositions := axisPositionVersions_insert_axis
        (events := events) action' .row
      have columnPositions := axisPositionVersions_insert_axis
        (events := events) action' .column
      have noncell : cellUpdate? e = none := by simp [cellUpdate?, action']
      have nonrange : rangeUpdate? e = none := by simp [rangeUpdate?, action']
      have nonpurge : purge? e = none := by simp [purge?, action']
      have cells := cellStored_insert_neutral notmem noncell nonpurge
      have ranges := rangeStored_insert_neutral notmem nonrange
      cases haxis : update.axis <;> cases hafter : update.after <;>
        apply State.ext <;>
        simp [step, action, materialize, applyAxis, applyCell, applyRange,
          applyPurge, addAxisKeep, setAxisPosition, removeAxisSeen,
          storedAxisIds_insert, rawLiveAxisTokens_insert,
          axisPositionVersions_insert, purgeMarkers_insert,
          Event.action, axisUpdate?, cellUpdate?, rangeUpdate?, purge?,
          haxis, hafter, rowTokens, columnTokens, rowPositions,
          columnPositions, cells, ranges]
  | cell update =>
      have action' : e.action = .cell update := action
      have rowTokens := rawLiveAxisTokens_insert_cell_fun notmem seenValid
        fresh action' .row
      have columnTokens := rawLiveAxisTokens_insert_cell_fun notmem seenValid
        fresh action' .column
      have nonaxis : axisUpdate? e = none := by simp [axisUpdate?, action']
      have rowPositions := axisPositionVersions_insert_nonaxis
        (events := events) nonaxis .row
      have columnPositions := axisPositionVersions_insert_nonaxis
        (events := events) nonaxis .column
      have nonrange : rangeUpdate? e = none := by simp [rangeUpdate?, action']
      have ranges := rangeStored_insert_neutral notmem nonrange
      have cells := cellStored_insert_cell notmem valid unique newMetadata
        fresh clock action'
      apply State.ext <;>
        simp [step, action, materialize, applyAxis, applyCell, applyRange,
          applyPurge, addAxisKeep, setAxisPosition, removeAxisSeen,
          storedAxisIds_insert, rawLiveAxisTokens_insert,
          axisPositionVersions_insert, purgeMarkers_insert,
          Event.action, axisUpdate?, cellUpdate?, rangeUpdate?, purge?,
          rowTokens, columnTokens, rowPositions, columnPositions, ranges, cells]

  | range update =>
      have action' : e.action = .range update := action
      have rowTokens := rawLiveAxisTokens_insert_range notmem action' .row
      have columnTokens := rawLiveAxisTokens_insert_range notmem action' .column
      have nonaxis : axisUpdate? e = none := by simp [axisUpdate?, action']
      have rowPositions := axisPositionVersions_insert_nonaxis
        (events := events) nonaxis .row
      have columnPositions := axisPositionVersions_insert_nonaxis
        (events := events) nonaxis .column
      have noncell : cellUpdate? e = none := by simp [cellUpdate?, action']
      have nonpurge : purge? e = none := by simp [purge?, action']
      have cells := cellStored_insert_neutral notmem noncell nonpurge
      have rangeStore := rangeStored_insert_range notmem valid unique
        newMetadata clock action'
      apply State.ext <;>
        simp [step, action, materialize, applyAxis, applyCell, applyRange,
          applyPurge, addAxisKeep, setAxisPosition, removeAxisSeen,
          storedAxisIds_insert, rawLiveAxisTokens_insert,
          axisPositionVersions_insert, purgeMarkers_insert,
          Event.action, axisUpdate?, cellUpdate?, rangeUpdate?, purge?,
          rowTokens, columnTokens, rowPositions, columnPositions, cells,
          rangeStore]
  | purge marker =>
      have action' : e.action = .purge marker := action
      have rowTokens := rawLiveAxisTokens_insert_purge notmem action' .row
      have columnTokens := rawLiveAxisTokens_insert_purge notmem action' .column
      have nonaxis : axisUpdate? e = none := by simp [axisUpdate?, action']
      have rowPositions := axisPositionVersions_insert_nonaxis
        (events := events) nonaxis .row
      have columnPositions := axisPositionVersions_insert_nonaxis
        (events := events) nonaxis .column
      have nonrange : rangeUpdate? e = none := by simp [rangeUpdate?, action']
      have ranges := rangeStored_insert_neutral notmem nonrange
      have cells := cellStored_insert_purge notmem action'
      apply State.ext <;>
        simp [step, action, materialize, applyAxis, applyCell, applyRange,
          applyPurge, addAxisKeep, setAxisPosition, removeAxisSeen,
          storedAxisIds_insert, rawLiveAxisTokens_insert,
          axisPositionVersions_insert, purgeMarkers_insert,
          Event.action, axisUpdate?, cellUpdate?, rangeUpdate?, purge?,
          rowTokens, columnTokens, rowPositions, columnPositions, ranges, cells]

theorem materialize_insert {events : Finset Event} {e : Event}
    (valid : AegisSheet.GC.StateValid events)
    (unique : AegisSheet.GC.TimestampUnique events)
    (seenValid : SeenValid events)
    (guard : applicable e events)
    (clock : ∀ old ∈ events, old.1 < e.1) :
    step (materialize events) e = materialize (insert e events) :=
  materialize_insert_of_facts valid unique seenValid
    (AegisSheet.GC.applicable_fresh guard)
    (AegisSheet.GC.applicable_metadataValid guard) clock

theorem linearMintHistory_prefix {ops initial suffix : List Event}
    (history : LinearMintHistory D AegisSheet.applicable ops)
    (split : ops = initial ++ suffix) :
    LinearMintHistory D AegisSheet.applicable initial := by
  constructor
  · intro (pre : List Event) (e : Event) (post : List Event) initialSplit
    apply history.guarded pre e (post ++ suffix)
    calc
      ops = initial ++ suffix := split
      _ = (pre ++ e :: post) ++ suffix := by rw [initialSplit]
      _ = pre ++ e :: (post ++ suffix) := by simp [List.append_assoc]
  · intro (pre : List Event) (e : Event) (post : List Event) initialSplit
      (old : Event) oldMember
    apply history.clocked pre e (post ++ suffix)
      (by
        calc
          ops = initial ++ suffix := split
          _ = (pre ++ e :: post) ++ suffix := by rw [initialSplit]
          _ = pre ++ e :: (post ++ suffix) := by simp [List.append_assoc])
      old oldMember

structure HistoryFacts (ops : List Event) : Prop where
  stateValid : AegisSheet.GC.StateValid ops.toFinset
  timestampUnique : AegisSheet.GC.TimestampUnique ops.toFinset
  seenValid : SeenValid ops.toFinset
  materialized : run ops = materialize ops.toFinset

theorem mem_rangeValues_iff {events : Finset Event} {id : RangeId}
    {rangeSpec : RangeSpec} :
    rangeSpec ∈ rangeValues events id ↔
      ∃ event ∈ events, ∃ update,
        rangeUpdate? event = some update ∧ update.id = id ∧
        update.after = some rangeSpec ∧ rangeOverwritten events event = false := by
  unfold rangeValues
  simp only [Finset.mem_biUnion, Finset.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨event, ⟨member, matched, active⟩, value⟩
    have hasUpdate : ∃ update, rangeUpdate? event = some update := by
      cases found : rangeUpdate? event with
      | none => simp [rangeMatches, found] at matched
      | some update => exact ⟨update, rfl⟩
    let update := Classical.choose hasUpdate
    have isRange : rangeUpdate? event = some update :=
      Classical.choose_spec hasUpdate
    simp only [rangeMatches, isRange, decide_eq_true_eq] at matched
    cases after : update.after with
    | none => simp [isRange, after, optionFinset] at value
    | some candidate =>
        simp only [isRange, after, optionFinset, Finset.mem_singleton] at value
        subst candidate
        exact ⟨event, member, update, isRange, matched, after,
          by simpa using active⟩
  · rintro ⟨event, member, update, isRange, sameId, after, active⟩
    refine ⟨event, ⟨member, ?_, ?_⟩, ?_⟩
    · simp [rangeMatches, isRange, sameId]
    · simpa using active
    · simp [isRange, after, optionFinset]

theorem rangeStored_values (events : Finset Event) (id : RangeId) :
    (rangeStored events id).image Prod.snd = rangeValues events id := by
  apply Finset.ext
  intro rangeSpec
  simp only [Finset.mem_image, mem_rangeValues_iff]
  constructor
  · rintro ⟨⟨timestamp, candidate⟩, stored, valueEq⟩
    simp only at valueEq
    subst candidate
    rw [mem_rangeStored_iff] at stored
    obtain ⟨event, member, update, isRange, sameId, after, _, active⟩ := stored
    exact ⟨event, member, update, isRange, sameId, after, active⟩
  · rintro ⟨event, member, update, isRange, sameId, after, active⟩
    refine ⟨(event.1, rangeSpec), ?_, rfl⟩
    rw [mem_rangeStored_iff]
    exact ⟨event, member, update, isRange, sameId, after, rfl, active⟩


theorem linearMintHistory_facts {ops : List Event}
    (history : LinearMintHistory D AegisSheet.applicable ops) :
    HistoryFacts ops := by
  induction ops using List.reverseRecOn with
  | nil =>
      refine ⟨?_, AegisSheet.GC.timestampUnique_empty, ?_, ?_⟩
      · simp [AegisSheet.GC.StateValid]
      · simp [SeenValid]
      · rfl
  | append_singleton initial e ih =>
      have initialHistory := linearMintHistory_prefix history
        (initial := initial) (suffix := [e]) rfl
      have initialFacts := ih initialHistory
      have guard : applicable e initial.toFinset := by
        have guarded := history.guarded initial e [] (by simp)
        simpa [AegisSheet.applySeq_eq_toFinset] using guarded
      have clock : ∀ old ∈ initial.toFinset, old.1 < e.1 := by
        intro old oldMember
        apply history.clocked initial e [] (by simp) old
        simpa using oldMember
      have fresh := AegisSheet.GC.applicable_fresh guard
      have metadata := AegisSheet.GC.applicable_metadataValid guard
      have seen := applicable_seen guard
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using AegisSheet.GC.stateValid_insert
          initialFacts.stateValid metadata
      · simpa using AegisSheet.GC.timestampUnique_insert
          initialFacts.timestampUnique fresh
      · simpa using seenValid_insert initialFacts.seenValid seen
      · change spec.run (initial ++ [e]) = materialize (initial ++ [e]).toFinset
        rw [SequentialMachine.run_append_single]
        change step (run initial) e = materialize (initial ++ [e]).toFinset
        rw [initialFacts.materialized]
        simpa using materialize_insert initialFacts.stateValid
          initialFacts.timestampUnique initialFacts.seenValid guard clock

theorem guarded_history_materializes {ops : List Event}
    (history : LinearMintHistory D AegisSheet.applicable ops) :
    run ops = materialize ops.toFinset :=
  (linearMintHistory_facts history).materialized

def ObservationInvariant (events : Finset Event) : Prop :=
  view (materialize events) = AegisSheet.view events

theorem observationInvariant_empty : ObservationInvariant ∅ := by
  rfl

def CellAxesKnown (events : Finset Event) : Prop :=
  ∀ event ∈ events, ∀ update, cellUpdate? event = some update →
    axisKnown events .row update.row = true ∧
      axisKnown events .column update.column = true

def CoveredWitnessed (events : Finset Event) : Prop :=
  ∀ entry ∈ AegisSheet.GC.markerCoveredEntries events,
    ∃ event ∈ events, ∃ update,
      cellUpdate? event = some update ∧ event.1 = entry.1 ∧
        (update.row, update.column) = entry.2

theorem axisKnown_iff_mem_axisIds {events : Finset Event} {axis : Axis}
    {id : StableId} :
    axisKnown events axis id = true ↔ id ∈ axisIds events axis := by
  unfold axisKnown axisIds
  rw [AegisSheet.GC.fold_or_eq_true_iff]
  constructor
  · rintro ⟨event, member, known⟩
    rw [Finset.mem_biUnion]
    refine ⟨event, member, ?_⟩
    cases found : axisUpdate? event with
    | none => simp [found] at known
    | some update =>
        simp only [found, decide_eq_true_eq] at known
        simp [found, known]
  · rw [Finset.mem_biUnion]
    rintro ⟨event, member, known⟩
    refine ⟨event, member, ?_⟩
    cases found : axisUpdate? event with
    | none => simp [found] at known
    | some update =>
        simp only [found] at known
        split at known
        · rename_i sameAxis
          simp only [Finset.mem_singleton] at known
          simp [found, sameAxis, known]
        · simp at known

theorem storedAxisIds_eq_axisIds {events : Finset Event}
    (known : CellAxesKnown events) (axis : Axis) :
    storedAxisIds events axis = axisIds events axis := by
  apply Finset.ext
  intro id
  constructor
  · intro storedMember
    unfold storedAxisIds at storedMember
    rw [Finset.mem_biUnion] at storedMember
    obtain ⟨event, member, stored⟩ := storedMember
    cases action : event.action with
    | axis update =>
        unfold axisIds
        rw [Finset.mem_biUnion]
        refine ⟨event, member, ?_⟩
        simp [axisUpdate?, action] at stored ⊢
        split at stored <;> simp_all
    | cell update =>
        have isCell : cellUpdate? event = some update := by
          simp [cellUpdate?, action]
        have axes := known event member update isCell
        cases axis with
        | row =>
            simp [action] at stored
            subst id
            exact axisKnown_iff_mem_axisIds.mp axes.1
        | column =>
            simp [action] at stored
            subst id
            exact axisKnown_iff_mem_axisIds.mp axes.2
    | range update => simp [action] at stored
    | purge marker => simp [action] at stored
  · intro axisMember
    unfold axisIds at axisMember
    rw [Finset.mem_biUnion] at axisMember
    obtain ⟨event, member, stored⟩ := axisMember
    unfold storedAxisIds
    rw [Finset.mem_biUnion]
    refine ⟨event, member, ?_⟩
    cases found : axisUpdate? event with
    | none => simp [found] at stored
    | some update =>
        have action : event.action = .axis update := by
          cases h : event.action <;> simp [axisUpdate?, h] at found
          simpa [h, found]
        simp only [found] at stored
        split at stored
        · rename_i sameAxis
          simp only [Finset.mem_singleton] at stored
          simp [action, sameAxis, stored]
        · simp at stored

theorem coveredAxisTimes_subset_raw {events : Finset Event}
    (witnessed : CoveredWitnessed events) (axis : Axis) (id : StableId) :
    AegisSheet.GC.coveredAxisTimes events axis id ⊆
      rawAxisKeepTimes events axis id := by
  intro timestamp member
  cases axis with
  | row =>
      unfold AegisSheet.GC.coveredAxisTimes at member
      rw [Finset.mem_biUnion] at member
      obtain ⟨entry, entryMember, selected⟩ := member
      change timestamp ∈
        (if (entry.2.1 == id) = true then {entry.1} else (∅ : Finset Timestamp)) at selected
      by_cases coordinate : entry.2.1 = id
      · simp [coordinate] at selected
        obtain ⟨event, eventMember, update, isCell, sameTime, sameCoordinate⟩ :=
          witnessed entry entryMember
        have cellAction : event.action = .cell update := by
          cases h : event.action <;> simp [cellUpdate?, h] at isCell
          simpa [h, isCell]
        unfold rawAxisKeepTimes
        rw [Finset.mem_image]
        refine ⟨event, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨eventMember, ?_⟩
          have updateCoordinate : update.row = id := by
            simpa [← sameCoordinate] using coordinate
          simp [keepsAxis, cellAction, updateCoordinate]
        · have timestampEq : timestamp = entry.1 := selected
          exact sameTime.trans timestampEq.symm
      · simp [coordinate] at selected
  | column =>
      unfold AegisSheet.GC.coveredAxisTimes at member
      rw [Finset.mem_biUnion] at member
      obtain ⟨entry, entryMember, selected⟩ := member
      change timestamp ∈
        (if (entry.2.2 == id) = true then {entry.1} else (∅ : Finset Timestamp)) at selected
      by_cases coordinate : entry.2.2 = id
      · simp [coordinate] at selected
        obtain ⟨event, eventMember, update, isCell, sameTime, sameCoordinate⟩ :=
          witnessed entry entryMember
        have cellAction : event.action = .cell update := by
          cases h : event.action <;> simp [cellUpdate?, h] at isCell
          simpa [h, isCell]
        unfold rawAxisKeepTimes
        rw [Finset.mem_image]
        refine ⟨event, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨eventMember, ?_⟩
          have updateCoordinate : update.column = id := by
            simpa [← sameCoordinate] using coordinate
          simp [keepsAxis, cellAction, updateCoordinate]
        · have timestampEq : timestamp = entry.1 := selected
          exact sameTime.trans timestampEq.symm
      · simp [coordinate] at selected

theorem axisKeepTimes_eq_raw {events : Finset Event}
    (witnessed : CoveredWitnessed events) (axis : Axis) (id : StableId) :
    axisKeepTimes events axis id = rawAxisKeepTimes events axis id := by
  rw [AegisSheet.GC.axisKeepTimes_eq]
  apply Finset.union_eq_left.mpr
  exact coveredAxisTimes_subset_raw witnessed axis id

theorem liveAxisTokens_eq_raw {events : Finset Event}
    (witnessed : CoveredWitnessed events) (axis : Axis) (id : StableId) :
    liveAxisTokens events axis id = rawLiveAxisTokens events axis id := by
  unfold liveAxisTokens rawLiveAxisTokens
  rw [axisKeepTimes_eq_raw witnessed]

theorem visibleIds_materialize {events : Finset Event}
    (known : CellAxesKnown events) (witnessed : CoveredWitnessed events)
    (axis : Axis) :
    visibleIds (storedAxisIds events axis) (rawLiveAxisTokens events axis) =
      liveAxisIds events axis := by
  rw [storedAxisIds_eq_axisIds known axis]
  have tokenFunctions : rawLiveAxisTokens events axis =
      liveAxisTokens events axis := by
    funext id
    exact (liveAxisTokens_eq_raw witnessed axis id).symm
  rw [tokenFunctions]
  apply Finset.ext
  intro id
  simp [visibleIds, liveAxisIds, axisLive, axisKnown_iff_mem_axisIds]

theorem mem_axisPositionVersions_iff {events : Finset Event} {axis : Axis}
    {id : StableId} {timestamp : Timestamp} {position : Position} :
    (timestamp, position) ∈ axisPositionVersions events axis id ↔
      ∃ event ∈ events, ∃ update,
        axisUpdate? event = some update ∧ update.axis = axis ∧
          update.id = id ∧ update.after = some position ∧
          event.1 = timestamp := by
  unfold axisPositionVersions
  simp only [Finset.mem_biUnion, Finset.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨event, ⟨member, candidate⟩, stored⟩
    cases found : axisUpdate? event with
    | none => simp [axisCandidate, found] at candidate
    | some update =>
        simp only [axisCandidate, found, decide_eq_true_eq] at candidate
        cases after : update.after with
        | none => simp [found, after, optionFinset] at stored
        | some value =>
            simp only [found, after, optionFinset, Finset.image_singleton,
              Finset.mem_singleton, Prod.mk.injEq] at stored
            obtain ⟨rfl, rfl⟩ := stored
            exact ⟨event, member, update, found, candidate.1,
              candidate.2.1, after, rfl⟩
  · rintro ⟨event, member, update, found, sameAxis, sameId, after, sameTime⟩
    refine ⟨event, ⟨member, ?_⟩, ?_⟩
    · simp [axisCandidate, found, sameAxis, sameId, after]
    · simp [found, after, optionFinset, sameTime]

theorem laterAxisCandidate_eq_true_iff {events : Finset Event}
    {axis : Axis} {id : StableId} {candidate : Event} :
    laterAxisCandidate events axis id candidate = true ↔
      ∃ later ∈ events,
        axisCandidate axis id later = true ∧ candidate.1 < later.1 := by
  unfold laterAxisCandidate
  rw [AegisSheet.GC.fold_or_eq_true_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem mem_axisPositions_iff {events : Finset Event} {axis : Axis}
    {id : StableId} {position : Position} :
    position ∈ axisPositions events axis id ↔
      ∃ event ∈ events, ∃ update,
        axisUpdate? event = some update ∧ update.axis = axis ∧
          update.id = id ∧ update.after = some position ∧
          laterAxisCandidate events axis id event = false := by
  unfold axisPositions
  simp only [Finset.mem_biUnion, Finset.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true]
  constructor
  · rintro ⟨event, ⟨member, candidate, latest⟩, stored⟩
    cases found : axisUpdate? event with
    | none => simp [axisCandidate, found] at candidate
    | some update =>
        simp only [axisCandidate, found, decide_eq_true_eq] at candidate
        cases after : update.after with
        | none => simp [found, after] at stored
        | some value =>
            simp only [found, after, Finset.mem_singleton] at stored
            subst value
            exact ⟨event, member, update, found, candidate.1,
              candidate.2.1, after, by simpa using latest⟩
  · rintro ⟨event, member, update, found, sameAxis, sameId, after, latest⟩
    refine ⟨event, ⟨member, ?_, by simpa using latest⟩, ?_⟩
    · simp [axisCandidate, found, sameAxis, sameId, after]
    · simp [found, after]

theorem latestPositions_axisPositionVersions (events : Finset Event)
    (axis : Axis) (id : StableId) :
    latestPositions (axisPositionVersions events axis id) =
      axisPositions events axis id := by
  apply Finset.ext
  intro position
  let versions := axisPositionVersions events axis id
  by_cases nonempty : versions.Nonempty
  · let maximum := (versions.image Prod.fst).max'
        (nonempty.image _)
    have maximumMember : maximum ∈ versions.image Prod.fst :=
      Finset.max'_mem _ _
    rw [mem_axisPositions_iff]
    change position ∈ latestPositions versions ↔ _
    unfold latestPositions maxNat?
    simp only [nonempty.image, dite_true]
    change position ∈
      (versions.filter fun version => decide (version.1 = maximum)).image Prod.snd ↔ _
    simp only [Finset.mem_image, Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨timestamp, value⟩, ⟨versionMember, sameTime⟩, sameValue⟩
      simp only at sameValue
      subst value
      rw [mem_axisPositionVersions_iff] at versionMember
      obtain ⟨event, eventMember, update, found, sameAxis, sameId, after,
        eventTime⟩ := versionMember
      refine ⟨event, eventMember, update, found, sameAxis, sameId, after, ?_⟩
      apply Bool.eq_false_iff.mpr
      intro laterExists
      rw [laterAxisCandidate_eq_true_iff] at laterExists
      obtain ⟨later, laterMember, laterCandidate, laterTime⟩ := laterExists
      have laterVersion : ∃ laterPosition,
          (later.1, laterPosition) ∈ versions := by
        cases laterFound : axisUpdate? later with
        | none => simp [axisCandidate, laterFound] at laterCandidate
        | some laterUpdate =>
            simp only [axisCandidate, laterFound, decide_eq_true_eq] at laterCandidate
            cases laterAfter : laterUpdate.after with
            | none => simp [laterAfter] at laterCandidate
            | some laterPosition =>
                refine ⟨laterPosition, ?_⟩
                rw [mem_axisPositionVersions_iff]
                exact ⟨later, laterMember, laterUpdate, laterFound,
                  laterCandidate.1, laterCandidate.2.1, laterAfter, rfl⟩
      obtain ⟨laterPosition, laterVersion⟩ := laterVersion
      have laterTimestampMember : later.1 ∈ versions.image Prod.fst :=
        Finset.mem_image.mpr ⟨(later.1, laterPosition), laterVersion, rfl⟩
      have bounded := Finset.le_max' _ _ laterTimestampMember
      have eventIsMaximum : event.1 = maximum := eventTime.trans sameTime
      exact (Nat.not_lt_of_ge (eventIsMaximum.symm ▸ bounded)) laterTime
    · rintro ⟨event, eventMember, update, found, sameAxis, sameId, after,
        latest⟩
      have versionMember : (event.1, position) ∈ versions := by
        rw [mem_axisPositionVersions_iff]
        exact ⟨event, eventMember, update, found, sameAxis, sameId, after, rfl⟩
      have timestampMember : event.1 ∈ versions.image Prod.fst :=
        Finset.mem_image.mpr ⟨(event.1, position), versionMember, rfl⟩
      have bounded : event.1 ≤ maximum := Finset.le_max' _ _ timestampMember
      have reachesMaximum : maximum ≤ event.1 := by
        by_contra notBounded
        have strictlyLater : event.1 < maximum := Nat.lt_of_not_ge notBounded
        obtain ⟨maximumVersion, maximumVersionMember, maximumTime⟩ :=
          Finset.mem_image.mp maximumMember
        obtain ⟨maximumTimestamp, maximumPosition⟩ := maximumVersion
        simp only at maximumTime
        rw [mem_axisPositionVersions_iff] at maximumVersionMember
        obtain ⟨later, laterMember, laterUpdate, laterFound, laterAxis,
          laterId, laterAfter, laterEventTime⟩ := maximumVersionMember
        have laterCandidate : axisCandidate axis id later = true := by
          simp [axisCandidate, laterFound, laterAxis, laterId, laterAfter]
        have laterIsMaximum : later.1 = maximum :=
          laterEventTime.trans maximumTime
        have : laterAxisCandidate events axis id event = true :=
          laterAxisCandidate_eq_true_iff.mpr ⟨later, laterMember,
            laterCandidate, by simpa [laterIsMaximum] using strictlyLater⟩
        simp [latest] at this
      have sameTime : event.1 = maximum := Nat.le_antisymm bounded reachesMaximum
      exact ⟨(event.1, position), ⟨versionMember, sameTime⟩, rfl⟩
  · have versionsEmpty : versions = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    change position ∈ latestPositions versions ↔
      position ∈ axisPositions events axis id
    rw [versionsEmpty]
    constructor
    · simp [latestPositions, maxNat?]
    · intro positionMember
      rw [mem_axisPositions_iff] at positionMember
      obtain ⟨event, eventMember, update, found, sameAxis, sameId, after, _⟩ :=
        positionMember
      have : (event.1, position) ∈ versions := by
        rw [mem_axisPositionVersions_iff]
        exact ⟨event, eventMember, update, found, sameAxis, sameId, after, rfl⟩
      simpa [versionsEmpty] using this

def purgeOverwritten (events : Finset Event) (row column : StableId)
    (timestamp : Timestamp) : Bool :=
  Finset.fold (· || ·) false (fun event =>
    match purge? event with
    | some marker => decide ((row, column) ∈ marker.coordinates ∧
        timestamp ≤ marker.cutoff)
    | none => false) events

theorem cellWriteOverwritten_eq_true_iff {events : Finset Event}
    {candidate : Event} :
    cellWriteOverwritten events candidate = true ↔
      ∃ later ∈ events, ∃ update, cellUpdate? later = some update ∧
        candidate.1 ∈ update.overwrites := by
  unfold cellWriteOverwritten
  rw [AegisSheet.GC.fold_or_eq_true_iff]
  constructor
  · rintro ⟨later, member, overwritten⟩
    cases found : cellUpdate? later with
    | none => simp [found] at overwritten
    | some update =>
        simp only [found, decide_eq_true_eq] at overwritten
        exact ⟨later, member, update, found, overwritten⟩
  · rintro ⟨later, member, update, found, overwritten⟩
    exact ⟨later, member, by simp [found, overwritten]⟩

theorem purgeOverwritten_eq_true_iff {events : Finset Event}
    {row column : StableId} {timestamp : Timestamp} :
    purgeOverwritten events row column timestamp = true ↔
      ∃ event ∈ events, ∃ marker, purge? event = some marker ∧
        (row, column) ∈ marker.coordinates ∧ timestamp ≤ marker.cutoff := by
  unfold purgeOverwritten
  rw [AegisSheet.GC.fold_or_eq_true_iff]
  constructor
  · rintro ⟨event, member, overwritten⟩
    cases found : purge? event with
    | none => simp [found] at overwritten
    | some marker =>
        simp only [found, decide_eq_true_eq] at overwritten
        exact ⟨event, member, marker, found, overwritten⟩
  · rintro ⟨event, member, marker, found, coordinate, cutoff⟩
    exact ⟨event, member, by simp [found, coordinate, cutoff]⟩

theorem cellOverwritten_split {events : Finset Event} {candidate : Event}
    {update : CellUpdate} (isCell : cellUpdate? candidate = some update) :
    cellOverwritten events candidate =
      (cellWriteOverwritten events candidate ||
        purgeOverwritten events update.row update.column candidate.1) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true, cellWriteOverwritten_eq_true_iff,
    purgeOverwritten_eq_true_iff]
  unfold cellOverwritten
  rw [AegisSheet.GC.fold_or_eq_true_iff]
  constructor
  · rintro ⟨later, member, overwritten⟩
    cases action : later.action with
    | axis axisUpdate => simp [action] at overwritten
    | range rangeUpdate => simp [action] at overwritten
    | cell laterUpdate =>
        left
        refine ⟨later, member, laterUpdate, ?_, ?_⟩
        · simp [cellUpdate?, action]
        · simpa [action] using overwritten
    | purge marker =>
        right
        refine ⟨later, member, marker, ?_, ?_⟩
        · simp [purge?, action]
        · simpa [action, isCell] using overwritten
  · rintro (written | purged)
    · obtain ⟨later, member, laterUpdate, found, overwritten⟩ := written
      refine ⟨later, member, ?_⟩
      have action : later.action = .cell laterUpdate := by
        cases h : later.action <;> simp [cellUpdate?, h] at found
        simpa [h, found]
      simp [action, overwritten]
    · obtain ⟨later, member, marker, found, coordinate, cutoff⟩ := purged
      refine ⟨later, member, ?_⟩
      have action : later.action = .purge marker :=
        AegisSheet.GC.action_eq_purge_of_purge_some found
      simp [action, isCell, coordinate, cutoff]

theorem mem_purgeMarkers_iff {events : Finset Event} {marker : Purge} :
    marker ∈ purgeMarkers events ↔
      ∃ event ∈ events, purge? event = some marker := by
  unfold purgeMarkers
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨event, member, stored⟩
    cases found : purge? event with
    | none => simp [found] at stored
    | some candidate =>
        simp only [found, Finset.mem_singleton] at stored
        subst candidate
        exact ⟨event, member, found⟩
  · rintro ⟨event, member, found⟩
    exact ⟨event, member, by simp [found]⟩

theorem versionPurged_materialize {events : Finset Event}
    (row column : StableId) (version : CellVersion) :
    versionPurged (materialize events) row column version =
      purgeOverwritten events row column version.1 := by
  apply Bool.eq_iff_iff.mpr
  rw [purgeOverwritten_eq_true_iff]
  unfold versionPurged
  rw [AegisSheet.GC.fold_or_eq_true_iff]
  simp only [materialize]
  constructor
  · rintro ⟨marker, member, purged⟩
    rw [mem_purgeMarkers_iff] at member
    obtain ⟨event, eventMember, found⟩ := member
    simp only [decide_eq_true_eq] at purged
    exact ⟨event, eventMember, marker, found, purged⟩
  · rintro ⟨event, eventMember, marker, found, coordinate, cutoff⟩
    refine ⟨marker, mem_purgeMarkers_iff.mpr ⟨event, eventMember, found⟩, ?_⟩
    simp [coordinate, cutoff]

theorem mem_rawCellValues_iff {events : Finset Event} {row column : StableId}
    {value : CellValue} :
    value ∈ rawCellValues events row column ↔
      ∃ event ∈ events, ∃ update,
        cellUpdate? event = some update ∧ update.row = row ∧
          update.column = column ∧ value ∈ update.after ∧
          cellOverwritten events event = false := by
  unfold rawCellValues
  simp only [Finset.mem_biUnion, Finset.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true]
  constructor
  · rintro ⟨event, ⟨member, matched, active⟩, stored⟩
    cases found : cellUpdate? event with
    | none => simp [cellMatches, found] at matched
    | some update =>
        simp only [cellMatches, found, decide_eq_true_eq] at matched
        simp only [found] at stored
        exact ⟨event, member, update, found, matched.1, matched.2,
          stored, by simpa using active⟩
  · rintro ⟨event, member, update, found, sameRow, sameColumn, stored, active⟩
    exact ⟨event, ⟨member, by
      simpa [cellMatches, found, sameRow, sameColumn] using active⟩,
      by simpa [found] using stored⟩

theorem materializedCellValues_eq_raw {events : Finset Event}
    (valid : AegisSheet.GC.StateValid events) (row column : StableId) :
    versionValues ((cellStored events row column).filter fun version =>
      !versionPurged (materialize events) row column version) =
      rawCellValues events row column := by
  apply Finset.ext
  intro value
  simp only [versionValues, Finset.mem_image, Finset.mem_filter,
    Bool.not_eq_true, mem_rawCellValues_iff]
  constructor
  · rintro ⟨⟨timestamp, storedValue⟩, ⟨stored, notPurged⟩, sameValue⟩
    simp only at sameValue
    subst storedValue
    rw [mem_cellStored_iff] at stored
    obtain ⟨event, member, update, found, sameRow, sameColumn, valueMember,
      sameTime, notWritten, _⟩ := stored
    refine ⟨event, member, update, found, sameRow, sameColumn, valueMember, ?_⟩
    rw [cellOverwritten_split found, Bool.or_eq_false_iff]
    refine ⟨notWritten, ?_⟩
    rw [sameRow, sameColumn, sameTime]
    rw [← versionPurged_materialize (events := events) row column (timestamp, value)]
    simpa using notPurged
  · rintro ⟨event, member, update, found, sameRow, sameColumn, valueMember,
      active⟩
    rw [cellOverwritten_split found, Bool.or_eq_false_iff] at active
    refine ⟨(event.1, value), ⟨?_, ?_⟩, rfl⟩
    · rw [mem_cellStored_iff]
      refine ⟨event, member, update, found, sameRow, sameColumn, valueMember,
        rfl, active.1, ?_⟩
      intro covered
      have overwritten := AegisSheet.GC.cellOverwritten_full_of_covered
        valid found covered
      rw [cellOverwritten_split found, active.1, active.2] at overwritten
      simp at overwritten
    · rw [versionPurged_materialize (events := events) row column (event.1, value)]
      simpa [sameRow, sameColumn] using active.2

theorem finsetNonemptyB_eq_true_iff {T : Type} [DecidableEq T]
    {values : Finset T} :
    finsetNonemptyB values = true ↔ values.Nonempty := by
  unfold finsetNonemptyB
  rw [AegisSheet.GC.fold_or_eq_true_iff]
  constructor
  · rintro ⟨value, member, _⟩
    exact ⟨value, member⟩
  · rintro ⟨value, member⟩
    exact ⟨value, member, rfl⟩

theorem rawLiveAxisTokens_nonempty_known {events : Finset Event}
    (known : CellAxesKnown events) (axis : Axis) (id : StableId)
    (nonempty : finsetNonemptyB (rawLiveAxisTokens events axis id) = true) :
    axisKnown events axis id = true := by
  rw [finsetNonemptyB_eq_true_iff] at nonempty
  obtain ⟨timestamp, live⟩ := nonempty
  unfold rawLiveAxisTokens at live
  have keepTime : timestamp ∈ rawAxisKeepTimes events axis id :=
    (Finset.mem_filter.mp live).1
  unfold rawAxisKeepTimes at keepTime
  obtain ⟨event, filtered, _⟩ := Finset.mem_image.mp keepTime
  obtain ⟨member, keeps⟩ := Finset.mem_filter.mp filtered
  rw [axisKnown_iff_mem_axisIds]
  cases action : event.action with
  | axis update =>
      unfold axisIds
      rw [Finset.mem_biUnion]
      refine ⟨event, member, ?_⟩
      simp [keepsAxis, action] at keeps
      simp [axisUpdate?, action, keeps]
  | cell update =>
      have isCell : cellUpdate? event = some update := by
        simp [cellUpdate?, action]
      have axes := known event member update isCell
      cases axis with
      | row =>
          simp [keepsAxis, action] at keeps
          subst id
          exact axisKnown_iff_mem_axisIds.mp axes.1
      | column =>
          simp [keepsAxis, action] at keeps
          subst id
          exact axisKnown_iff_mem_axisIds.mp axes.2
  | range update => simp [keepsAxis, action] at keeps
  | purge marker => simp [keepsAxis, action] at keeps

theorem rawLiveNonempty_eq_axisLive {events : Finset Event}
    (known : CellAxesKnown events) (witnessed : CoveredWitnessed events)
    (axis : Axis) (id : StableId) :
    finsetNonemptyB (rawLiveAxisTokens events axis id) =
      axisLive events axis id := by
  apply Bool.eq_iff_iff.mpr
  unfold axisLive
  rw [Bool.and_eq_true]
  constructor
  · intro nonempty
    refine ⟨rawLiveAxisTokens_nonempty_known known axis id nonempty, ?_⟩
    rw [liveAxisTokens_eq_raw witnessed]
    exact nonempty
  · rintro ⟨_, nonempty⟩
    rw [liveAxisTokens_eq_raw witnessed] at nonempty
    exact nonempty

theorem observationInvariant_of_facts {events : Finset Event}
    (valid : AegisSheet.GC.StateValid events)
    (known : CellAxesKnown events) (witnessed : CoveredWitnessed events) :
    ObservationInvariant events := by
  apply View.ext
  · exact visibleIds_materialize known witnessed .row
  · exact visibleIds_materialize known witnessed .column
  · funext id
    exact latestPositions_axisPositionVersions events .row id
  · funext id
    exact latestPositions_axisPositionVersions events .column id
  · funext row column
    simp only [view, materialize]
    change (if finsetNonemptyB (rawLiveAxisTokens events .row row) &&
          finsetNonemptyB (rawLiveAxisTokens events .column column) then
        versionValues ((cellStored events row column).filter fun version =>
          !versionPurged (materialize events) row column version)
      else ∅) = cellValues events row column
    unfold cellValues
    rw [rawLiveNonempty_eq_axisLive known witnessed,
      rawLiveNonempty_eq_axisLive known witnessed]
    split
    · exact materializedCellValues_eq_raw valid row column
    · rfl
  · funext id
    exact rangeStored_values events id

theorem axisKnown_insert_of_old {events : Finset Event} {e : Event}
    {axis : Axis} {id : StableId}
    (known : axisKnown events axis id = true) :
    axisKnown (insert e events) axis id = true := by
  rw [axisKnown_iff_mem_axisIds] at known ⊢
  rw [axisIds_insert]
  exact Finset.mem_union_right _ known

theorem inverseFor_cell_coordinates {prior : Event} {update : CellUpdate}
    (inverse : inverseFor prior = .cell update) :
    ∃ priorUpdate, cellUpdate? prior = some priorUpdate ∧
      priorUpdate.row = update.row ∧ priorUpdate.column = update.column := by
  cases action : prior.action with
  | axis axisUpdate => simp [inverseFor, invertAction, action] at inverse
  | range rangeUpdate => simp [inverseFor, invertAction, action] at inverse
  | purge marker => simp [inverseFor, invertAction, action] at inverse
  | cell priorUpdate =>
      refine ⟨priorUpdate, by simp [cellUpdate?, action], ?_⟩
      simp [inverseFor, invertAction, action] at inverse
      subst update
      simp

theorem action_eq_cell_of_cellUpdate_some {event : Event} {update : CellUpdate}
    (found : cellUpdate? event = some update) :
    event.action = .cell update := by
  cases action : event.action <;> simp [cellUpdate?, action] at found
  simpa [action, found]

theorem validUndo_cell_witness {events : Finset Event} {issuer : Replica}
    {target : Timestamp} {update : CellUpdate}
    (valid : validUndo events issuer target (.cell update) = true) :
    ∃ prior ∈ events, ∃ priorUpdate,
      cellUpdate? prior = some priorUpdate ∧ priorUpdate.row = update.row ∧
        priorUpdate.column = update.column := by
  unfold validUndo at valid
  rw [AegisSheet.GC.fold_or_eq_true_iff] at valid
  obtain ⟨prior, member, accepted⟩ := valid
  cases action : prior.action with
  | purge marker => simp [action] at accepted
  | axis axisUpdate => simp [inverseFor, invertAction, action] at accepted
  | range rangeUpdate => simp [inverseFor, invertAction, action] at accepted
  | cell priorUpdate =>
      simp only [action, decide_eq_true_eq] at accepted
      have inverse : inverseFor prior = .cell update := accepted.2.2.symm
      obtain ⟨source, isCell, sameRow, sameColumn⟩ :=
        inverseFor_cell_coordinates inverse
      exact ⟨prior, member, source, isCell, sameRow, sameColumn⟩

theorem cellAxesKnown_insert {events : Finset Event} {e : Event}
    (old : CellAxesKnown events) (guard : applicable e events) :
    CellAxesKnown (insert e events) := by
  intro event member update isCell
  rcases Finset.mem_insert.mp member with rfl | oldMember
  · rcases guard with ⟨guard, _⟩
    unfold applicableB at guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    have commandGuard := guard.2
    cases command : event.2.2.command with
    | direct action =>
        have actionEq : action = .cell update := by
          simpa [Event.action, Command.effect, command] using
            action_eq_cell_of_cellUpdate_some isCell
        subst action
        simp only [command, directApplicable] at commandGuard
        simp only [Bool.and_eq_true] at commandGuard
        have rowLive : axisLive events .row update.row = true :=
          commandGuard.1.1.1
        have columnLive : axisLive events .column update.column = true :=
          commandGuard.1.1.2
        unfold axisLive at rowLive columnLive
        simp only [axisLive, Bool.and_eq_true] at rowLive columnLive
        exact ⟨axisKnown_insert_of_old rowLive.1,
          axisKnown_insert_of_old columnLive.1⟩
    | undo target inverse =>
        have inverseEq : inverse = .cell update := by
          simpa [Event.action, Command.effect, command] using
            action_eq_cell_of_cellUpdate_some isCell
        subst inverse
        simp only [command, Bool.and_eq_true, decide_eq_true_eq] at commandGuard
        obtain ⟨prior, priorMember, priorUpdate, priorCell, sameRow, sameColumn⟩ :=
          validUndo_cell_witness commandGuard.2
        have priorKnown := old prior priorMember priorUpdate priorCell
        exact ⟨axisKnown_insert_of_old (sameRow ▸ priorKnown.1),
          axisKnown_insert_of_old (sameColumn ▸ priorKnown.2)⟩
  · have oldKnown := old event oldMember update isCell
    exact ⟨axisKnown_insert_of_old oldKnown.1,
      axisKnown_insert_of_old oldKnown.2⟩

theorem validUndo_purge_false (events : Finset Event) (issuer : Replica)
    (target : Timestamp) (marker : Purge) :
    validUndo events issuer target (.purge marker) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  unfold validUndo at accepted
  rw [AegisSheet.GC.fold_or_eq_true_iff] at accepted
  obtain ⟨prior, _, validPrior⟩ := accepted
  cases action : prior.action <;>
    simp [inverseFor, invertAction, action] at validPrior

theorem purgeApplicable_covered_witness {events : Finset Event}
    {issuer : Replica} {marker : Purge}
    (guard : purgeApplicable events issuer marker = true) :
    ∀ entry ∈ marker.covered,
      ∃ event ∈ events, ∃ update,
        cellUpdate? event = some update ∧ event.1 = entry.1 ∧
          (update.row, update.column) = entry.2 := by
  unfold purgeApplicable at guard
  simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
  have coveredGuard := guard.1.2
  rw [AegisSheet.GC.fold_and_eq_true_iff] at coveredGuard
  intro entry member
  have entryGuard := coveredGuard entry member
  rw [AegisSheet.GC.fold_or_eq_true_iff] at entryGuard
  obtain ⟨event, eventMember, accepted⟩ := entryGuard
  cases found : cellUpdate? event with
  | none => simp [found] at accepted
  | some update =>
      simp only [found, decide_eq_true_eq] at accepted
      exact ⟨event, eventMember, update, found, accepted.1, accepted.2.1⟩

theorem coveredWitnessed_insert {events : Finset Event} {e : Event}
    (old : CoveredWitnessed events) (guard : applicable e events) :
    CoveredWitnessed (insert e events) := by
  intro entry member
  rw [AegisSheet.GC.markerCoveredEntries_insert] at member
  rcases Finset.mem_union.mp member with newMember | oldMember
  · cases found : purge? e with
    | none => simp [found] at newMember
    | some marker =>
        simp only [found] at newMember
        rcases guard with ⟨guard, _⟩
        unfold applicableB at guard
        simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
        have commandGuard := guard.2
        cases command : e.2.2.command with
        | direct action =>
            have actionEq : action = .purge marker := by
              have effect : e.action = .purge marker :=
                AegisSheet.GC.action_eq_purge_of_purge_some found
              simpa [Event.action, Command.effect, command] using effect
            subst action
            simp only [command, directApplicable] at commandGuard
            obtain ⟨event, eventMember, update, isCell, sameTime,
              sameCoordinate⟩ :=
              purgeApplicable_covered_witness commandGuard entry newMember
            exact ⟨event, Finset.mem_insert_of_mem eventMember, update,
              isCell, sameTime, sameCoordinate⟩
        | undo target inverse =>
            have inverseEq : inverse = .purge marker := by
              have effect : e.action = .purge marker :=
                AegisSheet.GC.action_eq_purge_of_purge_some found
              simpa [Event.action, Command.effect, command] using effect
            subst inverse
            simp only [command, Bool.and_eq_true, decide_eq_true_eq] at commandGuard
            rw [validUndo_purge_false] at commandGuard
            simp at commandGuard
  · obtain ⟨event, eventMember, update, isCell, sameTime, sameCoordinate⟩ :=
      old entry oldMember
    exact ⟨event, Finset.mem_insert_of_mem eventMember, update,
      isCell, sameTime, sameCoordinate⟩

theorem linearMintHistory_provenance {ops : List Event}
    (history : LinearMintHistory D AegisSheet.applicable ops) :
    CellAxesKnown ops.toFinset ∧ CoveredWitnessed ops.toFinset := by
  induction ops using List.reverseRecOn with
  | nil =>
      constructor
      · simp [CellAxesKnown]
      · simp [CoveredWitnessed, AegisSheet.GC.markerCoveredEntries]
  | append_singleton initial e ih =>
      have initialHistory := linearMintHistory_prefix history
        (initial := initial) (suffix := [e]) rfl
      obtain ⟨known, witnessed⟩ := ih initialHistory
      have guard : applicable e initial.toFinset := by
        have guarded := history.guarded initial e [] (by simp)
        simpa [AegisSheet.applySeq_eq_toFinset] using guarded
      constructor
      · simpa using cellAxesKnown_insert known guard
      · simpa using coveredWitnessed_insert witnessed guard

theorem guarded_history_observes {ops : List Event}
    (history : LinearMintHistory D AegisSheet.applicable ops) :
    view (run ops) = AegisSheet.view ops.toFinset := by
  have facts := linearMintHistory_facts history
  obtain ⟨known, witnessed⟩ := linearMintHistory_provenance history
  rw [facts.materialized]
  exact observationInvariant_of_facts facts.stateValid known witnessed

/-! ## Sequential refinement

The replicated carrier forgets list order, while the incremental reference
machine consumes a list. A valid minted history has strictly increasing
Lamport timestamps. Therefore its event set has exactly one chronological
enumeration, and that enumeration determines the complete incremental state.
-/

def Chronological (events : List Event) : Prop :=
  ∀ pre e post, events = pre ++ e :: post →
    ∀ old ∈ pre, old.1 < e.1

def timestampLT (a b : Event) : Prop := a.1 < b.1

instance : DecidableRel timestampLT := fun a b =>
  inferInstanceAs (Decidable (a.1 < b.1))

instance : Std.Irrefl timestampLT :=
  ⟨fun event h => Nat.lt_irrefl event.1 h⟩

instance : Std.Antisymm timestampLT :=
  ⟨fun _ _ hab hba => False.elim (Nat.not_lt_of_ge (Nat.le_of_lt hba) hab)⟩

theorem chronological_pairwise {events : List Event}
    (h : Chronological events) : events.Pairwise timestampLT := by
  induction events with
  | nil => exact .nil
  | cons first rest ih =>
      rw [List.pairwise_cons]
      constructor
      · intro e he
        obtain ⟨pre, post, hrest⟩ := List.mem_iff_append.mp he
        exact h (first :: pre) e post (by simp [hrest]) first (by simp)
      · apply ih
        intro pre e post heq old hold
        exact h (first :: pre) e post (by simp [heq]) old (by simp [hold])

theorem chronological_of_pairwise {events : List Event}
    (h : events.Pairwise timestampLT) : Chronological events := by
  intro pre e post heq old hold
  subst events
  have cross := (List.pairwise_append.mp h).2.2
  exact cross old hold e (by simp)

theorem chronological_eq_of_toFinset_eq {left right : List Event}
    (leftChronological : Chronological left)
    (rightChronological : Chronological right)
    (sameEvents : left.toFinset = right.toFinset) : left = right := by
  apply (chronological_pairwise leftChronological).eq_of_mem_iff
    (chronological_pairwise rightChronological)
  intro event
  have hmem : event ∈ left.toFinset ↔ event ∈ right.toFinset :=
    Iff.of_eq (congrArg (fun events : Finset Event => event ∈ events)
      sameEvents)
  simpa only [List.mem_toFinset] using hmem

/-- Exact relation between the replicated event set and the in-place machine.
It is deliberately universal: every valid chronological enumeration of the
set must produce this same complete state. -/
def inplaceStateRel (events : D.State) (state : State) : Prop :=
  ∀ ops, Chronological ops → ops.toFinset = events → run ops = state

def GuardedChronological (ops : List Event) : Prop :=
  Chronological ops ∧
    ∀ pre e post, ops = pre ++ e :: post →
      applicable e pre.toFinset

/-- Merged-history legality checks each event at its encoded causal origin,
not against unrelated concurrent events that happen to precede it in the
chosen serialization. `applicable` checks that the origin's event times are
exactly `e.seen`; chronology makes every member of `origin` precede `e`. -/
def CausalOriginLegal (ops : List Event) : Prop :=
  Chronological ops ∧
    ∀ pre e post, ops = pre ++ e :: post →
      ∃ origin : Finset Event,
        origin ⊆ pre.toFinset ∧ applicable e origin

theorem causalOriginLegal_prefix {ops initial suffix : List Event}
    (legal : CausalOriginLegal ops) (split : ops = initial ++ suffix) :
    CausalOriginLegal initial := by
  constructor
  · intro pre e post initialSplit old oldMember
    apply legal.1 pre e (post ++ suffix)
    · calc
        ops = initial ++ suffix := split
        _ = (pre ++ e :: post) ++ suffix := by rw [initialSplit]
        _ = pre ++ e :: (post ++ suffix) := by simp [List.append_assoc]
    · exact oldMember
  · intro pre e post initialSplit
    apply legal.2 pre e (post ++ suffix)
    calc
      ops = initial ++ suffix := split
      _ = (pre ++ e :: post) ++ suffix := by rw [initialSplit]
      _ = pre ++ e :: (post ++ suffix) := by simp [List.append_assoc]

theorem seenValid_insert_of_origin {events origin : Finset Event} {e : Event}
    (valid : SeenValid events) (subset : origin ⊆ events)
    (guard : applicable e origin) : SeenValid (insert e events) := by
  intro candidate member
  rcases Finset.mem_insert.mp member with rfl | old
  · rw [applicable_seen guard]
    exact eventTimes_mono (Finset.Subset.trans subset
      (Finset.subset_insert candidate events))
  · exact fun timestamp timestampMember =>
      eventTimes_mono (Finset.subset_insert e events)
        (valid candidate old timestampMember)

theorem fresh_of_clock_and_coveredWitnessed {events : Finset Event}
    {e : Event} (clock : ∀ old ∈ events, old.1 < e.1)
    (witnessed : CoveredWitnessed events) : e.1 ∉ eventTimes events := by
  rw [AegisSheet.GC.eventTimes_eq]
  simp only [Finset.mem_union]
  rintro (direct | covered)
  · obtain ⟨old, oldMember, same⟩ := Finset.mem_image.mp direct
    exact Nat.ne_of_lt (clock old oldMember) same
  · unfold AegisSheet.GC.markerCoveredTimes at covered
    obtain ⟨⟨timestamp, coordinate⟩, entryMember, same⟩ :=
      Finset.mem_image.mp covered
    simp only at same
    obtain ⟨old, oldMember, update, _, oldTime, _⟩ :=
      witnessed (timestamp, coordinate) entryMember
    have lt := clock old oldMember
    exact (Nat.ne_of_lt lt) (oldTime.trans same)

theorem cellAxesKnown_insert_of_origin {events origin : Finset Event}
    {e : Event} (old : CellAxesKnown events) (subset : origin ⊆ events)
    (guard : applicable e origin) : CellAxesKnown (insert e events) := by
  intro event member update isCell
  rcases Finset.mem_insert.mp member with rfl | oldMember
  · rcases guard with ⟨guard, _⟩
    unfold applicableB at guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    have commandGuard := guard.2
    cases command : event.2.2.command with
    | direct action =>
        have actionEq : action = .cell update := by
          simpa [Event.action, Command.effect, command] using
            action_eq_cell_of_cellUpdate_some isCell
        subst action
        simp only [command, directApplicable] at commandGuard
        simp only [Bool.and_eq_true] at commandGuard
        have rowLive : axisLive origin .row update.row = true :=
          commandGuard.1.1.1
        have columnLive : axisLive origin .column update.column = true :=
          commandGuard.1.1.2
        unfold axisLive at rowLive columnLive
        simp only [axisLive, Bool.and_eq_true] at rowLive columnLive
        have rowKnown : axisKnown events .row update.row = true :=
          AegisSheet.GC.fold_or_true_mono subset _ rowLive.1
        have columnKnown : axisKnown events .column update.column = true :=
          AegisSheet.GC.fold_or_true_mono subset _ columnLive.1
        exact ⟨axisKnown_insert_of_old rowKnown,
          axisKnown_insert_of_old columnKnown⟩
    | undo target inverse =>
        have inverseEq : inverse = .cell update := by
          simpa [Event.action, Command.effect, command] using
            action_eq_cell_of_cellUpdate_some isCell
        subst inverse
        simp only [command, Bool.and_eq_true, decide_eq_true_eq] at commandGuard
        obtain ⟨prior, priorMember, priorUpdate, priorCell, sameRow, sameColumn⟩ :=
          validUndo_cell_witness commandGuard.2
        have priorKnown := old prior (subset priorMember) priorUpdate priorCell
        exact ⟨axisKnown_insert_of_old (sameRow ▸ priorKnown.1),
          axisKnown_insert_of_old (sameColumn ▸ priorKnown.2)⟩
  · have oldKnown := old event oldMember update isCell
    exact ⟨axisKnown_insert_of_old oldKnown.1,
      axisKnown_insert_of_old oldKnown.2⟩

theorem coveredWitnessed_insert_of_origin {events origin : Finset Event}
    {e : Event} (old : CoveredWitnessed events) (subset : origin ⊆ events)
    (guard : applicable e origin) : CoveredWitnessed (insert e events) := by
  intro entry member
  rw [AegisSheet.GC.markerCoveredEntries_insert] at member
  rcases Finset.mem_union.mp member with newMember | oldMember
  · cases found : purge? e with
    | none => simp [found] at newMember
    | some marker =>
        simp only [found] at newMember
        rcases guard with ⟨guard, _⟩
        unfold applicableB at guard
        simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
        have commandGuard := guard.2
        cases command : e.2.2.command with
        | direct action =>
            have actionEq : action = .purge marker := by
              have effect : e.action = .purge marker :=
                AegisSheet.GC.action_eq_purge_of_purge_some found
              simpa [Event.action, Command.effect, command] using effect
            subst action
            simp only [command, directApplicable] at commandGuard
            obtain ⟨event, eventMember, update, isCell, sameTime,
              sameCoordinate⟩ :=
              purgeApplicable_covered_witness commandGuard entry newMember
            exact ⟨event, Finset.mem_insert_of_mem (subset eventMember), update,
              isCell, sameTime, sameCoordinate⟩
        | undo target inverse =>
            have inverseEq : inverse = .purge marker := by
              have effect : e.action = .purge marker :=
                AegisSheet.GC.action_eq_purge_of_purge_some found
              simpa [Event.action, Command.effect, command] using effect
            subst inverse
            simp only [command, Bool.and_eq_true, decide_eq_true_eq] at commandGuard
            rw [validUndo_purge_false] at commandGuard
            simp at commandGuard
  · obtain ⟨event, eventMember, update, isCell, sameTime, sameCoordinate⟩ :=
      old entry oldMember
    exact ⟨event, Finset.mem_insert_of_mem eventMember, update,
      isCell, sameTime, sameCoordinate⟩

structure CausalHistoryFacts (ops : List Event) extends HistoryFacts ops where
  cellAxesKnown : CellAxesKnown ops.toFinset
  coveredWitnessed : CoveredWitnessed ops.toFinset

theorem causalOriginHistory_facts {ops : List Event}
    (legal : CausalOriginLegal ops) : CausalHistoryFacts ops := by
  induction ops using List.reverseRecOn with
  | nil =>
      apply CausalHistoryFacts.mk
      · refine ⟨?_, AegisSheet.GC.timestampUnique_empty, ?_, rfl⟩
        · simp [AegisSheet.GC.StateValid]
        · simp [SeenValid]
      · simp [CellAxesKnown]
      · simp [CoveredWitnessed, AegisSheet.GC.markerCoveredEntries]
  | append_singleton initial e ih =>
      have initialLegal := causalOriginLegal_prefix legal
        (initial := initial) (suffix := [e]) rfl
      have initialFacts := ih initialLegal
      obtain ⟨origin, originSubset, guard⟩ :=
        legal.2 initial e [] (by simp)
      have clock : ∀ old ∈ initial.toFinset, old.1 < e.1 := by
        intro old oldMember
        exact legal.1 initial e [] (by simp) old (by simpa using oldMember)
      have fresh := fresh_of_clock_and_coveredWitnessed clock
        initialFacts.coveredWitnessed
      have metadata : metadataValidB initial.toFinset e = true :=
        AegisSheet.GC.metadataValid_mono originSubset
          (AegisSheet.GC.applicable_metadataValid guard)
      apply CausalHistoryFacts.mk
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simpa using AegisSheet.GC.stateValid_insert
            initialFacts.stateValid metadata
        · simpa using AegisSheet.GC.timestampUnique_insert
            initialFacts.timestampUnique fresh
        · simpa using seenValid_insert_of_origin initialFacts.seenValid
            originSubset guard
        · change spec.run (initial ++ [e]) = materialize (initial ++ [e]).toFinset
          rw [SequentialMachine.run_append_single]
          change step (run initial) e = materialize (initial ++ [e]).toFinset
          rw [initialFacts.materialized]
          simpa using materialize_insert_of_facts initialFacts.stateValid
            initialFacts.timestampUnique initialFacts.seenValid fresh metadata clock
      · simpa using cellAxesKnown_insert_of_origin
          initialFacts.cellAxesKnown originSubset guard
      · simpa using coveredWitnessed_insert_of_origin
          initialFacts.coveredWitnessed originSubset guard

theorem causalOrigin_history_materializes {ops : List Event}
    (legal : CausalOriginLegal ops) :
    run ops = materialize ops.toFinset :=
  (causalOriginHistory_facts legal).materialized

theorem causalOrigin_history_observes {ops : List Event}
    (legal : CausalOriginLegal ops) :
    view (run ops) = AegisSheet.view ops.toFinset := by
  have facts := causalOriginHistory_facts legal
  rw [facts.materialized]
  exact observationInvariant_of_facts facts.stateValid facts.cellAxesKnown
    facts.coveredWitnessed

def chronologicalLEB (a b : Event) : Bool := decide (a.1 ≤ b.1)

/-- Deterministic timestamp enumeration used only to select the public
sequential witness. Reachable version sets have unique event timestamps. -/
def canonical (ops : List Event) : List Event :=
  ops.mergeSort chronologicalLEB

theorem canonical_perm (ops : List Event) : (canonical ops).Perm ops :=
  List.mergeSort_perm ops chronologicalLEB

theorem canonical_toFinset (ops : List Event) :
    (canonical ops).toFinset = ops.toFinset := by
  apply Finset.ext
  intro event
  simpa only [List.mem_toFinset] using (canonical_perm ops).mem_iff

theorem canonical_pairwise_le (ops : List Event) :
    (canonical ops).Pairwise (fun a b => a.1 ≤ b.1) := by
  have sorted := List.pairwise_mergeSort
    (le := chronologicalLEB)
    (fun a b c hab hbc => by
      simp only [chronologicalLEB, decide_eq_true_eq] at hab hbc ⊢
      exact Nat.le_trans hab hbc)
    (fun a b => by
      simp only [chronologicalLEB, Bool.or_eq_true, decide_eq_true_eq]
      exact Nat.le_total a.1 b.1)
    ops
  simpa only [canonical, chronologicalLEB, decide_eq_true_eq] using sorted

theorem canonical_nodup {ops : List Event} (nodup : ops.Nodup) :
    (canonical ops).Nodup :=
  nodup.perm (canonical_perm ops).symm

theorem canonical_chronological {ops : List Event}
    (nodup : ops.Nodup)
    (unique : AegisSheet.GC.TimestampUnique ops.toFinset) :
    Chronological (canonical ops) := by
  intro pre e post split old oldMember
  have sorted := canonical_pairwise_le ops
  rw [split] at sorted
  have oldLE : old.1 ≤ e.1 :=
    (List.pairwise_append.mp sorted).2.2 old oldMember e (by simp)
  have canonicalNodup := canonical_nodup nodup
  rw [split] at canonicalNodup
  have oldNe : old ≠ e :=
    (List.nodup_append.mp canonicalNodup).2.2 old oldMember e (by simp)
  have timeNe : old.1 ≠ e.1 := by
    intro same
    apply oldNe
    apply unique
    · rw [← canonical_toFinset ops, split]
      simp [oldMember]
    · rw [← canonical_toFinset ops, split]
      simp
    · exact same
  exact lt_of_le_of_ne oldLE timeNe

theorem mem_prefix_of_chronological {ops pre post : List Event}
    {e old : Event} (chronological : Chronological ops)
    (split : ops = pre ++ e :: post) (member : old ∈ ops)
    (before : old.1 < e.1) : old ∈ pre := by
  rw [split] at member
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with inPre | same | inPost
  · exact inPre
  · subst old
    exact False.elim (Nat.lt_irrefl _ before)
  · obtain ⟨beforeOld, afterOld, postSplit⟩ := List.mem_iff_append.mp inPost
    have after : e.1 < old.1 := by
      apply chronological (pre ++ e :: beforeOld) old afterOld
      · calc
          ops = pre ++ e :: post := split
          _ = pre ++ e :: (beforeOld ++ old :: afterOld) := by rw [postSplit]
          _ = (pre ++ e :: beforeOld) ++ old :: afterOld := by simp
      · simp
    exact False.elim (Nat.lt_asymm before after)

theorem canonical_causalOriginLegal {C : Configuration D}
    (exec : CertifiedExecution D AegisSheet.generation C)
    {v : Version} {s : D.State} {E : Set Event} {ops : List Event}
    (hver : C.ver v = some (s, E)) (perm : listPermOf ops E) :
    CausalOriginLegal (canonical ops) := by
  have good : GoodConfig3 C := exec.goodConfig (fun _ _ => AegisSheet.join _)
  have subsetEvents := good.ver_events_sub v s E hver
  have causalClosed := good.ver_causal v s E hver
  have unique : AegisSheet.GC.TimestampUnique ops.toFinset := by
    intro a ha b hb same
    apply C.core.ts_unique
    · apply subsetEvents a
      apply (perm.2 a).mp
      simpa using ha
    · apply subsetEvents b
      apply (perm.2 b).mp
      simpa using hb
    · exact same
  have chronological := canonical_chronological perm.1 unique
  refine ⟨chronological, ?_⟩
  intro pre e post split
  have eCanonical : e ∈ canonical ops := by rw [split]; simp
  have eOps : e ∈ ops := (canonical_perm ops).mem_iff.mp eCanonical
  have eE : e ∈ E := (perm.2 e).mp eOps
  obtain ⟨originOps, originPerm, _, issued⟩ :=
    exec.mintHonest e (subsetEvents e eE)
  have originGuard : applicable e originOps.toFinset := by
    simpa [AegisSheet.applySeq_eq_toFinset] using issued
  refine ⟨originOps.toFinset, ?_, originGuard⟩
  intro old oldMember
  have oldOrigin : old ∈ originOps := by simpa using oldMember
  have oldPred := (originPerm.2 old).mp oldOrigin
  have oldE : old ∈ E := causalClosed old e oldPred.2 eE
  have oldOps : old ∈ ops := (perm.2 old).mpr oldE
  have oldCanonical : old ∈ canonical ops :=
    (canonical_perm ops).mem_iff.mpr oldOps
  have oldTime : old.1 < e.1 :=
    originGuard.2.lt old.1 (eventTime_mem oldMember)
  have oldInPrefix : old ∈ pre :=
    mem_prefix_of_chronological (ops := canonical ops) chronological split
      oldCanonical oldTime
  simpa using oldInPrefix

def materializedStateRel (events : D.State) (state : State) : Prop :=
  inplaceStateRel events state ∧ state = materialize events ∧
    view state = AegisSheet.view events

/-- Client-facing sequential spreadsheet semantics. Legality records the
causal origin against which each operation was issued; the origin need only
be a subset of the merged serialization prefix. -/
noncomputable def clientSpec : SequentialSpec D where
  toSequentialMachine := spec
  Legal := CausalOriginLegal
  query := fun state _ => view state

theorem inplaceStateRel_empty : inplaceStateRel D.init empty := by
  intro ops chronological eventsEmpty
  have : ops = [] := by
    apply chronological_eq_of_toFinset_eq chronological (by simp [Chronological])
    simpa [D] using eventsEmpty
  subst ops
  rfl

theorem materializedStateRel_empty : materializedStateRel D.init empty := by
  refine ⟨inplaceStateRel_empty, rfl, rfl⟩

theorem inplaceSequentialSound (ops : List Event) (h : Chronological ops) :
    inplaceStateRel (applySeq D.toCRDTSig D.init ops) (run ops) := by
  intro other otherChronological sameEvents
  rw [AegisSheet.applySeq_eq_toFinset] at sameEvents
  rw [chronological_eq_of_toFinset_eq otherChronological h sameEvents]

theorem causalOriginSequentialSound (ops : List Event)
    (legal : CausalOriginLegal ops) :
    materializedStateRel (applySeq D.toCRDTSig D.init ops)
      (clientSpec.run ops) := by
  change materializedStateRel (applySeq D.toCRDTSig D.init ops) (run ops)
  refine ⟨inplaceSequentialSound ops legal.1, ?_, ?_⟩
  · rw [AegisSheet.applySeq_eq_toFinset]
    exact causalOrigin_history_materializes legal
  · rw [AegisSheet.applySeq_eq_toFinset]
    exact causalOrigin_history_observes legal

theorem guardedChronological_to_linearMintHistory {ops : List Event}
    (honest : GuardedChronological ops) :
    LinearMintHistory D applicable ops := by
  constructor
  · intro pre e post split
    simpa [AegisSheet.applySeq_eq_toFinset] using honest.2 pre e post split
  · exact honest.1

theorem materializedSequentialSound (ops : List Event)
    (honest : GuardedChronological ops) :
    materializedStateRel (applySeq D.toCRDTSig D.init ops) (run ops) := by
  have history := guardedChronological_to_linearMintHistory honest
  refine ⟨inplaceSequentialSound ops honest.1, ?_, ?_⟩
  · rw [AegisSheet.applySeq_eq_toFinset]
    exact (linearMintHistory_facts history).materialized
  · rw [AegisSheet.applySeq_eq_toFinset]
    exact guarded_history_observes history

noncomputable def inplaceSequential : SequentialRefinement D spec where
  Honest := GuardedChronological
  Rel := materializedStateRel
  init := materializedStateRel_empty
  sound := materializedSequentialSound

noncomputable def inplaceReplayVerified : ReplayVerifiedMRDT D where
  issuance := AegisSheet.generation
  convergence := AegisSheet.convergence
  Machine := spec
  sequential := inplaceSequential
  sequential_of_mint := fun _ h => ⟨h.clocked, fun pre e post split => by
    simpa [AegisSheet.applySeq_eq_toFinset] using h.guarded pre e post split⟩

theorem inplace_sequentially_correct (ops : List Event)
    (h : LinearMintHistory D AegisSheet.applicable ops) :
    materializedStateRel (applySeq D.toCRDTSig D.init ops) (run ops) :=
  inplaceReplayVerified.sequentially_correct ops h

theorem rawLo_false (C : Configuration D) (a b : Event) :
    ¬ Sal.MRDTs.Foundation.lo C.core a b := by
  rintro (⟨_, noncommuting⟩ | ⟨_, _, ordered, _⟩)
  · exact noncommuting (AegisSheet.all_comm a b)
  · exact RcRes.noConfusion ordered

theorem respects_rawLo (C : Configuration D) (ops : List Event) :
    respects ops (Sal.MRDTs.Foundation.lo C.core) := by
  induction ops with
  | nil => exact List.Pairwise.nil
  | cons event rest ih =>
      exact List.pairwise_cons.mpr
        ⟨fun later _ => rawLo_false C later event, ih⟩

/-- Reachable merged versions have a timestamp-canonical serialization in
which every event retains an honest causal origin, the incremental machine
materializes exactly the replicated state, and both sides answer the same
queries. -/
noncomputable def sequentialCorrectness :
    SequentialCorrectnessCertificate D AegisSheet.generation
      (InteractionSpec.raw D) clientSpec materializedStateRel where
  sound C exec replay := by
    intro v s E hver
    obtain ⟨ops, hperm, _, hfold⟩ := replay v s E hver
    have legal := canonical_causalOriginLegal exec hver hperm
    have canonicalPerm : listPermOf (canonical ops) E := by
      refine ⟨canonical_nodup hperm.1, ?_⟩
      intro event
      exact (canonical_perm ops).mem_iff.trans (hperm.2 event)
    have canonicalState :
        applySeq D.toCRDTSig D.init (canonical ops) = s := by
      rw [AegisSheet.applySeq_eq_toFinset, canonical_toFinset]
      rw [← AegisSheet.applySeq_eq_toFinset]
      exact hfold
    have refined := causalOriginSequentialSound (canonical ops) legal
    have refinedAtState : materializedStateRel s
        (clientSpec.run (canonical ops)) := by
      rw [← canonicalState]
      exact refined
    refine ⟨canonical ops, canonicalPerm,
      respects_interactionLoOn_raw_of_lo (respects_rawLo C (canonical ops)),
      legal, refinedAtState, ?_⟩
    intro query
    cases query
    simpa [D, clientSpec] using refinedAtState.2.2.symm

/-! PASS/FAIL controls for the ordering premise used by the refinement. -/

/-- Two independent replicas may both insert into an empty sheet.  Each event
truthfully records an empty issuer frontier. -/
def independentRow : Event :=
  axisEvent 11 1 ∅ .insert .row 101 none (some 10)

def independentColumn : Event :=
  axisEvent 12 2 ∅ .insert .column 202 none (some 10)

theorem independent_events_individually_applicable :
    applicable independentRow ∅ ∧ applicable independentColumn ∅ := by
  native_decide

/-- The older replay specification cannot serve as the public package: its
`GuardedChronological` predicate rechecks an event against the whole
serialization prefix. That is too strong for a merge because the second
independent event did not see the first. `CausalOriginLegal` repairs this
boundary without weakening issuance. -/
theorem concurrent_origins_not_guarded_chronological :
    Chronological [independentRow, independentColumn] ∧
      ¬ GuardedChronological [independentRow, independentColumn] := by
  constructor
  · apply chronological_of_pairwise
    native_decide
  · intro guarded
    have bad := guarded.2 [independentRow] independentColumn [] (by simp)
    have bad := bad.1
    change applicableB independentColumn {independentRow} = true at bad
    have hfalse : applicableB independentColumn {independentRow} = false := by
      native_decide
    rw [hfalse] at bad
    exact Bool.noConfusion bad

/-- PASS control: both concurrent insertions retain their truthful empty
origin even though one must appear second in the chronological witness. -/
theorem concurrent_origins_causal_legal :
    CausalOriginLegal [independentRow, independentColumn] := by
  constructor
  · apply chronological_of_pairwise
    native_decide
  · intro pre e post split
    have member : e ∈ [independentRow, independentColumn] := by
      rw [split]
      simp
    simp at member
    rcases member with rfl | rfl
    · exact ⟨∅, by simp, independent_events_individually_applicable.1⟩
    · exact ⟨∅, by simp, independent_events_individually_applicable.2⟩

/-- An event cannot cite a causal timestamp for which its history contains no
origin event or compact purge witness. -/
def unavailableOriginColumn : Event :=
  axisEvent 12 2 {999} .insert .column 202 none (some 10)

/-- FAIL control: origin legality is not an always-accepting replacement for
whole-prefix issuance. -/
theorem unavailable_origin_not_causal_legal :
    ¬ CausalOriginLegal [unavailableOriginColumn] := by
  intro legal
  obtain ⟨origin, subset, guard⟩ :=
    legal.2 [] unavailableOriginColumn [] rfl
  have empty : origin = ∅ := Finset.Subset.antisymm subset (by simp)
  subst origin
  have guard := guard.1
  change applicableB unavailableOriginColumn ∅ = true at guard
  have rejected : applicableB unavailableOriginColumn ∅ = false := by
    native_decide
  rw [rejected] at guard
  exact Bool.noConfusion guard

example : [baseRow, baseColumn, baseCell].Pairwise timestampLT := by
  native_decide

example : ¬ [baseColumn, baseRow].Pairwise timestampLT := by
  native_decide

#print axioms chronological_eq_of_toFinset_eq
#print axioms materialize_insert
#print axioms guarded_history_materializes
#print axioms storedAxisIds_eq_axisIds
#print axioms AegisSheet.GC.axisKeepTimes_eq
#print axioms coveredAxisTimes_subset_raw
#print axioms liveAxisTokens_eq_raw
#print axioms visibleIds_materialize
#print axioms latestPositions_axisPositionVersions
#print axioms materializedCellValues_eq_raw
#print axioms rangeStored_values
#print axioms observationInvariant_of_facts
#print axioms linearMintHistory_provenance
#print axioms guarded_history_observes
#print axioms inplaceSequentialSound
#print axioms canonical_causalOriginLegal
#print axioms causalOriginSequentialSound
#print axioms sequentialCorrectness
#print axioms inplaceReplayVerified
#print axioms inplace_sequentially_correct
#print axioms concurrent_origins_not_guarded_chronological
#print axioms concurrent_origins_causal_legal
#print axioms unavailable_origin_not_causal_legal

/-! Directed equivalence checks against the replicated semantic reference. -/

def baseRun : State := run [baseRow, baseColumn, baseCell]
example : (view baseRun).rows = {r0} := by native_decide
example : (view baseRun).columns = {c0} := by native_decide
example : (view baseRun).cell r0 c0 = {0} := by native_decide

def editRemoveRun₁ : State :=
  run [baseRow, baseColumn, baseCell, concurrentRemove, concurrentEdit]
def editRemoveRun₂ : State :=
  run [baseRow, baseColumn, baseCell, concurrentEdit, concurrentRemove]
example : (view editRemoveRun₁).rows = (view editRemoveRun₂).rows := by native_decide
example : (view editRemoveRun₁).cell r0 c0 = {1} := by native_decide
example : (view editRemoveRun₂).cell r0 c0 = {1} := by native_decide
example : (view editRemoveRun₁).rows =
    (Sal.MRDTs.Instances.AegisSheet.view editRemoveState).rows := by native_decide

def conflictUndoRun : State :=
  run [baseRow, baseColumn, baseCell, editA, editB, undoA]
example : (view conflictUndoRun).cell r0 c0 = {0, 2} := by native_decide
example : (view conflictUndoRun).cell r0 c0 =
    (Sal.MRDTs.Instances.AegisSheet.view undoConflictState).cell r0 c0 := by native_decide

def moveRemoveRun₁ : State :=
  run [baseRow, baseColumn, baseCell, concurrentRemove, moveRow]
def moveRemoveRun₂ : State :=
  run [baseRow, baseColumn, baseCell, moveRow, concurrentRemove]
example : (view moveRemoveRun₁).rows = {r0} := by native_decide
example : (view moveRemoveRun₂).rows = {r0} := by native_decide
example : (view moveRemoveRun₁).rowPosition r0 = {30} := by native_decide
example : (view moveRemoveRun₂).rowPosition r0 = {30} := by native_decide

def rangeRun : State :=
  run [baseRow, baseColumn, baseCell, secondRow, secondColumn, addRange]
example : (view rangeRun).range 30 = {rangeSpec} := by native_decide
example : (view rangeRun).range 30 =
    (Sal.MRDTs.Instances.AegisSheet.view rangedBase).range 30 := by native_decide

end Sal.MRDTs.Instances.AegisSheet.Sequential

namespace Sal.MRDTs.Instances.AegisSheet

open Sal.MRDTs.Foundation

/-- Production verification package. Its sequential specification is the
independent incremental spreadsheet machine, not an event-list echo. -/
noncomputable def replayVerified : ReplayVerifiedMRDT D :=
  Sequential.inplaceReplayVerified

/-- Complete public AegisSheet package. Unlike `replayVerified`, this package
certifies a legal client history for every reachable ordinary or virtual-LCA
version and relates that history to the independent incremental spreadsheet
machine. -/
noncomputable def verified : VerifiedMRDT D where
  issuance := generation
  interaction := InteractionSpec.raw D
  convergence := convergence
  Spec := Sequential.clientSpec
  Rel := Sequential.materializedStateRel
  sequentialCorrectness := Sequential.sequentialCorrectness

theorem spec_linearizable {C : Configuration D}
    (h : MintCertifiedReach D generation C) :
    IsSpecRALinearizable D (InteractionSpec.raw D)
      Sequential.clientSpec Sequential.materializedStateRel C :=
  verified.converges h

theorem spec_linearizableV {C : Configuration D}
    (h : MintCertifiedReachV D (canonicalVirtualLCA D) generation C) :
    IsSpecRALinearizable D (InteractionSpec.raw D)
      Sequential.clientSpec Sequential.materializedStateRel C :=
  verified.convergesV h

theorem sequentially_correct (ops : List Event)
    (h : LinearMintHistory D applicable ops) :
    Sequential.materializedStateRel
      (applySeq D.toCRDTSig D.init ops) (Sequential.run ops) :=
  Sequential.inplace_sequentially_correct ops h

theorem observationally_correct (ops : List Event)
    (h : LinearMintHistory D applicable ops) :
    Sequential.view (Sequential.run ops) = view ops.toFinset :=
  Sequential.guarded_history_observes h

#print axioms replayVerified
#print axioms verified
#print axioms spec_linearizable
#print axioms spec_linearizableV
#print axioms sequentially_correct
#print axioms observationally_correct

end Sal.MRDTs.Instances.AegisSheet
