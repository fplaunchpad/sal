import Sal.MRDTs.Instances.AegisSheetSequential

/-!
# AegisSheet sequential-abstraction audit

The client-visible `View` is not a transition congruence. A sequential state
must retain enough semantic history to distinguish observed-remove tokens and
active write identities. The SPOTs below use reachable prefixes and operations
issued honestly at a named causal origin; they do not rely on malformed raw
states.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction

open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.AegisSheet
open Sal.MRDTs.Instances.AegisSheet.Sequential

def baseOps : List Event := [baseRow, baseColumn, baseCell]

/-- Concrete origin extractor used by the audit SPOTs. Production legality is
existential and also supports compact purge timestamps that have no retained
event payload. -/
def encodedOrigin (ops : List Event) (e : Event) : Finset Event :=
  ops.toFinset.filter fun old => decide (old.1 ∈ e.seen)

theorem causalOriginLegal_of_encodedOrigins {ops : List Event}
    (chronological : Chronological ops)
    (origins : ∀ e ∈ ops, applicable e (encodedOrigin ops e)) :
    CausalOriginLegal ops := by
  refine ⟨chronological, ?_⟩
  intro pre e post split
  have eMember : e ∈ ops := by rw [split]; simp
  have guard := origins e eMember
  refine ⟨encodedOrigin ops e, ?_, guard⟩
  intro old oldMember
  have oldWhole : old ∈ ops := by
    have := (Finset.mem_filter.mp oldMember).1
    simpa using this
  have oldTime : old.1 < e.1 :=
    guard.2.lt old.1 (eventTime_mem oldMember)
  have oldPrefix : old ∈ pre :=
    mem_prefix_of_chronological chronological split oldWhole oldTime
  simpa using oldPrefix

/-- A move to the current position changes no client-visible field, but adds
an observed-remove keep token for the row. -/
def samePositionMove : Event :=
  axisEvent 4 1 {1, 2, 3} .move .row r0 (some 10) (some 10)

/-- This removal is issued at the base origin, concurrently with
`samePositionMove`. -/
def baseOriginRemove : Event :=
  axisEvent 5 2 {1, 2, 3} .remove .row r0 (some 10) none

def tokenBase : State := run baseOps
def tokenExtended : State := step tokenBase samePositionMove

theorem tokenExtended_reachable :
    tokenExtended = run (baseOps ++ [samePositionMove]) := by
  simp [tokenExtended, tokenBase, run, spec]

theorem samePositionMove_applicable :
    applicable samePositionMove baseOps.toFinset := by
  native_decide

theorem baseOriginRemove_applicable :
    applicable baseOriginRemove baseOps.toFinset := by
  native_decide

def tokenMergedOps : List Event :=
  baseOps ++ [samePositionMove, baseOriginRemove]

theorem token_merged_history_legal : CausalOriginLegal tokenMergedOps := by
  apply causalOriginLegal_of_encodedOrigins
  · apply chronological_of_pairwise
    native_decide
  · intro e member
    simp [tokenMergedOps, baseOps] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      native_decide

theorem token_rows_equal :
    (view tokenBase).rows = (view tokenExtended).rows := by
  native_decide

theorem token_columns_equal :
    (view tokenBase).columns = (view tokenExtended).columns := by
  native_decide

theorem token_rowPosition_equal :
    (view tokenBase).rowPosition r0 =
      (view tokenExtended).rowPosition r0 := by
  native_decide

theorem token_cell_equal :
    (view tokenBase).cell r0 c0 = (view tokenExtended).cell r0 c0 := by
  native_decide

theorem token_rowLiveB_equal (id : StableId) :
    finsetNonemptyB (tokenBase.rowTokens id) =
      finsetNonemptyB (tokenExtended.rowTokens id) := by
  by_cases h : id = r0
  · subst id
    native_decide
  · simp [tokenExtended, samePositionMove, step, Event.action,
      Command.effect, axisEvent, applyAxis, setAxisPosition, addAxisKeep,
      h]

theorem token_columnTokens_equal :
    tokenBase.columnTokens = tokenExtended.columnTokens := by
  rfl

theorem token_cells_state_equal : tokenBase.cells = tokenExtended.cells := by
  rfl

theorem token_purges_equal : tokenBase.purges = tokenExtended.purges := by
  rfl

theorem token_versionPurged_equal (row column : StableId)
    (version : CellVersion) :
    versionPurged tokenBase row column version =
      versionPurged tokenExtended row column version := by
  simp [versionPurged, token_purges_equal]

theorem token_views_equal : view tokenBase = view tokenExtended := by
  apply View.ext
  · native_decide
  · native_decide
  · funext id
    by_cases h : id = r0
    · subst id
      exact token_rowPosition_equal
    · change latestPositions (tokenBase.rowPositions id) =
          latestPositions (tokenExtended.rowPositions id)
      congr 1
      simp [tokenExtended, samePositionMove, step, Event.action,
        Command.effect, axisEvent, applyAxis, setAxisPosition, addAxisKeep,
        h]
  · funext id
    rfl
  · funext row column
    change (if finsetNonemptyB (tokenBase.rowTokens row) &&
          finsetNonemptyB (tokenBase.columnTokens column) then
        versionValues ((tokenBase.cells row column).filter fun version =>
          !versionPurged tokenBase row column version) else ∅) =
      (if finsetNonemptyB (tokenExtended.rowTokens row) &&
          finsetNonemptyB (tokenExtended.columnTokens column) then
        versionValues ((tokenExtended.cells row column).filter fun version =>
          !versionPurged tokenExtended row column version) else ∅)
    rw [token_rowLiveB_equal row, token_columnTokens_equal,
      token_cells_state_equal]
    by_cases live : (finsetNonemptyB (tokenExtended.rowTokens row) &&
        finsetNonemptyB (tokenExtended.columnTokens column)) = true
    · simp only [live, if_true]
      apply congrArg versionValues
      apply Finset.filter_congr
      intro version _
      rw [token_versionPurged_equal]
    · simp [live]
  · funext id
    rfl

/-- FAIL control for the visible-sheet quotient: applying the same honestly
issued concurrent removal kills the base row but not the row with the hidden
concurrent keep token. -/
theorem row_tokens_distinguish_future :
    (view (step tokenBase baseOriginRemove)).rows = ∅ ∧
    (view (step tokenExtended baseOriginRemove)).rows = {r0} := by
  native_decide

theorem token_future_views_ne :
    view (step tokenBase baseOriginRemove) ≠
      view (step tokenExtended baseOriginRemove) := by
  intro same
  have rowsSame := congrArg View.rows same
  have distinguished := row_tokens_distinguish_future
  rw [distinguished.1, distinguished.2] at rowsSame
  have impossible : r0 ∈ (∅ : Finset StableId) := by
    rw [rowsSame]
    simp
  simpa using impossible

/-- No deterministic sequential machine whose complete state is just `View`
can implement both reachable prefixes and their common legal continuation. -/
theorem no_view_only_step :
    ¬ ∃ next : View → Event → View,
      next (view tokenBase) baseOriginRemove =
          view (step tokenBase baseOriginRemove) ∧
      next (view tokenExtended) baseOriginRemove =
          view (step tokenExtended baseOriginRemove) := by
  rintro ⟨next, baseExact, extendedExact⟩
  apply token_future_views_ne
  calc
    view (step tokenBase baseOriginRemove) =
        next (view tokenBase) baseOriginRemove := baseExact.symm
    _ = next (view tokenExtended) baseOriginRemove := by
      rw [token_views_equal]
    _ = view (step tokenExtended baseOriginRemove) := extendedExact

/-! ## Active cell-version identity -/

/-- A local overwrite writes the same visible value under a fresh version. -/
def sameValueOverwrite : Event :=
  cellEvent 4 1 {1, 2, 3} r0 c0 {0} {0} {3}

/-- This edit is issued concurrently at the base origin and removes only the
base version. -/
def baseOriginEdit : Event :=
  cellEvent 5 2 {1, 2, 3} r0 c0 {0} {1} {3}

def cellBase : State := run baseOps
def cellReversioned : State := step cellBase sameValueOverwrite

theorem cellReversioned_reachable :
    cellReversioned = run (baseOps ++ [sameValueOverwrite]) := by
  simp [cellReversioned, cellBase, run, spec]

theorem sameValueOverwrite_applicable :
    applicable sameValueOverwrite baseOps.toFinset := by
  native_decide

theorem baseOriginEdit_applicable :
    applicable baseOriginEdit baseOps.toFinset := by
  native_decide

def cellMergedOps : List Event :=
  baseOps ++ [sameValueOverwrite, baseOriginEdit]

theorem cell_merged_history_legal : CausalOriginLegal cellMergedOps := by
  apply causalOriginLegal_of_encodedOrigins
  · apply chronological_of_pairwise
    native_decide
  · intro e member
    simp [cellMergedOps, baseOps] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      native_decide

theorem cell_values_initially_equal :
    (view cellBase).cell r0 c0 = (view cellReversioned).cell r0 c0 := by
  native_decide

theorem cell_rowLiveB_equal (id : StableId) :
    finsetNonemptyB (cellBase.rowTokens id) =
      finsetNonemptyB (cellReversioned.rowTokens id) := by
  by_cases h : id = r0
  · subst id
    native_decide
  · simp [cellReversioned, sameValueOverwrite, step, Event.action,
      Command.effect, cellEvent, applyCell, addAxisKeep, h]

theorem cell_columnLiveB_equal (id : StableId) :
    finsetNonemptyB (cellBase.columnTokens id) =
      finsetNonemptyB (cellReversioned.columnTokens id) := by
  by_cases h : id = c0
  · subst id
    native_decide
  · simp [cellReversioned, sameValueOverwrite, step, Event.action,
      Command.effect, cellEvent, applyCell, addAxisKeep, h]

theorem cell_cells_other {row column : StableId}
    (other : row ≠ r0 ∨ column ≠ c0) :
    cellBase.cells row column = cellReversioned.cells row column := by
  rcases other with rowOther | columnOther
  · simp [cellReversioned, sameValueOverwrite, step, Event.action,
      Command.effect, cellEvent, applyCell, addAxisKeep, rowOther]
  · by_cases rowSame : row = r0
    · subst row
      simp [cellReversioned, sameValueOverwrite, step, Event.action,
        Command.effect, cellEvent, applyCell, addAxisKeep, columnOther]
    · simp [cellReversioned, sameValueOverwrite, step, Event.action,
        Command.effect, cellEvent, applyCell, addAxisKeep, rowSame]

theorem cell_versionPurged_equal (row column : StableId)
    (version : CellVersion) :
    versionPurged cellBase row column version =
      versionPurged cellReversioned row column version := by
  rfl

theorem cell_views_equal : view cellBase = view cellReversioned := by
  apply View.ext
  · native_decide
  · native_decide
  · funext id
    rfl
  · funext id
    rfl
  · funext row column
    by_cases hr : row = r0
    · subst row
      by_cases hc : column = c0
      · subst column
        exact cell_values_initially_equal
      · change (if finsetNonemptyB (cellBase.rowTokens r0) &&
            finsetNonemptyB (cellBase.columnTokens column) then
          versionValues ((cellBase.cells r0 column).filter fun version =>
            !versionPurged cellBase r0 column version) else ∅) =
        (if finsetNonemptyB (cellReversioned.rowTokens r0) &&
            finsetNonemptyB (cellReversioned.columnTokens column) then
          versionValues ((cellReversioned.cells r0 column).filter fun version =>
            !versionPurged cellReversioned r0 column version) else ∅)
        rw [cell_rowLiveB_equal r0, cell_columnLiveB_equal column,
          ← cell_cells_other (Or.inr hc)]
        simp only [cell_versionPurged_equal]
    · change (if finsetNonemptyB (cellBase.rowTokens row) &&
          finsetNonemptyB (cellBase.columnTokens column) then
        versionValues ((cellBase.cells row column).filter fun version =>
          !versionPurged cellBase row column version) else ∅) =
      (if finsetNonemptyB (cellReversioned.rowTokens row) &&
          finsetNonemptyB (cellReversioned.columnTokens column) then
        versionValues ((cellReversioned.cells row column).filter fun version =>
          !versionPurged cellReversioned row column version) else ∅)
      rw [cell_rowLiveB_equal row, cell_columnLiveB_equal column,
        ← cell_cells_other (Or.inl hr)]
      simp only [cell_versionPurged_equal]
  · funext id
    rfl

/-- FAIL control: values alone cannot implement selective overwrite. The
timestamped active write identity is semantic history, not a cache artifact. -/
theorem cell_versions_distinguish_future :
    (view (step cellBase baseOriginEdit)).cell r0 c0 = {1} ∧
    (view (step cellReversioned baseOriginEdit)).cell r0 c0 = {0, 1} := by
  native_decide

theorem cell_future_views_ne :
    view (step cellBase baseOriginEdit) ≠
      view (step cellReversioned baseOriginEdit) := by
  intro same
  have valuesSame := congrArg (fun result => result.cell r0 c0) same
  change (view (step cellBase baseOriginEdit)).cell r0 c0 =
    (view (step cellReversioned baseOriginEdit)).cell r0 c0 at valuesSame
  have distinguished := cell_versions_distinguish_future
  rw [distinguished.1, distinguished.2] at valuesSame
  have impossible : 0 ∈ ({1} : Finset CellValue) := by
    rw [valuesSame]
    simp
  exact Nat.zero_ne_one (Finset.mem_singleton.mp impossible)

/-! ## Active range-version identity -/

def rangeBaseOps : List Event :=
  [baseRow, baseColumn, baseCell, secondRow, secondColumn, addRange]

def sameRangeOverwrite : Event :=
  rangeEvent 7 1 {1, 2, 3, 4, 5, 6} 30
    (some rangeSpec) (some rangeSpec) {6}

def alternateRange : RangeSpec := ⟨r1, r1, c0, c1⟩

def baseOriginRangeEdit : Event :=
  rangeEvent 8 2 {1, 2, 3, 4, 5, 6} 30
    (some rangeSpec) (some alternateRange) {6}

def rangeBase : State := run rangeBaseOps
def rangeReversioned : State := step rangeBase sameRangeOverwrite

theorem rangeReversioned_reachable :
    rangeReversioned = run (rangeBaseOps ++ [sameRangeOverwrite]) := by
  simp [rangeReversioned, rangeBase, run, spec]

theorem sameRangeOverwrite_applicable :
    applicable sameRangeOverwrite rangeBaseOps.toFinset := by
  native_decide

theorem baseOriginRangeEdit_applicable :
    applicable baseOriginRangeEdit rangeBaseOps.toFinset := by
  native_decide

def rangeMergedOps : List Event :=
  rangeBaseOps ++ [sameRangeOverwrite, baseOriginRangeEdit]

theorem range_merged_history_legal : CausalOriginLegal rangeMergedOps := by
  apply causalOriginLegal_of_encodedOrigins
  · apply chronological_of_pairwise
    native_decide
  · intro e member
    simp [rangeMergedOps, rangeBaseOps] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      native_decide

theorem range_values_initially_equal :
    (view rangeBase).range 30 = (view rangeReversioned).range 30 := by
  native_decide

theorem range_views_equal : view rangeBase = view rangeReversioned := by
  apply View.ext
  · rfl
  · rfl
  · funext id
    rfl
  · funext id
    rfl
  · funext row column
    rfl
  · funext id
    by_cases h : id = 30
    · subst id
      exact range_values_initially_equal
    · simp [rangeReversioned, sameRangeOverwrite, step, Event.action,
        Command.effect, rangeEvent, applyRange, view, h]

/-- FAIL control: a visible range value does not identify the active write
that a selective overwrite removes. -/
theorem range_versions_distinguish_future :
    (view (step rangeBase baseOriginRangeEdit)).range 30 = {alternateRange} ∧
    (view (step rangeReversioned baseOriginRangeEdit)).range 30 =
      {rangeSpec, alternateRange} := by
  native_decide

theorem range_future_views_ne :
    view (step rangeBase baseOriginRangeEdit) ≠
      view (step rangeReversioned baseOriginRangeEdit) := by
  intro same
  have valuesSame := congrArg (fun result => result.range 30) same
  change (view (step rangeBase baseOriginRangeEdit)).range 30 =
    (view (step rangeReversioned baseOriginRangeEdit)).range 30 at valuesSame
  have distinguished := range_versions_distinguish_future
  rw [distinguished.1, distinguished.2] at valuesSame
  have impossible : rangeSpec ∈ ({alternateRange} : Finset RangeSpec) := by
    rw [valuesSame]
    simp
  have different : rangeSpec ≠ alternateRange := by native_decide
  exact different (Finset.mem_singleton.mp impossible)

#print axioms row_tokens_distinguish_future
#print axioms no_view_only_step
#print axioms cell_versions_distinguish_future
#print axioms range_versions_distinguish_future
#print axioms cell_future_views_ne
#print axioms range_future_views_ne
#print axioms token_merged_history_legal
#print axioms cell_merged_history_legal
#print axioms range_merged_history_legal

end Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction
