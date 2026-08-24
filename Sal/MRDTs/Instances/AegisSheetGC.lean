import Sal.MRDTs.Instances.AegisSheet
import Sal.MRDTs.Framework.StateGC
import Sal.MRDTs.GC.Distributed

/-!
# AegisSheet state garbage collection

The paper's purge removes contents from deleted rows and columns and states
that a late old change may restore the axis but not the purged contents. That
operation changes future behavior. This module records the smallest checked
counterexample to treating it as silent collection, then proves the corrected
semantic-marker collector through the framework's `StateGCCertificate`.

A sound implementation must retain a semantic purge marker (cutoff plus
reclaimed timestamp-to-coordinate entries) or strengthen the generation
protocol so no later continuation can reveal the removed contents. Merely
filtering the local materialization is insufficient.
-/

namespace Sal.MRDTs.Instances.AegisSheet.GC

open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.AegisSheet

theorem fold_or_eq_true_iff {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → Bool) :
    Finset.fold (· || ·) false f s = true ↔
      ∃ x ∈ s, f x = true := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s fresh ih =>
      rw [Finset.fold_insert fresh]
      simp [ih]

theorem fold_and_eq_true_iff {α : Type} [DecidableEq α]
    (s : Finset α) (f : α → Bool) :
    Finset.fold (· && ·) true f s = true ↔
      ∀ x ∈ s, f x = true := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s fresh ih =>
      rw [Finset.fold_insert fresh]
      simp [ih]

theorem fold_or_true_mono {α : Type} [DecidableEq α]
    {s t : Finset α} (subset : s ⊆ t) (f : α → Bool)
    (h : Finset.fold (· || ·) false f s = true) :
    Finset.fold (· || ·) false f t = true := by
  rw [fold_or_eq_true_iff] at h ⊢
  obtain ⟨x, member, hx⟩ := h
  exact ⟨x, subset member, hx⟩

/-- All retained events carry enough causal metadata for payload elision to
remain closed under later update and merge. -/
def StateValid (events : Finset Event) : Prop :=
  ∀ e ∈ events, metadataValidB events e = true

/-- A timestamp names at most one event. This is an execution invariant, not
an extra runtime index. -/
def TimestampUnique (events : Finset Event) : Prop :=
  ∀ a ∈ events, ∀ b ∈ events, a.1 = b.1 → a = b

/-- Two branch heads agree on the meaning of every shared timestamp. -/
def TimestampCompatible (a b : Finset Event) : Prop :=
  ∀ ea ∈ a, ∀ eb ∈ b, ea.1 = eb.1 → ea = eb

theorem timestampUnique_empty : TimestampUnique (∅ : Finset Event) := by
  simp [TimestampUnique]

theorem timestampUnique_insert {events : Finset Event} {e : Event}
    (unique : TimestampUnique events) (fresh : e.1 ∉ eventTimes events) :
    TimestampUnique (insert e events) := by
  intro a ha b hb same
  rcases Finset.mem_insert.mp ha with haeq | haold
  · subst a
    rcases Finset.mem_insert.mp hb with hbeq | hbold
    · exact hbeq.symm
    · exfalso
      apply fresh
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨b, hbold, same.symm⟩)
  · rcases Finset.mem_insert.mp hb with hbeq | hbold
    · subst b
      exfalso
      apply fresh
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨a, haold, same⟩)
    · exact unique a haold b hbold same

theorem timestampUnique_union {a b : Finset Event}
    (ua : TimestampUnique a) (ub : TimestampUnique b)
    (compatible : TimestampCompatible a b) : TimestampUnique (a ∪ b) := by
  intro x hx y hy same
  rw [Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact ua x hx y hy same
  · exact compatible x hx y hy same
  · exact (compatible y hy x hx same.symm).symm
  · exact ub x hx y hy same

theorem metadataValid_mono {small large : Finset Event}
    (subset : small ⊆ large) {e : Event}
    (valid : metadataValidB small e = true) :
    metadataValidB large e = true := by
  unfold metadataValidB at valid ⊢
  cases isCell : cellUpdate? e with
  | some update =>
    simp only [isCell] at valid
    rw [fold_and_eq_true_iff] at valid ⊢
    intro overwritten member
    have one := valid overwritten member
    simp only [Bool.and_eq_true] at one ⊢
    exact ⟨one.1, fold_or_true_mono subset _ one.2⟩
  | none =>
    simp only [isCell] at valid
    cases isRange : rangeUpdate? e with
    | some update =>
      simp only [isRange] at valid ⊢
      rw [fold_and_eq_true_iff] at valid ⊢
      intro overwritten member
      have one := valid overwritten member
      simp only [Bool.and_eq_true] at one ⊢
      exact ⟨one.1, fold_or_true_mono subset _ one.2⟩
    | none =>
      simp only [isRange] at valid
      cases isMarker : purge? e <;> simp_all only

theorem StateValid.mono {small large : Finset Event}
    (valid : StateValid small) (subset : small ⊆ large) :
    ∀ e ∈ small, metadataValidB large e = true := by
  intro e member
  exact metadataValid_mono subset (valid e member)

theorem stateValid_insert {events : Finset Event} {e : Event}
    (valid : StateValid events) (newValid : metadataValidB events e = true) :
    StateValid (insert e events) := by
  intro candidate member
  rcases Finset.mem_insert.mp member with same | old
  · subst candidate
    exact metadataValid_mono (Finset.subset_insert e events) newValid
  · exact metadataValid_mono (Finset.subset_insert e events) (valid candidate old)

theorem stateValid_union {a b : Finset Event}
    (ha : StateValid a) (hb : StateValid b) : StateValid (a ∪ b) := by
  intro e member
  rw [Finset.mem_union] at member
  rcases member with left | right
  · exact metadataValid_mono Finset.subset_union_left (ha e left)
  · exact metadataValid_mono Finset.subset_union_right (hb e right)

theorem cellUpdate_none_of_axisUpdate_some {e : Event} {u : AxisUpdate}
    (h : axisUpdate? e = some u) : cellUpdate? e = none := by
  cases action : e.action <;> simp [axisUpdate?, cellUpdate?, action] at h ⊢

theorem cellUpdate_none_of_rangeUpdate_some {e : Event} {u : RangeUpdate}
    (h : rangeUpdate? e = some u) : cellUpdate? e = none := by
  cases action : e.action <;> simp [rangeUpdate?, cellUpdate?, action] at h ⊢

def retainAfterLocalPurge (full : Finset Event) (e : Event) : Bool :=
  match cellUpdate? e with
  | some update =>
      axisLive full .row update.row && axisLive full .column update.column
  | none => true

/-- The tempting local implementation: discard cell versions whose row or
column is currently absent. -/
def naiveCollect (full : Finset Event) : Finset Event :=
  full.filter fun e => retainAfterLocalPurge full e

/-! The actual collector is driven by replicated purge evidence, rather than
the current materialized visibility of an axis.  Only cell payloads whose
timestamps occur in a retained marker's `covered` set may be removed. -/

def markerCoveredEntries (events : Finset Event) : Finset (Timestamp × Coordinate) :=
  events.biUnion fun e =>
    match purge? e with
    | some marker => marker.covered
    | none => ∅

def markerCoveredTimes (events : Finset Event) : Finset Timestamp :=
  (markerCoveredEntries events).image Prod.fst

def retainAfterSemanticPurge (full : Finset Event) (e : Event) : Bool :=
  match cellUpdate? e with
  | some update =>
      decide ((e.1, (update.row, update.column)) ∉ markerCoveredEntries full)
  | none => true

def semanticCollect (full : Finset Event) : Finset Event :=
  full.filter fun e => retainAfterSemanticPurge full e

theorem semanticCollect_subset (full : Finset Event) :
    semanticCollect full ⊆ full := Finset.filter_subset _ _

theorem noncell_retained {full : Finset Event} {e : Event}
    (member : e ∈ full) (noncell : cellUpdate? e = none) :
    e ∈ semanticCollect full := by
  simp [semanticCollect, retainAfterSemanticPurge, member, noncell]

theorem purge_retained {full : Finset Event} {e : Event} {marker : Purge}
    (member : e ∈ full) (isMarker : purge? e = some marker) :
    e ∈ semanticCollect full := by
  apply noncell_retained member
  unfold purge? at isMarker
  split at isMarker <;> simp_all [cellUpdate?]

theorem fold_or_semanticCollect_eq (full : Finset Event) (f : Event → Bool)
    (noncell : ∀ e, f e = true → cellUpdate? e = none) :
    Finset.fold (· || ·) false f (semanticCollect full) =
      Finset.fold (· || ·) false f full := by
  apply Bool.eq_iff_iff.mpr
  rw [fold_or_eq_true_iff, fold_or_eq_true_iff]
  constructor
  · rintro ⟨e, member, yes⟩
    exact ⟨e, semanticCollect_subset full member, yes⟩
  · rintro ⟨e, member, yes⟩
    exact ⟨e, noncell_retained member (noncell e yes), yes⟩

theorem filter_semanticCollect_eq (full : Finset Event) (f : Event → Bool)
    (noncell : ∀ e, f e = true → cellUpdate? e = none) :
    (semanticCollect full).filter (fun e => f e) =
      full.filter (fun e => f e) := by
  apply Finset.ext
  intro e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨member, yes⟩
    exact ⟨semanticCollect_subset full member, yes⟩
  · rintro ⟨member, yes⟩
    exact ⟨noncell_retained member (noncell e yes), yes⟩

theorem removesAxis_noncell {axis : Axis} {id : StableId} {e : Event}
    (h : removesAxis axis id e = true) : cellUpdate? e = none := by
  cases action : e.action <;>
    simp [removesAxis, cellUpdate?, action] at h ⊢

theorem axisCandidate_noncell {axis : Axis} {id : StableId} {e : Event}
    (h : axisCandidate axis id e = true) : cellUpdate? e = none := by
  unfold axisCandidate at h
  cases update : axisUpdate? e with
  | none => simp [update] at h
  | some u => exact cellUpdate_none_of_axisUpdate_some update

theorem axisKnown_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) :
    axisKnown (semanticCollect full) axis id = axisKnown full axis id := by
  unfold axisKnown
  apply fold_or_semanticCollect_eq
  intro e yes
  cases update : axisUpdate? e with
  | none => simp [update] at yes
  | some u => exact cellUpdate_none_of_axisUpdate_some update

theorem axisTokenRemoved_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) (token : Timestamp) :
    axisTokenRemoved (semanticCollect full) axis id token =
      axisTokenRemoved full axis id token := by
  unfold axisTokenRemoved
  apply fold_or_semanticCollect_eq
  intro e yes
  simp only [Bool.and_eq_true] at yes
  exact removesAxis_noncell yes.1

theorem laterAxisCandidate_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) (candidate : Event) :
    laterAxisCandidate (semanticCollect full) axis id candidate =
      laterAxisCandidate full axis id candidate := by
  unfold laterAxisCandidate
  apply fold_or_semanticCollect_eq
  intro e yes
  simp only [Bool.and_eq_true] at yes
  exact axisCandidate_noncell yes.1

theorem axisPositions_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) :
    axisPositions (semanticCollect full) axis id = axisPositions full axis id := by
  unfold axisPositions
  have filtered :
      (semanticCollect full).filter (fun e =>
        axisCandidate axis id e &&
          !laterAxisCandidate (semanticCollect full) axis id e) =
      full.filter (fun e =>
        axisCandidate axis id e && !laterAxisCandidate full axis id e) := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter]
    rw [laterAxisCandidate_semanticCollect]
    constructor
    · rintro ⟨member, yes⟩
      exact ⟨semanticCollect_subset full member, yes⟩
    · rintro ⟨member, yes⟩
      have both : axisCandidate axis id e = true ∧
          (!laterAxisCandidate full axis id e) = true := by
        simpa only [Bool.and_eq_true] using yes
      exact ⟨noncell_retained member
        (axisCandidate_noncell both.1), yes⟩
  rw [filtered]

theorem biUnion_semanticCollect_eq {α : Type} [DecidableEq α]
    (full : Finset Event) (g : Event → Finset α)
    (noncell : ∀ e x, x ∈ g e → cellUpdate? e = none) :
    (semanticCollect full).biUnion g = full.biUnion g := by
  apply Finset.ext
  intro x
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨e, member, hx⟩
    exact ⟨e, semanticCollect_subset full member, hx⟩
  · rintro ⟨e, member, hx⟩
    exact ⟨e, noncell_retained member (noncell e x hx), hx⟩

theorem axisIds_semanticCollect (full : Finset Event) (axis : Axis) :
    axisIds (semanticCollect full) axis = axisIds full axis := by
  unfold axisIds
  apply biUnion_semanticCollect_eq
  intro e id member
  cases update : axisUpdate? e with
  | none => simp [update] at member
  | some u => exact cellUpdate_none_of_axisUpdate_some update

theorem rangeOverwritten_semanticCollect (full : Finset Event)
    (candidate : Event) :
    rangeOverwritten (semanticCollect full) candidate =
      rangeOverwritten full candidate := by
  unfold rangeOverwritten
  apply fold_or_semanticCollect_eq
  intro e yes
  cases update : rangeUpdate? e with
  | none => simp [update] at yes
  | some u => exact cellUpdate_none_of_rangeUpdate_some update

theorem rangeValues_semanticCollect (full : Finset Event) (id : RangeId) :
    rangeValues (semanticCollect full) id = rangeValues full id := by
  unfold rangeValues
  have filtered :
      (semanticCollect full).filter (fun e =>
        rangeMatches id e && !rangeOverwritten (semanticCollect full) e) =
      full.filter (fun e =>
        rangeMatches id e && !rangeOverwritten full e) := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter]
    rw [rangeOverwritten_semanticCollect]
    constructor
    · rintro ⟨member, yes⟩
      exact ⟨semanticCollect_subset full member, yes⟩
    · rintro ⟨member, yes⟩
      have noncell : cellUpdate? e = none := by
        unfold rangeMatches at yes
        cases update : rangeUpdate? e with
        | none => simp [update] at yes
        | some u => exact cellUpdate_none_of_rangeUpdate_some update
      exact ⟨noncell_retained member noncell, yes⟩
  rw [filtered]

theorem markerCoveredEntries_semanticCollect (full : Finset Event) :
    markerCoveredEntries (semanticCollect full) = markerCoveredEntries full := by
  apply Finset.ext
  intro entry
  simp only [markerCoveredEntries, Finset.mem_biUnion]
  constructor
  · rintro ⟨event, member, covered⟩
    exact ⟨event, semanticCollect_subset full member, covered⟩
  · rintro ⟨event, member, covered⟩
    have retained : event ∈ semanticCollect full := by
      cases isMarker : purge? event with
      | none => simp [isMarker] at covered
      | some marker => exact purge_retained member isMarker
    exact ⟨event, retained, covered⟩

theorem markerCoveredTimes_semanticCollect (full : Finset Event) :
    markerCoveredTimes (semanticCollect full) = markerCoveredTimes full := by
  simp only [markerCoveredTimes, markerCoveredEntries_semanticCollect]

def coveredAxisTimes (events : Finset Event) (axis : Axis)
    (id : StableId) : Finset Timestamp :=
  (markerCoveredEntries events).biUnion fun entry =>
    if match axis with
      | .row => entry.2.1 == id
      | .column => entry.2.2 == id
    then {entry.1} else ∅

theorem axisKeepTimes_eq (events : Finset Event) (axis : Axis)
    (id : StableId) :
    axisKeepTimes events axis id =
      (events.filter fun e => keepsAxis axis id e).image (fun e => e.1) ∪
        coveredAxisTimes events axis id := by
  unfold axisKeepTimes coveredAxisTimes markerCoveredEntries
  apply congrArg (fun covered =>
    (events.filter fun e => keepsAxis axis id e).image (fun e => e.1) ∪ covered)
  rw [Finset.biUnion_biUnion]
  apply Finset.biUnion_congr rfl
  intro event _
  cases marker : purge? event <;> rfl

theorem coveredAxisTimes_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) :
    coveredAxisTimes (semanticCollect full) axis id =
      coveredAxisTimes full axis id := by
  unfold coveredAxisTimes
  rw [markerCoveredEntries_semanticCollect]

theorem coordinate_eq_of_keepsAxis_cell {axis : Axis} {id : StableId}
    {e : Event} {update : CellUpdate} (isCell : cellUpdate? e = some update)
    (keeps : keepsAxis axis id e = true) :
    match axis with
    | .row => update.row = id
    | .column => update.column = id := by
  cases axis <;> cases action : e.action <;>
    simp [cellUpdate?, keepsAxis, action] at isCell keeps ⊢
  all_goals subst_vars; rfl

theorem axisKeepTimes_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) :
    axisKeepTimes (semanticCollect full) axis id =
      axisKeepTimes full axis id := by
  rw [axisKeepTimes_eq, axisKeepTimes_eq,
    coveredAxisTimes_semanticCollect]
  apply Finset.ext
  intro token
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨e, ⟨member, keeps⟩, rfl⟩ | covered)
    · exact Or.inl ⟨e, ⟨semanticCollect_subset full member, keeps⟩, rfl⟩
    · exact Or.inr covered

  · rintro (⟨e, ⟨member, keeps⟩, rfl⟩ | covered)
    · by_cases retained : e ∈ semanticCollect full
      · exact Or.inl ⟨e, ⟨retained, keeps⟩, rfl⟩
      · have isSome : (cellUpdate? e).isSome := by
          by_contra absent
          rw [Option.not_isSome_iff_eq_none] at absent
          exact retained (noncell_retained member absent)
        rcases Option.isSome_iff_exists.mp isSome with ⟨update, isCell⟩
        have pairCovered :
            (e.1, (update.row, update.column)) ∈ markerCoveredEntries full := by
          simp [semanticCollect, retainAfterSemanticPurge, member, isCell]
            at retained
          exact retained
        right
        unfold coveredAxisTimes
        rw [Finset.mem_biUnion]
        refine ⟨(e.1, (update.row, update.column)), pairCovered, ?_⟩
        have coordinate := coordinate_eq_of_keepsAxis_cell isCell keeps
        cases axis <;> simp_all
    · exact Or.inr covered

theorem liveAxisTokens_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) :
    liveAxisTokens (semanticCollect full) axis id =
      liveAxisTokens full axis id := by
  unfold liveAxisTokens
  rw [axisKeepTimes_semanticCollect]
  apply Finset.filter_congr
  intro token _
  rw [axisTokenRemoved_semanticCollect]

theorem axisLive_semanticCollect (full : Finset Event) (axis : Axis)
    (id : StableId) :
    axisLive (semanticCollect full) axis id = axisLive full axis id := by
  unfold axisLive
  rw [axisKnown_semanticCollect, liveAxisTokens_semanticCollect]

theorem liveAxisIds_semanticCollect (full : Finset Event) (axis : Axis) :
    liveAxisIds (semanticCollect full) axis = liveAxisIds full axis := by
  unfold liveAxisIds
  rw [axisIds_semanticCollect]
  apply Finset.filter_congr
  intro id _
  rw [axisLive_semanticCollect]

theorem eventTimes_eq (events : Finset Event) :
    eventTimes events = events.image (fun e => e.1) ∪ markerCoveredTimes events := by
  unfold eventTimes markerCoveredTimes markerCoveredEntries
  rw [Finset.biUnion_image]
  apply congrArg (fun covered => events.image (fun e => e.1) ∪ covered)
  apply Finset.biUnion_congr rfl
  intro event _
  cases purge? event <;> rfl

theorem eventTimes_semanticCollect (full : Finset Event) :
    eventTimes (semanticCollect full) = eventTimes full := by
  rw [eventTimes_eq, eventTimes_eq, markerCoveredTimes_semanticCollect]
  apply Finset.ext
  intro timestamp
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨event, member, rfl⟩ | covered)
    · exact Or.inl ⟨event, semanticCollect_subset full member, rfl⟩
    · exact Or.inr covered
  · rintro (⟨event, member, rfl⟩ | covered)
    · by_cases retained : event ∈ semanticCollect full
      · exact Or.inl ⟨event, retained, rfl⟩
      · have isCell : (cellUpdate? event).isSome := by
          by_contra absent
          rw [Option.not_isSome_iff_eq_none] at absent
          exact retained (noncell_retained member absent)
        have coveredTime : event.1 ∈ markerCoveredTimes full := by
          rcases Option.isSome_iff_exists.mp isCell with ⟨update, isUpdate⟩
          simp [semanticCollect, retainAfterSemanticPurge, member, isUpdate]
            at retained
          exact Finset.mem_image.mpr ⟨
            (event.1, (update.row, update.column)), retained, rfl⟩
        exact Or.inr coveredTime
    · exact Or.inr covered

theorem semanticCollect_idempotent (full : Finset Event) :
    semanticCollect (semanticCollect full) = semanticCollect full := by
  apply Finset.ext
  intro event
  rw [semanticCollect, Finset.mem_filter]
  constructor
  · exact And.left
  · intro retained
    refine ⟨retained, ?_⟩
    have guard := (Finset.mem_filter.mp retained).2
    unfold retainAfterSemanticPurge at guard ⊢
    rw [markerCoveredEntries_semanticCollect]
    exact guard

theorem Purge.valid_entry {marker : Purge} (valid : marker.Valid)
    {entry : Timestamp × Coordinate} (member : entry ∈ marker.covered) :
    entry.2 ∈ marker.coordinates ∧ entry.1 ≤ marker.cutoff := by
  unfold Purge.Valid Purge.validB at valid
  rw [fold_and_eq_true_iff] at valid
  simpa using valid entry member

theorem action_eq_purge_of_purge_some {e : Event} {marker : Purge}
    (h : purge? e = some marker) : e.action = .purge marker := by
  cases action : e.action <;> simp [purge?, action] at h
  simpa [action, h]

/-- Every reclaimed payload is masked by a retained, intrinsically valid
semantic marker. -/
theorem cellOverwritten_semanticCollect_of_covered_le {full : Finset Event}
    (valid : StateValid full) {candidate : Event} {update : CellUpdate}
    (isCell : cellUpdate? candidate = some update) {coveredTime : Timestamp}
    {coordinate : Coordinate}
    (covered : (coveredTime, coordinate) ∈
      markerCoveredEntries full) :
    (update.row, update.column) = coordinate → candidate.1 ≤ coveredTime →
    cellOverwritten (semanticCollect full) candidate = true := by
  intro sameCoordinate before
  rw [markerCoveredEntries, Finset.mem_biUnion] at covered
  obtain ⟨markerEvent, markerMember, entryMember⟩ := covered
  cases isMarker : purge? markerEvent with
  | none => simp [isMarker] at entryMember
  | some marker =>
      simp only [isMarker] at entryMember
      have retained := purge_retained markerMember isMarker
      have markerValid : marker.Valid := by
        have := valid markerEvent markerMember
        unfold metadataValidB at this
        have markerNoncell : cellUpdate? markerEvent = none := by
          unfold purge? at isMarker
          cases action : markerEvent.action <;>
            simp [action, cellUpdate?] at isMarker ⊢
        have markerNonrange : rangeUpdate? markerEvent = none := by
          unfold purge? at isMarker
          cases action : markerEvent.action <;>
            simp [action, rangeUpdate?] at isMarker ⊢
        simp only [markerNoncell, markerNonrange, isMarker] at this
        exact this
      have entryValid := Purge.valid_entry markerValid entryMember
      rw [cellOverwritten, fold_or_eq_true_iff]
      refine ⟨markerEvent, retained, ?_⟩
      have action := action_eq_purge_of_purge_some isMarker
      have targetBefore : candidate.1 ≤ marker.cutoff :=
        Nat.le_trans before entryValid.2
      simp [action, isCell, sameCoordinate, entryValid.1, targetBefore]

theorem cellOverwritten_semanticCollect_of_covered {full : Finset Event}
    (valid : StateValid full) {candidate : Event} {update : CellUpdate}
    (isCell : cellUpdate? candidate = some update)
    (covered : (candidate.1, (update.row, update.column)) ∈
      markerCoveredEntries full) :
    cellOverwritten (semanticCollect full) candidate = true := by
  exact cellOverwritten_semanticCollect_of_covered_le valid isCell covered rfl
    (Nat.le_refl _)

theorem cellOverwritten_full_of_covered {full : Finset Event}
    (valid : StateValid full) {candidate : Event} {update : CellUpdate}
    (isCell : cellUpdate? candidate = some update)
    (covered : (candidate.1, (update.row, update.column)) ∈
      markerCoveredEntries full) : cellOverwritten full candidate = true := by
  have compact := cellOverwritten_semanticCollect_of_covered valid isCell covered
  rw [cellOverwritten, fold_or_eq_true_iff] at compact ⊢
  obtain ⟨markerEvent, member, yes⟩ := compact
  exact ⟨markerEvent, semanticCollect_subset full member, yes⟩

theorem covered_of_not_retained {full : Finset Event} {e : Event}
    {update : CellUpdate} (member : e ∈ full)
    (isCell : cellUpdate? e = some update)
    (removed : e ∉ semanticCollect full) :
    (e.1, (update.row, update.column)) ∈ markerCoveredEntries full := by
  simp [semanticCollect, retainAfterSemanticPurge, member, isCell] at removed
  exact removed

theorem metadata_cell_overwrite {full : Finset Event}
    (valid : StateValid full) {later : Event} {update : CellUpdate}
    (member : later ∈ full) (isCell : cellUpdate? later = some update)
    {overwritten : Timestamp} (overwrites : overwritten ∈ update.overwrites) :
    overwritten < later.1 ∧ ∃ prior ∈ full,
      ∃ priorUpdate, cellUpdate? prior = some priorUpdate ∧
        prior.1 = overwritten ∧ priorUpdate.row = update.row ∧
        priorUpdate.column = update.column := by
  have metadata := valid later member
  unfold metadataValidB at metadata
  simp only [isCell] at metadata
  rw [fold_and_eq_true_iff] at metadata
  have one := metadata overwritten overwrites
  simp only [Bool.and_eq_true, decide_eq_true_eq] at one
  refine ⟨one.1, ?_⟩
  rw [fold_or_eq_true_iff] at one
  obtain ⟨prior, priorMember, priorValid⟩ := one.2
  cases priorCell : cellUpdate? prior with
  | none => simp [priorCell] at priorValid
  | some priorUpdate =>
      simp only [priorCell, decide_eq_true_eq] at priorValid
      exact ⟨prior, priorMember, priorUpdate, priorCell, priorValid⟩

theorem cellOverwritten_semanticCollect {full : Finset Event}
    (valid : StateValid full) (unique : TimestampUnique full)
    {candidate : Event} (member : candidate ∈ full) :
    cellOverwritten (semanticCollect full) candidate =
      cellOverwritten full candidate := by
  apply Bool.eq_iff_iff.mpr
  rw [cellOverwritten, fold_or_eq_true_iff,
    cellOverwritten, fold_or_eq_true_iff]
  constructor
  · rintro ⟨later, laterMember, yes⟩
    exact ⟨later, semanticCollect_subset full laterMember, yes⟩
  · rintro ⟨later, laterMember, yes⟩
    by_cases retained : later ∈ semanticCollect full
    · exact ⟨later, retained, yes⟩
    · have laterSome : (cellUpdate? later).isSome := by
        by_contra absent
        rw [Option.not_isSome_iff_eq_none] at absent
        exact retained (noncell_retained laterMember absent)
      obtain ⟨laterUpdate, laterCell⟩ := Option.isSome_iff_exists.mp laterSome
      have overwriteMember : candidate.1 ∈ laterUpdate.overwrites := by
        unfold cellUpdate? at laterCell
        cases action : later.action <;>
          simp [action] at laterCell yes
        subst_vars
        exact yes
      obtain ⟨before, prior, priorMember, priorUpdate, priorCell,
          priorTime, priorRow, priorColumn⟩ :=
        metadata_cell_overwrite valid laterMember laterCell overwriteMember
      have priorEq : prior = candidate :=
        unique prior priorMember candidate member priorTime
      subst prior
      have candidateCell : cellUpdate? candidate = some priorUpdate := priorCell
      have covered := covered_of_not_retained laterMember laterCell retained
      have masked := cellOverwritten_semanticCollect_of_covered_le valid
        candidateCell covered
        (by simp [priorRow, priorColumn]) (Nat.le_of_lt before)
      rw [cellOverwritten, fold_or_eq_true_iff] at masked
      exact masked

theorem rawCellValues_semanticCollect {full : Finset Event}
    (valid : StateValid full) (unique : TimestampUnique full)
    (row column : StableId) :
    rawCellValues (semanticCollect full) row column =
      rawCellValues full row column := by
  unfold rawCellValues
  apply Finset.ext
  intro value
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨event, ⟨member, active⟩, valueMember⟩
    have fullMember := semanticCollect_subset full member
    rw [cellOverwritten_semanticCollect valid unique fullMember] at active
    exact ⟨event, ⟨fullMember, active⟩, valueMember⟩
  · rintro ⟨event, ⟨member, active⟩, valueMember⟩
    have activeParts : cellMatches row column event = true ∧
        (!cellOverwritten full event) = true := by
      simpa only [Bool.and_eq_true] using active
    have matched := activeParts.1
    cases isCell : cellUpdate? event with
    | none => simp [cellMatches, isCell] at matched
    | some update =>
        have retained : event ∈ semanticCollect full := by
          by_contra removed
          have covered := covered_of_not_retained member isCell removed
          have overwritten := cellOverwritten_full_of_covered valid isCell covered
          have notOverwritten := activeParts.2
          simp [overwritten] at notOverwritten
        refine ⟨event, ⟨retained, ?_⟩, valueMember⟩
        rw [cellOverwritten_semanticCollect valid unique member]
        exact active

theorem cellValues_semanticCollect {full : Finset Event}
    (valid : StateValid full) (unique : TimestampUnique full)
    (row column : StableId) :
    cellValues (semanticCollect full) row column = cellValues full row column := by
  unfold cellValues
  rw [axisLive_semanticCollect, axisLive_semanticCollect]
  rw [rawCellValues_semanticCollect valid unique row column]

theorem view_semanticCollect {full : Finset Event}
    (valid : StateValid full) (unique : TimestampUnique full) :
    view (semanticCollect full) = view full := by
  have rowPositionEq :
      axisPositions (semanticCollect full) .row = axisPositions full .row := by
    funext id
    exact axisPositions_semanticCollect full .row id
  have columnPositionEq :
      axisPositions (semanticCollect full) .column =
        axisPositions full .column := by
    funext id
    exact axisPositions_semanticCollect full .column id
  have cellEq : cellValues (semanticCollect full) = cellValues full := by
    funext row column
    exact cellValues_semanticCollect valid unique row column
  have rangeEq : rangeValues (semanticCollect full) = rangeValues full := by
    funext id
    exact rangeValues_semanticCollect full id
  unfold view
  rw [liveAxisIds_semanticCollect, liveAxisIds_semanticCollect,
    rowPositionEq, columnPositionEq, cellEq, rangeEq]

theorem markerCoveredEntries_insert (events : Finset Event) (e : Event) :
    markerCoveredEntries (insert e events) =
      (match purge? e with | some marker => marker.covered | none => ∅) ∪
        markerCoveredEntries events := by
  unfold markerCoveredEntries
  simp [Finset.biUnion_insert]

theorem markerCoveredEntries_union (a b : Finset Event) :
    markerCoveredEntries (a ∪ b) =
      markerCoveredEntries a ∪ markerCoveredEntries b := by
  apply Finset.ext
  intro entry
  simp only [markerCoveredEntries, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨event, left | right, covered⟩
    · exact Or.inl ⟨event, left, covered⟩
    · exact Or.inr ⟨event, right, covered⟩
  · rintro (⟨event, member, covered⟩ | ⟨event, member, covered⟩)
    · exact ⟨event, Or.inl member, covered⟩
    · exact ⟨event, Or.inr member, covered⟩

theorem semanticCollect_insert_normalized (full : Finset Event) (e : Event) :
    semanticCollect (insert e (semanticCollect full)) =
      semanticCollect (insert e full) := by
  have coverage :
      markerCoveredEntries (insert e (semanticCollect full)) =
        markerCoveredEntries (insert e full) := by
    rw [markerCoveredEntries_insert, markerCoveredEntries_insert,
      markerCoveredEntries_semanticCollect]
  apply Finset.ext
  intro candidate
  have retentionEq :
      retainAfterSemanticPurge (insert e (semanticCollect full)) candidate =
        retainAfterSemanticPurge (insert e full) candidate := by
    unfold retainAfterSemanticPurge
    cases cellUpdate? candidate <;> simp [coverage]
  have retentionEq' :
      retainAfterSemanticPurge
          (insert e (full.filter fun event =>
            retainAfterSemanticPurge full event)) candidate =
        retainAfterSemanticPurge (insert e full) candidate := by
    simpa only [semanticCollect] using retentionEq
  simp only [semanticCollect, Finset.mem_filter, Finset.mem_insert]
  rw [retentionEq']
  constructor
  · rintro ⟨same | ⟨member, _⟩, retained⟩
    · exact ⟨Or.inl same, retained⟩
    · exact ⟨Or.inr member, retained⟩
  · rintro ⟨same | member, retained⟩
    · exact ⟨Or.inl same, retained⟩
    · refine ⟨Or.inr ?_, retained⟩
      cases isCell : cellUpdate? candidate with
      | none => exact ⟨member, by simp [retainAfterSemanticPurge, isCell]⟩
      | some update =>
          have unionNotCovered :
              (candidate.1, (update.row, update.column)) ∉
                markerCoveredEntries (insert e full) := by
            simpa only [retainAfterSemanticPurge, isCell, decide_eq_true_eq]
              using retained
          have notCovered :
              (candidate.1, (update.row, update.column)) ∉
                markerCoveredEntries full := by
            intro oldCovered
            apply unionNotCovered
            rw [markerCoveredEntries_insert]
            exact Finset.mem_union_right _ oldCovered
          exact ⟨member, by
            simp [retainAfterSemanticPurge, isCell, notCovered]⟩

theorem semanticCollect_union_normalized (a b : Finset Event) :
    semanticCollect (semanticCollect a ∪ semanticCollect b) =
      semanticCollect (a ∪ b) := by
  have coverage :
      markerCoveredEntries (semanticCollect a ∪ semanticCollect b) =
        markerCoveredEntries (a ∪ b) := by
    rw [markerCoveredEntries_union, markerCoveredEntries_union,
      markerCoveredEntries_semanticCollect,
      markerCoveredEntries_semanticCollect]
  apply Finset.ext
  intro candidate
  have retentionEq :
      retainAfterSemanticPurge
          (semanticCollect a ∪ semanticCollect b) candidate =
        retainAfterSemanticPurge (a ∪ b) candidate := by
    unfold retainAfterSemanticPurge
    cases cellUpdate? candidate <;> simp [coverage]
  have retentionEq' :
      retainAfterSemanticPurge
          ((a.filter fun event => retainAfterSemanticPurge a event) ∪
           (b.filter fun event => retainAfterSemanticPurge b event)) candidate =
        retainAfterSemanticPurge (a ∪ b) candidate := by
    simpa only [semanticCollect] using retentionEq
  simp only [semanticCollect, Finset.mem_filter, Finset.mem_union]
  rw [retentionEq']
  constructor
  · rintro ⟨⟨left, _⟩ | ⟨right, _⟩, retained⟩
    · exact ⟨Or.inl left, retained⟩
    · exact ⟨Or.inr right, retained⟩
  · rintro ⟨left | right, retained⟩
    · refine ⟨Or.inl ?_, retained⟩
      cases isCell : cellUpdate? candidate with
      | none => exact ⟨left, by simp [retainAfterSemanticPurge, isCell]⟩
      | some update =>
          have unionNotCovered :
              (candidate.1, (update.row, update.column)) ∉
                markerCoveredEntries (a ∪ b) := by
            simpa only [retainAfterSemanticPurge, isCell, decide_eq_true_eq]
              using retained
          have notCovered :
              (candidate.1, (update.row, update.column)) ∉
                markerCoveredEntries a := by
            intro oldCovered
            apply unionNotCovered
            rw [markerCoveredEntries_union]
            exact Finset.mem_union_left _ oldCovered
          exact ⟨left, by
            simp [retainAfterSemanticPurge, isCell, notCovered]⟩
    · refine ⟨Or.inr ?_, retained⟩
      cases isCell : cellUpdate? candidate with
      | none => exact ⟨right, by simp [retainAfterSemanticPurge, isCell]⟩
      | some update =>
          have unionNotCovered :
              (candidate.1, (update.row, update.column)) ∉
                markerCoveredEntries (a ∪ b) := by
            simpa only [retainAfterSemanticPurge, isCell, decide_eq_true_eq]
              using retained
          have notCovered :
              (candidate.1, (update.row, update.column)) ∉
                markerCoveredEntries b := by
            intro oldCovered
            apply unionNotCovered
            rw [markerCoveredEntries_union]
            exact Finset.mem_union_right _ oldCovered
          exact ⟨right, by
            simp [retainAfterSemanticPurge, isCell, notCovered]⟩

theorem applicable_fresh {events : Finset Event} {e : Event}
    (guard : applicable e events) : e.1 ∉ eventTimes events := by
  unfold applicable applicableB at guard
  simp only [Bool.and_eq_true] at guard
  have first := guard.1.1.1
  simpa using first

theorem applicable_metadataValid {events : Finset Event} {e : Event}
    (guard : applicable e events) : metadataValidB events e = true := by
  unfold applicable applicableB at guard
  simp only [Bool.and_eq_true] at guard
  exact guard.1.2

/-- The compact state is the event set with certified cell payloads removed.
The semantic marker remains an ordinary replicated event, so collection needs
no ghost tombstone set. -/
def Represents (compact full : Finset Event) : Prop :=
  compact = semanticCollect full ∧ StateValid full ∧ TimestampUnique full

def certificate : StateGCCertificate D generation where
  CompactState := Finset Event
  Evidence := Unit
  Represents := Represents
  EvidenceValid := fun _ _ _ => True
  Compatible := TimestampCompatible
  init := ∅
  collect := fun _ compact => semanticCollect compact
  update := fun compact op => semanticCollect (insert op compact)
  merge := fun _ a b => semanticCollect (a ∪ b)
  query := fun compact _ => view compact
  init_represents := by
    refine ⟨by rfl, ?_, timestampUnique_empty⟩
    · intro e member
      simp [D] at member
  collect_represents := by
    intro evidence compact full represented _
    rcases represented with ⟨rfl, valid, unique⟩
    exact ⟨semanticCollect_idempotent full, valid, unique⟩
  update_represents := by
    intro compact full op represented guard
    rcases represented with ⟨rfl, valid, unique⟩
    refine ⟨?_, stateValid_insert valid (applicable_metadataValid guard),
      timestampUnique_insert unique (applicable_fresh guard)⟩
    simpa [D] using semanticCollect_insert_normalized full op
  merge_represents := by
    intro cl ca cb l a b _ representedA representedB compatible
    rcases representedA with ⟨rfl, validA, uniqueA⟩
    rcases representedB with ⟨rfl, validB, uniqueB⟩
    refine ⟨?_, stateValid_union validA validB,
      timestampUnique_union uniqueA uniqueB compatible⟩
    simpa [D] using semanticCollect_union_normalized a b
  query_correct := by
    intro compact full represented query
    rcases represented with ⟨rfl, valid, unique⟩
    simpa [D] using view_semanticCollect valid unique

/-! ## Distributed frontier authorization

Fetching a remote commit supplies generic authored frontier evidence. The
purge action records exactly which configured replicas have such evidence;
the state collector itself then needs no network state. -/

noncomputable def frontierAcknowledgements (parents : Version → List Version)
    (author : Sal.MRDTs.GC.Author) (self : Replica)
    (holding : Sal.MRDTs.GC.Local) : Finset Replica :=
  by
    classical
    exact requiredRoster.filter fun replica =>
      replica = self ∨ ∃ version,
        version ∈ Sal.MRDTs.GC.DerivedEvidence parents author holding replica

theorem frontierAcknowledgements_complete (parents : Version → List Version)
    (author : Sal.MRDTs.GC.Author) (self : Replica)
    (holding : Sal.MRDTs.GC.Local)
    (complete : Sal.MRDTs.GC.EvidenceComplete parents author
      (↑requiredRoster : Set Replica) self holding) :
    requiredRoster ⊆ frontierAcknowledgements parents author self holding := by
  classical
  intro replica member
  rw [frontierAcknowledgements, Finset.mem_filter]
  exact ⟨member, complete replica (by simpa using member)⟩

noncomputable def markerFromFrontier
    (parents : Version → List Version) (author : Sal.MRDTs.GC.Author)
    (self : Replica) (holding : Sal.MRDTs.GC.Local)
    (cutoff : Timestamp) (coordinates : Finset Coordinate)
    (covered : Finset (Timestamp × Coordinate)) : Purge where
  cutoff := cutoff
  coordinates := coordinates
  covered := covered
  acknowledgements := frontierAcknowledgements parents author self holding

theorem markerFromFrontier_has_roster
    (parents : Version → List Version) (author : Sal.MRDTs.GC.Author)
    (self : Replica) (holding : Sal.MRDTs.GC.Local)
    (cutoff : Timestamp) (coordinates : Finset Coordinate)
    (covered : Finset (Timestamp × Coordinate))
    (complete : Sal.MRDTs.GC.EvidenceComplete parents author
      (↑requiredRoster : Set Replica) self holding) :
    requiredRoster ⊆ Purge.acknowledgements
      (markerFromFrontier parents author self holding cutoff coordinates covered) := by
  exact frontierAcknowledgements_complete parents author self holding complete

def deleted : Finset Event := insert concurrentRemove base
def collected : Finset Event := naiveCollect deleted

/-- Collection is currently invisible because the removed row hides its cell. -/
example : axisLive deleted .row r0 = false := by native_decide
example : axisLive collected .row r0 = false := by native_decide
example : cellValues deleted r0 c0 = ∅ := by native_decide
example : cellValues collected r0 c0 = ∅ := by native_decide

/-- A permitted selective undo later restores the row. The uncollected model
also restores its old cell, while the locally collected representation cannot.
This is the contextual counterexample. -/
def restoredFull : Finset Event := insert undoRemove deleted
def restoredCollected : Finset Event := insert undoRemove collected

example : axisLive restoredFull .row r0 = true := by native_decide
example : axisLive restoredCollected .row r0 = true := by native_decide
example : cellValues restoredFull r0 c0 = {0} := by native_decide
example : cellValues restoredCollected r0 c0 = ∅ := by native_decide

theorem naive_collection_changes_future_observation :
    cellValues restoredFull r0 c0 ≠ cellValues restoredCollected r0 c0 := by
  decide

/-- Evidence required by a future purge-marker implementation. `frontier`
comes from the generic distributed history collector; `coordinates` is the
finite set of cell keys whose old versions the marker permanently masks. -/
structure StablePurgeEvidence where
  cutoff : Timestamp
  frontier : Replica → Timestamp
  roster : Finset Replica
  coordinates : Finset (StableId × StableId)
  covered : Finset (Timestamp × Coordinate)
  complete : ∀ replica ∈ roster, cutoff ≤ frontier replica

/-- The negative result rules out promoting the naive filter to the framework
state-GC interface without a semantic purge marker or a no-revival premise. -/
def RequiresSemanticMarker : Prop :=
  ∃ continuation : Event,
    cellValues (insert continuation deleted) r0 c0 ≠
      cellValues (insert continuation collected) r0 c0

theorem requires_semantic_marker : RequiresSemanticMarker := by
  refine ⟨undoRemove, ?_⟩
  decide

/-! ## Semantic cutoff marker

The marker is a replicated action, not ghost collector evidence. It remains
after old cell versions are removed and masks matching pre-cutoff versions
that arrive from a stale branch.
-/

def marker : Event :=
  purgeEvent 7 0 {1, 2, 3, 4} 4 {(r0, c0)} {(3, (r0, c0))} requiredRoster

def markedFull : Finset Event := insert marker deleted
def markedCollected : Finset Event := semanticCollect markedFull
def markedRestoredFull : Finset Event := insert undoRemove markedFull
def markedRestoredCollected : Finset Event := insert undoRemove markedCollected

example : applicableB marker deleted = true := by native_decide
example : baseCell ∉ markedCollected := by native_decide
example : eventTimes markedCollected = eventTimes markedFull :=
  eventTimes_semanticCollect markedFull
example : axisKeepTimes markedCollected .row r0 =
    axisKeepTimes markedFull .row r0 := by native_decide
example : axisKeepTimes markedCollected .column c0 =
    axisKeepTimes markedFull .column c0 := by native_decide
example : cellValues markedRestoredFull r0 c0 = ∅ := by native_decide
example : cellValues markedRestoredCollected r0 c0 = ∅ := by native_decide

theorem marker_preserves_late_restore_fixture :
    cellValues markedRestoredFull r0 c0 =
      cellValues markedRestoredCollected r0 c0 := by
  decide

/-- A stale branch can reintroduce the reclaimed payload event, but the
replicated marker continues to mask it. -/
def staleMerged : Finset Event := insert baseCell markedCollected

example : cellValues staleMerged r0 c0 = cellValues markedFull r0 c0 := by
  native_decide

/-- A post-cutoff write is not masked. It can edit a row restored by a stale
undo while the old pre-cutoff contents remain collected. -/
def freshAfterMarker : Event :=
  cellEvent 8 2 {1, 2, 3, 4, 6, 7} r0 c0 ∅ {9} ∅

def continuedMarkedCollected : Finset Event :=
  insert freshAfterMarker markedRestoredCollected

example : applicableB freshAfterMarker markedRestoredCollected = true := by native_decide
example : cellValues continuedMarkedCollected r0 c0 = {9} := by native_decide

#print axioms naive_collection_changes_future_observation
#print axioms requires_semantic_marker
#print axioms eventTimes_semanticCollect
#print axioms semanticCollect_idempotent
#print axioms view_semanticCollect
#print axioms certificate
#print axioms markerFromFrontier_has_roster
#print axioms marker_preserves_late_restore_fixture

end Sal.MRDTs.Instances.AegisSheet.GC
