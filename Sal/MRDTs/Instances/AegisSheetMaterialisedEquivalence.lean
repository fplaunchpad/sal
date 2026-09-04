import Sal.MRDTs.Instances.AegisSheetMaterialised

/-!
# Observation equivalence of the materialised AegisSheet

`mview (canon E) = view E` for purge-free histories `E` of the union model:
the observation of the canonical materialised state of a history is the
union model's declarative view of that history. Each component is a
membership bridge between a Boolean fold of the union model and an
existential over entries of `canon`.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs.Foundation

/-! ## Boolean folds -/

theorem fold_or_eq_true_iff' {β : Type} [DecidableEq β] (s : Finset β) (f : β → Bool) :
    Finset.fold (· || ·) false f s = true ↔ ∃ x ∈ s, f x = true := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s fresh ih =>
      rw [Finset.fold_insert fresh]
      simp [ih]

theorem finsetNonemptyB_iff {β : Type} [DecidableEq β] (s : Finset β) :
    finsetNonemptyB s = true ↔ s.Nonempty := by
  unfold finsetNonemptyB
  rw [fold_or_eq_true_iff']
  constructor
  · rintro ⟨x, hx, _⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩

/-! ## Known identifiers -/

theorem mem_canonKnown {E : Finset Event} {axis : Axis} {id : StableId} :
    (axis, id) ∈ canonKnown E ↔ axisKnown E axis id = true := by
  unfold canonKnown axisKnown
  rw [fold_or_eq_true_iff', Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hk⟩
    refine ⟨e, he, ?_⟩
    cases h : axisUpdate? e with
    | none => rw [h] at hk; simp at hk
    | some u =>
      rw [h] at hk
      simp only [Finset.mem_singleton, Prod.mk.injEq] at hk
      simp [hk.1, hk.2]
  · rintro ⟨e, he, hk⟩
    refine ⟨e, he, ?_⟩
    cases h : axisUpdate? e with
    | none => rw [h] at hk; simp at hk
    | some u =>
      rw [h] at hk
      simp only [decide_eq_true_eq] at hk
      simp [hk.1, hk.2]

theorem mem_axisIds {E : Finset Event} {axis : Axis} {id : StableId} :
    id ∈ axisIds E axis ↔ axisKnown E axis id = true := by
  unfold axisIds axisKnown
  rw [fold_or_eq_true_iff', Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hk⟩
    refine ⟨e, he, ?_⟩
    cases h : axisUpdate? e with
    | none => rw [h] at hk; simp at hk
    | some u =>
      rw [h] at hk
      by_cases ha : u.axis = axis
      · simp only [ha, if_true, Finset.mem_singleton] at hk
        simp [ha, hk]
      · simp [ha] at hk
  · rintro ⟨e, he, hk⟩
    refine ⟨e, he, ?_⟩
    cases h : axisUpdate? e with
    | none => rw [h] at hk; simp at hk
    | some u =>
      rw [h] at hk
      simp only [decide_eq_true_eq] at hk
      simp [hk.1, hk.2]

theorem axisKeys_of_known {E : Finset Event} {axis : Axis} {id : StableId}
    (h : axisKnown E axis id = true) : (axis, id) ∈ axisKeys E := by
  rw [← mem_canonKnown] at h
  unfold canonKnown at h
  unfold axisKeys
  rw [Finset.mem_biUnion] at h ⊢
  obtain ⟨e, he, hk⟩ := h
  refine ⟨e, he, ?_⟩
  cases ha : axisUpdate? e with
  | none => rw [ha] at hk; simp at hk
  | some u =>
    rw [ha] at hk
    unfold axisUpdate? at ha
    cases hact : e.action with
    | axis v =>
      rw [hact] at ha
      simp only [Option.some.injEq] at ha
      subst ha
      simpa using hk
    | cell _ => rw [hact] at ha; simp at ha
    | range _ => rw [hact] at ha; simp at ha
    | purge _ => rw [hact] at ha; simp at ha

/-! ## Tokens and liveness -/

theorem mem_canonTokens {E : Finset Event} {x : TokenEntry} :
    x ∈ canonTokens E ↔ (x.1, x.2.1) ∈ axisKeys E ∧ x.2.2 ∈ liveAxisTokens E x.1 x.2.1 := by
  unfold canonTokens
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [Finset.mem_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨hk, ht⟩
  · rintro ⟨hk, ht⟩
    refine ⟨(x.1, x.2.1), hk, ?_⟩
    rw [Finset.mem_image]
    exact ⟨x.2.2, ht, rfl⟩

theorem mLive_canon (E : Finset Event) (axis : Axis) (id : StableId) :
    mLive (canon E) axis id = axisLive E axis id := by
  apply Bool.eq_iff_iff.mpr
  unfold mLive axisLive
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  show ((axis, id) ∈ canonKnown E ∧ ∃ x ∈ canonTokens E, x.1 = axis ∧ x.2.1 = id) ↔
    axisKnown E axis id = true ∧ finsetNonemptyB (liveAxisTokens E axis id) = true
  rw [mem_canonKnown, finsetNonemptyB_iff]
  constructor
  · rintro ⟨hk, x, hx, h1, h2⟩
    refine ⟨hk, ?_⟩
    rw [mem_canonTokens] at hx
    rw [h1, h2] at hx
    exact ⟨x.2.2, hx.2⟩
  · rintro ⟨hk, t, ht⟩
    refine ⟨hk, (axis, id, t), ?_, rfl, rfl⟩
    rw [mem_canonTokens]
    exact ⟨axisKeys_of_known hk, ht⟩

theorem mLiveIds_canon (E : Finset Event) (axis : Axis) :
    mLiveIds (canon E) axis = liveAxisIds E axis := by
  ext id
  unfold mLiveIds liveAxisIds
  rw [Finset.mem_image, Finset.mem_filter, mem_axisIds]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_filter] at hk
    obtain ⟨hkK, hka, hl⟩ := hk
    have hk' : k = (axis, k.2) := by
      rcases k with ⟨a, i⟩; simp only at hka; rw [hka]
    rw [hk'] at hkK
    rw [mLive_canon] at hl
    exact ⟨mem_canonKnown.mp hkK, hl⟩
  · rintro ⟨hk, hl⟩
    refine ⟨(axis, id), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨mem_canonKnown.mpr hk, rfl, ?_⟩
    rw [mLive_canon]; exact hl

theorem canon_pos (E : Finset Event) : (canon E).pos = canonPos E := rfl
theorem canon_cells (E : Finset Event) : (canon E).cells = canonCells E := rfl
theorem canon_ranges (E : Finset Event) : (canon E).ranges = canonRanges E := rfl

/-! ## Positions -/

theorem axisCandidate_iff {axis : Axis} {id : StableId} {e : Event} :
    axisCandidate axis id e = true ↔
      ∃ u, axisUpdate? e = some u ∧ u.axis = axis ∧ u.id = id ∧ u.after.isSome = true := by
  unfold axisCandidate
  cases h : axisUpdate? e with
  | none => simp
  | some u => simp

theorem mem_canonPos {E : Finset Event} {x : PosEntry} :
    x ∈ canonPos E ↔ ∃ e ∈ E, ∃ u, axisUpdate? e = some u ∧ ∃ p, u.after = some p ∧
      laterAxisCandidate E u.axis u.id e = false ∧ x = (u.axis, u.id, e.1, p) := by
  unfold canonPos
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hx⟩
    refine ⟨e, he, ?_⟩
    cases hu : axisUpdate? e with
    | none => simp [hu] at hx
    | some u =>
      simp only [hu] at hx
      refine ⟨u, rfl, ?_⟩
      cases ha : u.after with
      | none => simp [ha] at hx
      | some p =>
        simp only [ha] at hx
        by_cases hl : laterAxisCandidate E u.axis u.id e = true
        · simp [hl] at hx
        · have hl' : laterAxisCandidate E u.axis u.id e = false := by simpa using hl
          simp only [hl', Bool.false_eq_true, if_false, Finset.mem_singleton] at hx
          exact ⟨p, rfl, hl', hx⟩
  · rintro ⟨e, he, u, hu, p, ha, hl, rfl⟩
    refine ⟨e, he, ?_⟩
    simp [hu, ha, hl]

theorem mPositions_canon (E : Finset Event) (axis : Axis) (id : StableId) :
    mPositions (canon E) axis id = axisPositions E axis id := by
  ext p
  unfold mPositions axisPositions
  rw [Finset.mem_image, Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [canon_pos, Finset.mem_filter] at hx
    obtain ⟨hx, hk⟩ := hx
    rw [mem_canonPos] at hx
    obtain ⟨e, he, u, hu, q, ha, hl, rfl⟩ := hx
    simp only [posKey, Prod.mk.injEq] at hk
    refine ⟨e, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨he, ?_⟩
      rw [Bool.and_eq_true, Bool.not_eq_true']
      rw [hk.1, hk.2] at hl
      refine ⟨?_, hl⟩
      rw [axisCandidate_iff]
      exact ⟨u, hu, hk.1, hk.2, by rw [ha]; rfl⟩
    · simp [hu, ha, posVal]
  · rintro ⟨e, he, hp⟩
    rw [Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true', axisCandidate_iff] at he
    obtain ⟨he, ⟨u, hu, hax, hid, _⟩, hl⟩ := he
    simp only [hu] at hp
    cases ha : u.after with
    | none => simp [ha] at hp
    | some q =>
      simp only [ha, Finset.mem_singleton] at hp
      subst hp
      refine ⟨(u.axis, u.id, e.1, p), ?_, rfl⟩
      rw [canon_pos, Finset.mem_filter, mem_canonPos]
      refine ⟨⟨e, he, u, hu, p, ha, by rw [hax, hid]; exact hl, rfl⟩, ?_⟩
      simp [posKey, hax, hid]

/-! ## Cells -/

theorem cellOverwrittenD2_eq_of_purgeFree {E : Finset Event}
    (hp : ∀ e ∈ E, purge? e = none) (cand : Event) :
    cellOverwrittenD2 E cand = cellOverwritten E cand := by
  unfold cellOverwrittenD2 cellOverwritten
  apply Finset.fold_congr
  intro later hl
  have hpl := hp later hl
  unfold purge? at hpl
  cases h : later.action with
  | purge m => rw [h] at hpl; simp at hpl
  | axis _ => rfl
  | cell _ => rfl
  | range _ => rfl

theorem mem_canonCells {E : Finset Event} {x : CellEntry} :
    x ∈ canonCells E ↔ ∃ e ∈ E, ∃ u, cellUpdate? e = some u ∧
      cellOverwrittenD2 E e = false ∧ x = (u.row, u.column, e.1, u.after) := by
  unfold canonCells
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hx⟩
    refine ⟨e, he, ?_⟩
    cases hu : cellUpdate? e with
    | none => simp [hu] at hx
    | some u =>
      simp only [hu] at hx
      by_cases ho : cellOverwrittenD2 E e = true
      · simp [ho] at hx
      · have ho' : cellOverwrittenD2 E e = false := by simpa using ho
        simp only [ho', Bool.false_eq_true, if_false, Finset.mem_singleton] at hx
        exact ⟨u, rfl, ho', hx⟩
  · rintro ⟨e, he, u, hu, ho, rfl⟩
    refine ⟨e, he, ?_⟩
    simp [hu, ho]

theorem cellMatches_iff {row column : StableId} {e : Event} :
    cellMatches row column e = true ↔
      ∃ u, cellUpdate? e = some u ∧ u.row = row ∧ u.column = column := by
  unfold cellMatches
  cases h : cellUpdate? e with
  | none => simp
  | some u => simp

theorem mCellValues_canon {E : Finset Event} (hp : ∀ e ∈ E, purge? e = none)
    (row column : StableId) :
    mCellValues (canon E) row column = cellValues E row column := by
  unfold mCellValues cellValues
  rw [mLive_canon, mLive_canon]
  split_ifs with h
  · ext v
    unfold rawCellValues
    rw [Finset.mem_biUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, hv⟩
      rw [canon_cells, Finset.mem_filter, mem_canonCells] at hx
      obtain ⟨⟨e, he, u, hu, ho, rfl⟩, hr, hc⟩ := hx
      simp only at hr hc hv
      refine ⟨e, ?_, ?_⟩
      · rw [Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
          ← cellOverwrittenD2_eq_of_purgeFree hp, cellMatches_iff]
        exact ⟨he, ⟨u, hu, hr, hc⟩, ho⟩
      · simp only [hu]; exact hv
    · rintro ⟨e, he, hv⟩
      rw [Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
        ← cellOverwrittenD2_eq_of_purgeFree hp, cellMatches_iff] at he
      obtain ⟨he, ⟨u, hu, hr, hc⟩, ho⟩ := he
      simp only [hu] at hv
      refine ⟨(u.row, u.column, e.1, u.after), ?_, hv⟩
      rw [canon_cells, Finset.mem_filter, mem_canonCells]
      exact ⟨⟨e, he, u, hu, ho, rfl⟩, hr, hc⟩
  · rfl

/-! ## Ranges -/

theorem mem_canonRanges {E : Finset Event} {x : RangeEntry} :
    x ∈ canonRanges E ↔ ∃ e ∈ E, ∃ u, rangeUpdate? e = some u ∧
      rangeOverwritten E e = false ∧ x = (u.id, e.1, u.after) := by
  unfold canonRanges
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hx⟩
    refine ⟨e, he, ?_⟩
    cases hu : rangeUpdate? e with
    | none => simp [hu] at hx
    | some u =>
      simp only [hu] at hx
      by_cases ho : rangeOverwritten E e = true
      · simp [ho] at hx
      · have ho' : rangeOverwritten E e = false := by simpa using ho
        simp only [ho', Bool.false_eq_true, if_false, Finset.mem_singleton] at hx
        exact ⟨u, rfl, ho', hx⟩
  · rintro ⟨e, he, u, hu, ho, rfl⟩
    refine ⟨e, he, ?_⟩
    simp [hu, ho]

theorem rangeMatches_iff {id : RangeId} {e : Event} :
    rangeMatches id e = true ↔ ∃ u, rangeUpdate? e = some u ∧ u.id = id := by
  unfold rangeMatches
  cases h : rangeUpdate? e with
  | none => simp
  | some u => simp

theorem mRangeValues_canon (E : Finset Event) (id : RangeId) :
    mRangeValues (canon E) id = rangeValues E id := by
  ext spec
  unfold mRangeValues rangeValues
  rw [Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx, hs⟩
    rw [canon_ranges, Finset.mem_filter, mem_canonRanges] at hx
    obtain ⟨⟨e, he, u, hu, ho, rfl⟩, hid⟩ := hx
    simp only at hid hs
    refine ⟨e, ?_, ?_⟩
    · rw [Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true', rangeMatches_iff]
      exact ⟨he, ⟨u, hu, hid⟩, ho⟩
    · simp only [hu]; exact hs
  · rintro ⟨e, he, hs⟩
    rw [Finset.mem_filter, Bool.and_eq_true, Bool.not_eq_true', rangeMatches_iff] at he
    obtain ⟨he, ⟨u, hu, hid⟩, ho⟩ := he
    simp only [hu] at hs
    refine ⟨(u.id, e.1, u.after), ?_, hs⟩
    rw [canon_ranges, Finset.mem_filter, mem_canonRanges]
    exact ⟨⟨e, he, u, hu, ho, rfl⟩, hid⟩

/-! ## The equivalence -/

theorem view_ext {a b : View} (rows : a.rows = b.rows) (columns : a.columns = b.columns)
    (rowPosition : a.rowPosition = b.rowPosition)
    (columnPosition : a.columnPosition = b.columnPosition)
    (cell : a.cell = b.cell) (range : a.range = b.range) : a = b := by
  cases a; cases b
  simp only at rows columns rowPosition columnPosition cell range
  subst rows columns rowPosition columnPosition cell range
  rfl

/-- **Observation equivalence on purge-free histories.** -/
theorem observationEquivalence : ObservationEquivalence := by
  intro E hp
  apply view_ext
  · exact mLiveIds_canon E .row
  · exact mLiveIds_canon E .column
  · funext id; exact mPositions_canon E .row id
  · funext id; exact mPositions_canon E .column id
  · funext row column; exact mCellValues_canon hp row column
  · funext id; exact mRangeValues_canon E id

#print axioms observationEquivalence

end Sal.MRDTs.Instances.AegisSheet.Materialised
