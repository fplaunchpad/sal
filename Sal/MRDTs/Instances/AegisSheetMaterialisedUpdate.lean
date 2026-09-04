import Sal.MRDTs.Instances.AegisSheetMaterialisedEquivalence
import Sal.MRDTs.Instances.AegisSheetMaterialisedJoin

/-!
# Update preservation for the materialised AegisSheet

An honest update of the union model commutes with the canonical state:
`mupdate (canon E) (toM E e) = canon (insert e E)` whenever `e` is applicable
at `E` and `E` satisfies the invariants the union model maintains along honest
executions (seen sets within the history's timestamps, unique timestamps,
valid metadata). Without those invariants the statement is false: a removal
whose `seen` set names a fresh timestamp would kill a token the materialised
update adds, and an overwrite list naming a timestamp at another coordinate
would mask a version the materialised update keeps.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs.Foundation

/-! ## Clauses of applicability -/

theorem MEvent.action_toM (E : Finset Event) (e : Event) :
    MEvent.action (toM E e) = e.action := rfl

theorem applicable_fresh {e : Event} {E : Finset Event} (h : applicable e E) :
    e.1 ∉ eventTimes E := by
  obtain ⟨hb, _⟩ := h
  unfold applicableB at hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hb
  exact hb.1.1.1

theorem applicable_seen {e : Event} {E : Finset Event} (h : applicable e E) :
    e.seen = eventTimes E := by
  obtain ⟨hb, _⟩ := h
  unfold applicableB at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb.1.1.2

theorem applicable_lt {e : Event} {E : Finset Event} (h : applicable e E) :
    ∀ t ∈ eventTimes E, t < e.1 :=
  h.2.lt

theorem applicable_not_mem {e : Event} {E : Finset Event} (h : applicable e E) : e ∉ E := by
  intro he
  exact applicable_fresh h (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he))

theorem mem_eventTimes_of_mem {E : Finset Event} {a : Event} (ha : a ∈ E) :
    a.1 ∈ eventTimes E :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)

/-! ## The `known` component -/

theorem canonKnown_insert (E : Finset Event) (e : Event) (he : e ∉ E) :
    canonKnown (insert e E) = canonKnown E ∪ (knownAdds (toM E e)).toFinset := by
  unfold canonKnown
  rw [Finset.biUnion_insert, Finset.union_comm]
  congr 1
  unfold knownAdds axisUpdate?
  rw [MEvent.action_toM]
  cases e.action <;> simp

theorem known_preserved {E : Finset Event} {e : Event} (h : applicable e E) :
    (mupdate (canon E) (toM E e)).known = canonKnown (insert e E) := by
  rw [known_step, canonKnown_insert E e (applicable_not_mem h)]
  rfl

/-! ## The position register -/

theorem laterAxisCandidate_insert (E : Finset Event) (e : Event) (he : e ∉ E)
    (axis : Axis) (id : StableId) (c : Event) :
    laterAxisCandidate (insert e E) axis id c =
      (laterAxisCandidate E axis id c || (axisCandidate axis id e && decide (c.1 < e.1))) := by
  unfold laterAxisCandidate
  rw [Finset.fold_insert he, Bool.or_comm]

/-- No element of `E` is a later candidate than a fresh clocked event. -/
theorem not_later_of_clocked {E : Finset Event} {e : Event} (h : applicable e E)
    (axis : Axis) (id : StableId) :
    laterAxisCandidate E axis id e = false := by
  unfold laterAxisCandidate
  rw [Bool.eq_false_iff]
  intro hf
  rw [fold_or_eq_true_iff'] at hf
  obtain ⟨l, hl, hc⟩ := hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact absurd (applicable_lt h l.1 (mem_eventTimes_of_mem hl)) (not_lt.mpr (le_of_lt hc.2))

theorem posCand_toM (E : Finset Event) (e : Event) :
    posCand (toM E e) = match axisUpdate? e with
      | some u => match u.after with
          | some p => some (u.axis, u.id, e.1, p)
          | none => none
      | none => none := by
  unfold posCand axisUpdate?
  rw [MEvent.action_toM]
  cases e.action <;> rfl

theorem pos_preserved {E : Finset Event} {e : Event} (h : applicable e E) :
    (mupdate (canon E) (toM E e)).pos = canonPos (insert e E) := by
  have he : e ∉ E := applicable_not_mem h
  rw [pos_step, posCand_toM, canon_pos]
  cases hu : axisUpdate? e with
  | none =>
    dsimp only
    have hnc : ∀ axis id, axisCandidate axis id e = false := by
      intro axis id; simp [axisCandidate, hu]
    ext x
    rw [mem_canonPos, mem_canonPos]
    constructor
    · rintro ⟨c, hc, u, hcu, p, hp, hl, rfl⟩
      refine ⟨c, Finset.mem_insert_of_mem hc, u, hcu, p, hp, ?_, rfl⟩
      simp [laterAxisCandidate_insert E e he, hl, hnc]
    · rintro ⟨c, hc, u, hcu, p, hp, hl, rfl⟩
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · rw [hu] at hcu; cases hcu
      · refine ⟨c, hc, u, hcu, p, hp, ?_, rfl⟩
        rw [laterAxisCandidate_insert E e he] at hl
        exact (Bool.or_eq_false_iff.mp hl).1
  | some u =>
    cases ha : u.after with
    | none =>
      simp only [ha]
      have hnc : ∀ axis id, axisCandidate axis id e = false := by
        intro axis id; simp [axisCandidate, hu, ha]
      ext x
      rw [mem_canonPos, mem_canonPos]
      constructor
      · rintro ⟨c, hc, v, hcv, p, hp, hl, rfl⟩
        refine ⟨c, Finset.mem_insert_of_mem hc, v, hcv, p, hp, ?_, rfl⟩
        simp [laterAxisCandidate_insert E e he, hl, hnc]
      · rintro ⟨c, hc, v, hcv, p, hp, hl, rfl⟩
        rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · rw [hu] at hcv
          cases hcv
          rw [ha] at hp; cases hp
        · refine ⟨c, hc, v, hcv, p, hp, ?_, rfl⟩
          rw [laterAxisCandidate_insert E e he] at hl
          exact (Bool.or_eq_false_iff.mp hl).1
    | some p =>
      simp only [ha]
      have hcand : axisCandidate u.axis u.id e = true := by
        simp [axisCandidate, hu, ha]
      have hnolater : ¬ ∃ x ∈ canonPos E, posKey x = (u.axis, u.id) ∧ e.1 < posTs x := by
        rintro ⟨x, hx, _, hlt⟩
        rw [mem_canonPos] at hx
        obtain ⟨c, hc, v, hcv, q, hq, _, rfl⟩ := hx
        exact absurd (applicable_lt h c.1 (mem_eventTimes_of_mem hc)) (not_lt.mpr (le_of_lt hlt))
      unfold posInsert
      split
      next hc => exact absurd hc hnolater
      next hc =>
        ext x
        rw [Finset.mem_insert, Finset.mem_filter, mem_canonPos, mem_canonPos]
        constructor
        · rintro (rfl | ⟨⟨c, hc, v, hcv, q, hq, hl, rfl⟩, hk⟩)
          · refine ⟨e, Finset.mem_insert_self e E, u, hu, p, ha, ?_, rfl⟩
            rw [laterAxisCandidate_insert E e he, not_later_of_clocked h]
            simp
          · refine ⟨c, Finset.mem_insert_of_mem hc, v, hcv, q, hq, ?_, rfl⟩
            simp only [posKey, ne_eq, Prod.mk.injEq] at hk
            have hnc : axisCandidate v.axis v.id e = false := by
              simp only [axisCandidate, hu, decide_eq_false_iff_not, not_and]
              intro h1 h2; exact absurd ⟨h1.symm, h2.symm⟩ hk
            simp [laterAxisCandidate_insert E e he, hl, hnc]
        · rintro ⟨c, hc, v, hcv, q, hq, hl, rfl⟩
          rw [Finset.mem_insert] at hc
          rcases hc with rfl | hc
          · left
            rw [hu] at hcv; cases hcv
            rw [ha] at hq; cases hq
            rfl
          · right
            rw [laterAxisCandidate_insert E e he] at hl
            have hl' := Bool.or_eq_false_iff.mp hl
            refine ⟨⟨c, hc, v, hcv, q, hq, hl'.1, rfl⟩, ?_⟩
            simp only [posKey, ne_eq, Prod.mk.injEq]
            rintro ⟨h1, h2⟩
            have hcand' : axisCandidate v.axis v.id e = true := by rw [h1, h2]; exact hcand
            have := hl'.2
            rw [hcand', Bool.true_and, decide_eq_false_iff_not, not_lt] at this
            exact absurd (applicable_lt h c.1 (mem_eventTimes_of_mem hc)) (not_lt.mpr this)

/-! ## Metadata validity -/

theorem fold_and_eq_true_iff' {β : Type} [DecidableEq β] (s : Finset β) (f : β → Bool) :
    Finset.fold (· && ·) true f s = true ↔ ∀ x ∈ s, f x = true := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s fresh ih =>
      rw [Finset.fold_insert fresh]
      simp [ih]

theorem cellUpdate?_eq_some {e : Event} {u : CellUpdate} :
    cellUpdate? e = some u ↔ e.action = .cell u := by
  unfold cellUpdate?; cases e.action <;> simp

theorem rangeUpdate?_eq_some {e : Event} {u : RangeUpdate} :
    rangeUpdate? e = some u ↔ e.action = .range u := by
  unfold rangeUpdate?; cases e.action <;> simp

theorem applicable_valid {e : Event} {E : Finset Event} (h : applicable e E) :
    metadataValidB E e = true := by
  obtain ⟨hb, _⟩ := h
  unfold applicableB at hb
  simp only [Bool.and_eq_true] at hb
  exact hb.1.2

theorem metadataValid_cell {E : Finset Event} {r : Event} {u : CellUpdate}
    (hu : r.action = .cell u) (hv : metadataValidB E r = true) :
    ∀ t ∈ u.overwrites, t < r.1 ∧ ∃ prior ∈ E, ∃ w : CellUpdate,
      prior.action = .cell w ∧ prior.1 = t ∧ w.row = u.row ∧ w.column = u.column := by
  unfold metadataValidB at hv
  have hcu : cellUpdate? r = some u := cellUpdate?_eq_some.mpr hu
  simp only [hcu] at hv
  rw [fold_and_eq_true_iff'] at hv
  intro t ht
  have := hv t ht
  rw [Bool.and_eq_true, decide_eq_true_eq, fold_or_eq_true_iff'] at this
  obtain ⟨hlt, prior, hp, hpr⟩ := this
  refine ⟨hlt, prior, hp, ?_⟩
  cases hw : cellUpdate? prior with
  | none => rw [hw] at hpr; simp at hpr
  | some w =>
    rw [hw] at hpr
    simp only [decide_eq_true_eq] at hpr
    exact ⟨w, cellUpdate?_eq_some.mp hw, hpr.1, hpr.2.1, hpr.2.2⟩

theorem metadataValid_range {E : Finset Event} {r : Event} {u : RangeUpdate}
    (hu : r.action = .range u) (hv : metadataValidB E r = true) :
    ∀ t ∈ u.overwrites, t < r.1 ∧ ∃ prior ∈ E, ∃ w : RangeUpdate,
      prior.action = .range w ∧ prior.1 = t ∧ w.id = u.id := by
  unfold metadataValidB at hv
  have h1 : cellUpdate? r = none := by simp [cellUpdate?, hu]
  have h2 : rangeUpdate? r = some u := rangeUpdate?_eq_some.mpr hu
  simp only [h1, h2] at hv
  rw [fold_and_eq_true_iff'] at hv
  intro t ht
  have := hv t ht
  rw [Bool.and_eq_true, decide_eq_true_eq, fold_or_eq_true_iff'] at this
  obtain ⟨hlt, prior, hp, hpr⟩ := this
  refine ⟨hlt, prior, hp, ?_⟩
  cases hw : rangeUpdate? prior with
  | none => rw [hw] at hpr; simp at hpr
  | some w =>
    rw [hw] at hpr
    simp only [decide_eq_true_eq] at hpr
    exact ⟨w, rangeUpdate?_eq_some.mp hw, hpr.1, hpr.2⟩

/-! ## Ranges -/

theorem rangeOverwritten_insert (E : Finset Event) (e : Event) (he : e ∉ E) (c : Event) :
    rangeOverwritten (insert e E) c = (rangeOverwritten E c ||
      match rangeUpdate? e with
      | some u => decide (c.1 ∈ u.overwrites)
      | none => false) := by
  unfold rangeOverwritten
  rw [Finset.fold_insert he]
  exact Bool.or_comm _ _

/-- A fresh range event is not overwritten by any event of an honest history. -/
theorem not_rangeOverwritten_fresh {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) : rangeOverwritten E e = false := by
  unfold rangeOverwritten
  rw [Bool.eq_false_iff]
  intro hf
  rw [fold_or_eq_true_iff'] at hf
  obtain ⟨later, hl, hlo⟩ := hf
  cases hw : rangeUpdate? later with
  | none => rw [hw] at hlo; simp at hlo
  | some w =>
    rw [hw] at hlo
    simp only [decide_eq_true_eq] at hlo
    obtain ⟨_, prior, hp, _, _, hpt, _⟩ :=
      metadataValid_range (rangeUpdate?_eq_some.mp hw) (hH.valid later hl) e.1 hlo
    exact applicable_fresh h (hpt ▸ mem_eventTimes_of_mem hp)

theorem canonRanges_insert_nonrange (E : Finset Event) (e : Event) (he : e ∉ E)
    (hn : rangeUpdate? e = none) : canonRanges (insert e E) = canonRanges E := by
  ext x
  rw [mem_canonRanges, mem_canonRanges]
  constructor
  · rintro ⟨c, hc, w, hcw, ho, rfl⟩
    rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · rw [hn] at hcw; cases hcw
    · refine ⟨c, hc, w, hcw, ?_, rfl⟩
      rw [rangeOverwritten_insert E e he] at ho
      exact (Bool.or_eq_false_iff.mp ho).1
  · rintro ⟨c, hc, w, hcw, ho, rfl⟩
    refine ⟨c, Finset.mem_insert_of_mem hc, w, hcw, ?_, rfl⟩
    rw [rangeOverwritten_insert E e he, ho, hn]
    rfl

theorem ranges_preserved {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) :
    (mupdate (canon E) (toM E e)).ranges = canonRanges (insert e E) := by
  have he := applicable_not_mem h
  rw [ranges_step, canon_ranges]
  cases hu : e.action with
  | range u =>
    have hru : rangeUpdate? e = some u := rangeUpdate?_eq_some.mpr hu
    have hvalid_e := metadataValid_range hu (applicable_valid h)
    ext x
    simp only [NR.step, rangeNR, rangeRemoves, rangeAdds, MEvent.action_toM, hu,
      Finset.mem_union, Finset.mem_filter, List.mem_toFinset, List.mem_singleton,
      decide_eq_false_iff_not, mem_canonRanges]
    constructor
    · rintro (⟨⟨c, hc, w, hcw, ho, rfl⟩, hnr⟩ | rfl)
      · refine ⟨c, Finset.mem_insert_of_mem hc, w, hcw, ?_, rfl⟩
        rw [rangeOverwritten_insert E e he, ho, hru]
        simp only [Bool.false_or, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨_, prior, hp, w', hpw', hpt, hid⟩ := hvalid_e c.1 hmem
        have hpc : prior = c := hH.ts_unique prior hp c hc hpt
        subst hpc
        have hww : w' = w := Action.range.inj ((rangeUpdate?_eq_some.mp hcw).symm.trans hpw').symm
        subst hww
        exact hnr ⟨hid, hmem⟩
      · refine ⟨e, Finset.mem_insert_self e E, u, hru, ?_, rfl⟩
        rw [rangeOverwritten_insert E e he, not_rangeOverwritten_fresh hH h, hru]
        simp only [Bool.false_or, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨_, prior, hp, _, _, hpt, _⟩ := hvalid_e e.1 hmem
        exact applicable_fresh h (hpt ▸ mem_eventTimes_of_mem hp)
    · rintro ⟨c, hc, w, hcw, ho, rfl⟩
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · right
        have hwu : w = u := Action.range.inj ((rangeUpdate?_eq_some.mp hcw).symm.trans hu)
        subst hwu; rfl
      · left
        rw [rangeOverwritten_insert E e he, hru] at ho
        have ho' := Bool.or_eq_false_iff.mp ho
        refine ⟨⟨c, hc, w, hcw, ho'.1, rfl⟩, ?_⟩
        rintro ⟨_, hmem⟩
        have := ho'.2
        rw [decide_eq_false_iff_not] at this
        exact this hmem
  | axis u =>
    have hn : rangeUpdate? e = none := by simp [rangeUpdate?, hu]
    rw [canonRanges_insert_nonrange E e he hn]
    simp [NR.step, rangeNR, rangeRemoves, rangeAdds, MEvent.action_toM, hu]
  | cell u =>
    have hn : rangeUpdate? e = none := by simp [rangeUpdate?, hu]
    rw [canonRanges_insert_nonrange E e he hn]
    simp [NR.step, rangeNR, rangeRemoves, rangeAdds, MEvent.action_toM, hu]
  | purge m =>
    have hn : rangeUpdate? e = none := by simp [rangeUpdate?, hu]
    rw [canonRanges_insert_nonrange E e he hn]
    simp [NR.step, rangeNR, rangeRemoves, rangeAdds, MEvent.action_toM, hu]

/-! ## Cells -/

theorem cellOverwrittenD2_insert (E : Finset Event) (e : Event) (he : e ∉ E) (c : Event) :
    cellOverwrittenD2 (insert e E) c = (cellOverwrittenD2 E c ||
      match e.action with
      | .cell u => decide (c.1 ∈ u.overwrites)
      | .purge m => match cellUpdate? c with
          | some update => decide ((c.1, (update.row, update.column)) ∈ m.covered)
          | none => false
      | _ => false) := by
  unfold cellOverwrittenD2
  rw [Finset.fold_insert he]
  exact Bool.or_comm _ _

theorem covered_time_mem_eventTimes {E : Finset Event} {r : Event} {m : Purge}
    (hr : r ∈ E) (hm : r.action = .purge m) {entry : Timestamp × Coordinate}
    (hentry : entry ∈ m.covered) : entry.1 ∈ eventTimes E := by
  unfold eventTimes
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  refine ⟨r, hr, ?_⟩
  have hp : purge? r = some m := by simp [purge?, hm]
  rw [hp]
  exact Finset.mem_image_of_mem _ hentry

/-- A fresh cell event is not overwritten by any event of an honest history. -/
theorem not_cellOverwrittenD2_fresh {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) : cellOverwrittenD2 E e = false := by
  unfold cellOverwrittenD2
  rw [Bool.eq_false_iff]
  intro hf
  rw [fold_or_eq_true_iff'] at hf
  obtain ⟨later, hl, hlo⟩ := hf
  cases hw : later.action with
  | cell w =>
    rw [hw] at hlo
    simp only [decide_eq_true_eq] at hlo
    obtain ⟨_, prior, hp, _, _, hpt, _, _⟩ :=
      metadataValid_cell hw (hH.valid later hl) e.1 hlo
    exact applicable_fresh h (hpt ▸ mem_eventTimes_of_mem hp)
  | purge m =>
    rw [hw] at hlo
    cases hc : cellUpdate? e with
    | none => rw [hc] at hlo; simp at hlo
    | some u =>
      rw [hc] at hlo
      simp only [decide_eq_true_eq] at hlo
      exact applicable_fresh h (covered_time_mem_eventTimes hl hw hlo)
  | axis _ => rw [hw] at hlo; simp at hlo
  | range _ => rw [hw] at hlo; simp at hlo

theorem canonCells_insert_other (E : Finset Event) (e : Event) (he : e ∉ E)
    (hn : cellUpdate? e = none) (hnp : purge? e = none) :
    canonCells (insert e E) = canonCells E := by
  have hclause : ∀ c : Event, (match e.action with
      | .cell u => decide (c.1 ∈ u.overwrites)
      | .purge m => match cellUpdate? c with
          | some update => decide ((c.1, (update.row, update.column)) ∈ m.covered)
          | none => false
      | _ => false) = false := by
    intro c
    unfold cellUpdate? at hn
    unfold purge? at hnp
    cases hu : e.action <;> simp_all
  ext x
  rw [mem_canonCells, mem_canonCells]
  constructor
  · rintro ⟨c, hc, w, hcw, ho, rfl⟩
    rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · rw [hn] at hcw; cases hcw
    · refine ⟨c, hc, w, hcw, ?_, rfl⟩
      rw [cellOverwrittenD2_insert E e he] at ho
      exact (Bool.or_eq_false_iff.mp ho).1
  · rintro ⟨c, hc, w, hcw, ho, rfl⟩
    refine ⟨c, Finset.mem_insert_of_mem hc, w, hcw, ?_, rfl⟩
    rw [cellOverwrittenD2_insert E e he, ho, hclause c]
    rfl

theorem cells_preserved {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) :
    (mupdate (canon E) (toM E e)).cells = canonCells (insert e E) := by
  have he := applicable_not_mem h
  rw [cells_step, canon_cells]
  cases hu : e.action with
  | cell u =>
    have hcu : cellUpdate? e = some u := cellUpdate?_eq_some.mpr hu
    have hvalid_e := metadataValid_cell hu (applicable_valid h)
    ext x
    simp only [NR.step, cellNR, cellRemoves, cellAdds, MEvent.action_toM, hu,
      Finset.mem_union, Finset.mem_filter, List.mem_toFinset, List.mem_singleton,
      decide_eq_false_iff_not, mem_canonCells]
    constructor
    · rintro (⟨⟨c, hc, w, hcw, ho, rfl⟩, hnr⟩ | rfl)
      · refine ⟨c, Finset.mem_insert_of_mem hc, w, hcw, ?_, rfl⟩
        rw [cellOverwrittenD2_insert E e he, ho, hu]
        simp only [Bool.false_or, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨_, prior, hp, w', hpw', hpt, hrow, hcol⟩ := hvalid_e c.1 hmem
        have hpc : prior = c := hH.ts_unique prior hp c hc hpt
        subst hpc
        have hww : w' = w := Action.cell.inj ((cellUpdate?_eq_some.mp hcw).symm.trans hpw').symm
        subst hww
        exact hnr ⟨hrow, hcol, hmem⟩
      · refine ⟨e, Finset.mem_insert_self e E, u, hcu, ?_, rfl⟩
        rw [cellOverwrittenD2_insert E e he, not_cellOverwrittenD2_fresh hH h, hu]
        simp only [Bool.false_or, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨_, prior, hp, _, _, hpt, _, _⟩ := hvalid_e e.1 hmem
        exact applicable_fresh h (hpt ▸ mem_eventTimes_of_mem hp)
    · rintro ⟨c, hc, w, hcw, ho, rfl⟩
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · right
        have hwu : w = u := Action.cell.inj ((cellUpdate?_eq_some.mp hcw).symm.trans hu)
        subst hwu; rfl
      · left
        rw [cellOverwrittenD2_insert E e he, hu] at ho
        have ho' := Bool.or_eq_false_iff.mp ho
        refine ⟨⟨c, hc, w, hcw, ho'.1, rfl⟩, ?_⟩
        rintro ⟨_, _, hmem⟩
        have := ho'.2
        rw [decide_eq_false_iff_not] at this
        exact this hmem
  | purge m =>
    ext x
    simp only [NR.step, cellNR, cellRemoves, cellAdds, MEvent.action_toM, hu,
      Finset.mem_union, Finset.mem_filter, List.mem_toFinset, List.not_mem_nil, or_false,
      decide_eq_false_iff_not, mem_canonCells]
    constructor
    · rintro ⟨⟨c, hc, w, hcw, ho, rfl⟩, hnr⟩
      refine ⟨c, Finset.mem_insert_of_mem hc, w, hcw, ?_, rfl⟩
      rw [cellOverwrittenD2_insert E e he, ho, hu, hcw]
      simp only [Bool.false_or, decide_eq_false_iff_not]
      exact hnr
    · rintro ⟨c, hc, w, hcw, ho, rfl⟩
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · rw [cellUpdate?_eq_some, hu] at hcw; cases hcw
      · rw [cellOverwrittenD2_insert E e he, hu, hcw] at ho
        have ho' := Bool.or_eq_false_iff.mp ho
        refine ⟨⟨c, hc, w, hcw, ho'.1, rfl⟩, ?_⟩
        have := ho'.2
        rw [decide_eq_false_iff_not] at this
        exact this
  | axis u =>
    have hn : cellUpdate? e = none := by simp [cellUpdate?, hu]
    have hnp : purge? e = none := by simp [purge?, hu]
    rw [canonCells_insert_other E e he hn hnp]
    simp [NR.step, cellNR, cellRemoves, cellAdds, MEvent.action_toM, hu]
  | range u =>
    have hn : cellUpdate? e = none := by simp [cellUpdate?, hu]
    have hnp : purge? e = none := by simp [purge?, hu]
    rw [canonCells_insert_other E e he hn hnp]
    simp [NR.step, cellNR, cellRemoves, cellAdds, MEvent.action_toM, hu]

/-! ## Purges and the honesty of extended histories -/

theorem purge?_eq_some {e : Event} {m : Purge} : purge? e = some m ↔ e.action = .purge m := by
  unfold purge?; cases e.action <;> simp

/-- A purge is never the effect of an undo, so an applicable purge passes the
direct purge guard. -/
theorem applicable_purge {e : Event} {E : Finset Event} {m : Purge} (h : applicable e E)
    (hm : e.action = .purge m) : purgeApplicable E e.2.1 m = true := by
  obtain ⟨hb, _⟩ := h
  unfold applicableB at hb
  simp only [Bool.and_eq_true] at hb
  have hcmd := hb.2
  cases hc : e.2.2.command with
  | direct action =>
    have ha : action = .purge m := by
      have h' : (Command.direct action).effect = .purge m := by rw [← hc]; exact hm
      exact h'
    rw [hc] at hcmd
    subst ha
    exact hcmd
  | undo target inverse =>
    have hi : inverse = .purge m := by
      have h' : (Command.undo target inverse).effect = .purge m := by rw [← hc]; exact hm
      exact h'
    rw [hc] at hcmd
    simp only [Bool.and_eq_true] at hcmd
    have hv := hcmd.2
    unfold validUndo at hv
    rw [fold_or_eq_true_iff'] at hv
    obtain ⟨prior, _, hpr⟩ := hv
    subst hi
    cases hpa : prior.action with
    | purge _ => rw [hpa] at hpr; simp at hpr
    | axis u =>
      rw [hpa] at hpr
      simp only [decide_eq_true_eq] at hpr
      have hinv := hpr.2.2
      simp [inverseFor, invertAction, hpa] at hinv
    | cell u =>
      rw [hpa] at hpr
      simp only [decide_eq_true_eq] at hpr
      have hinv := hpr.2.2
      simp [inverseFor, invertAction, hpa] at hinv
    | range u =>
      rw [hpa] at hpr
      simp only [decide_eq_true_eq] at hpr
      have hinv := hpr.2.2
      simp [inverseFor, invertAction, hpa] at hinv

/-- Every entry covered by an applicable purge names a cell event of the history
at the covered coordinate. -/
theorem covered_of_applicable {e : Event} {E : Finset Event} {m : Purge} (h : applicable e E)
    (hm : e.action = .purge m) {entry : Timestamp × Coordinate} (hentry : entry ∈ m.covered) :
    ∃ c ∈ E, ∃ w : CellUpdate, c.action = .cell w ∧ c.1 = entry.1 ∧ (w.row, w.column) = entry.2 := by
  have hp := applicable_purge h hm
  unfold purgeApplicable at hp
  simp only [Bool.and_eq_true] at hp
  have h4 := hp.1.2
  rw [fold_and_eq_true_iff'] at h4
  have := h4 entry hentry
  rw [fold_or_eq_true_iff'] at this
  obtain ⟨c, hc, hcc⟩ := this
  cases hw : cellUpdate? c with
  | none => rw [hw] at hcc; simp at hcc
  | some w =>
    rw [hw] at hcc
    simp only [decide_eq_true_eq] at hcc
    exact ⟨c, hc, w, cellUpdate?_eq_some.mp hw, hcc.1, hcc.2.1⟩

theorem eventTimes_mono {E : Finset Event} {e : Event} :
    eventTimes E ⊆ eventTimes (insert e E) := by
  unfold eventTimes
  apply Finset.union_subset_union
  · exact Finset.image_subset_image (Finset.subset_insert e E)
  · exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_insert e E)

theorem metadataValidB_mono {E : Finset Event} {e r : Event}
    (hv : metadataValidB E r = true) : metadataValidB (insert e E) r = true := by
  unfold metadataValidB at hv ⊢
  cases hc : cellUpdate? r with
  | some u =>
    simp only [hc] at hv ⊢
    rw [fold_and_eq_true_iff'] at hv ⊢
    intro t ht
    have := hv t ht
    rw [Bool.and_eq_true, fold_or_eq_true_iff'] at this ⊢
    obtain ⟨hlt, prior, hp, hpr⟩ := this
    exact ⟨hlt, prior, Finset.mem_insert_of_mem hp, hpr⟩
  | none =>
    simp only [hc] at hv ⊢
    cases hr : rangeUpdate? r with
    | some u =>
      simp only [hr] at hv ⊢
      rw [fold_and_eq_true_iff'] at hv ⊢
      intro t ht
      have := hv t ht
      rw [Bool.and_eq_true, fold_or_eq_true_iff'] at this ⊢
      obtain ⟨hlt, prior, hp, hpr⟩ := this
      exact ⟨hlt, prior, Finset.mem_insert_of_mem hp, hpr⟩
    | none =>
      simp only [hr] at hv ⊢
      exact hv

/-- Honesty is preserved by an applicable insertion. -/
theorem HonestHistory.insert {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) : HonestHistory (insert e E) where
  seen_sub := by
    intro r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · rw [applicable_seen h]; exact eventTimes_mono
    · exact (hH.seen_sub r hr).trans eventTimes_mono
  ts_unique := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (hab ▸ mem_eventTimes_of_mem hb) (applicable_fresh h)
    · exact absurd (hab ▸ mem_eventTimes_of_mem ha) (applicable_fresh h)
    · exact hH.ts_unique a ha b hb hab
  valid := by
    intro r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact metadataValidB_mono (applicable_valid h)
    · exact metadataValidB_mono (hH.valid r hr)
  covered_valid := by
    intro r hr m hm entry hentry
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · obtain ⟨c, hc, w, hcw, hct, hco⟩ := covered_of_applicable h hm hentry
      exact ⟨c, Finset.mem_insert_of_mem hc, w, hcw, hct, hco⟩
    · obtain ⟨c, hc, w, hcw, hct, hco⟩ := hH.covered_valid r hr m hm entry hentry
      exact ⟨c, Finset.mem_insert_of_mem hc, w, hcw, hct, hco⟩

/-! ## Tokens -/

theorem mem_axisKeepTimes {E : Finset Event} {a : Axis} {id : StableId} {t : Timestamp} :
    t ∈ axisKeepTimes E a id ↔
      (∃ c ∈ E, keepsAxis a id c = true ∧ c.1 = t) ∨
      (∃ r ∈ E, ∃ m : Purge, r.action = .purge m ∧ ∃ entry ∈ m.covered, entry.1 = t ∧
        (match a with
          | .row => entry.2.1 == id
          | .column => entry.2.2 == id) = true) := by
  unfold axisKeepTimes
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]
  apply or_congr
  · constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Finset.mem_filter] at hc
      exact ⟨c, hc.1, hc.2, rfl⟩
    · rintro ⟨c, hc, hk, rfl⟩
      exact ⟨c, Finset.mem_filter.mpr ⟨hc, hk⟩, rfl⟩
  · constructor
    · rintro ⟨r, hr, ht⟩
      cases hp : purge? r with
      | none => rw [hp] at ht; simp at ht
      | some m =>
        rw [hp, Finset.mem_biUnion] at ht
        obtain ⟨entry, hentry, ht⟩ := ht
        refine ⟨r, hr, m, purge?_eq_some.mp hp, entry, hentry, ?_⟩
        split_ifs at ht with hc
        · rw [Finset.mem_singleton] at ht; exact ⟨ht.symm, hc⟩
        · simp at ht
    · rintro ⟨r, hr, m, hm, entry, hentry, rfl, hcond⟩
      refine ⟨r, hr, ?_⟩
      rw [purge?_eq_some.mpr hm, Finset.mem_biUnion]
      refine ⟨entry, hentry, ?_⟩
      split_ifs with hc
      · exact Finset.mem_singleton_self _
      · exact absurd hcond hc

theorem axisTokenRemoved_iff {E : Finset Event} {a : Axis} {id : StableId} {t : Timestamp} :
    axisTokenRemoved E a id t = true ↔ ∃ r ∈ E, removesAxis a id r = true ∧ t ∈ r.seen := by
  unfold axisTokenRemoved
  rw [fold_or_eq_true_iff']
  simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem mem_liveAxisTokens {E : Finset Event} {a : Axis} {id : StableId} {t : Timestamp} :
    t ∈ liveAxisTokens E a id ↔
      t ∈ axisKeepTimes E a id ∧ axisTokenRemoved E a id t = false := by
  unfold liveAxisTokens
  simp only [Finset.mem_filter, Bool.not_eq_true']

theorem keepTime_mem_eventTimes {E : Finset Event} {a : Axis} {id : StableId} {t : Timestamp}
    (h : t ∈ axisKeepTimes E a id) : t ∈ eventTimes E := by
  rw [mem_axisKeepTimes] at h
  rcases h with ⟨c, hc, _, rfl⟩ | ⟨r, hr, m, hm, entry, hentry, rfl, _⟩
  · exact mem_eventTimes_of_mem hc
  · exact covered_time_mem_eventTimes hr hm hentry

theorem mem_axisKeys_of_keeps {E : Finset Event} {a : Axis} {id : StableId} {c : Event}
    (hc : c ∈ E) (hk : keepsAxis a id c = true) : (a, id) ∈ axisKeys E := by
  unfold axisKeys
  rw [Finset.mem_biUnion]
  refine ⟨c, hc, ?_⟩
  unfold keepsAxis at hk
  cases h : c.action with
  | axis u =>
    rw [h] at hk
    simp only [decide_eq_true_eq] at hk
    obtain ⟨rfl, rfl, _⟩ := hk
    simp [h]
  | cell u =>
    rw [h] at hk
    cases a
    · simp only [decide_eq_true_eq] at hk
      subst hk
      simp [h]
    · simp only [decide_eq_true_eq] at hk
      subst hk
      simp [h]
  | range _ => rw [h] at hk; simp at hk
  | purge _ => rw [h] at hk; simp at hk

theorem keeps_of_covered {a : Axis} {id : StableId} {c : Event} {w : CellUpdate}
    {entry : Timestamp × Coordinate} (hcw : c.action = .cell w)
    (hcoord : (w.row, w.column) = entry.2)
    (hcond : (match a with
      | .row => entry.2.1 == id
      | .column => entry.2.2 == id) = true) : keepsAxis a id c = true := by
  unfold keepsAxis
  rw [hcw]
  cases a
  · simp only [beq_iff_eq] at hcond
    rw [← hcoord] at hcond
    simp only [decide_eq_true_eq]
    exact hcond
  · simp only [beq_iff_eq] at hcond
    rw [← hcoord] at hcond
    simp only [decide_eq_true_eq]
    exact hcond

/-- In an honest history every keep time belongs to a known key. -/
theorem key_of_keepTime {E : Finset Event} (hH : HonestHistory E) {a : Axis} {id : StableId}
    {t : Timestamp} (h : t ∈ axisKeepTimes E a id) : (a, id) ∈ axisKeys E := by
  rw [mem_axisKeepTimes] at h
  rcases h with ⟨c, hc, hk, _⟩ | ⟨r, hr, m, hm, entry, hentry, _, hcond⟩
  · exact mem_axisKeys_of_keeps hc hk
  · obtain ⟨c, hc, w, hcw, _, hcoord⟩ := hH.covered_valid r hr m hm entry hentry
    exact mem_axisKeys_of_keeps hc (keeps_of_covered hcw hcoord hcond)

theorem mem_canonTokens' {E : Finset Event} (hH : HonestHistory E) {x : TokenEntry} :
    x ∈ canonTokens E ↔ x.2.2 ∈ liveAxisTokens E x.1 x.2.1 := by
  rw [mem_canonTokens]
  constructor
  · exact And.right
  · intro h
    exact ⟨key_of_keepTime hH (mem_liveAxisTokens.mp h).1, h⟩

theorem mem_axisKeepTimes_insert (E : Finset Event) (e : Event) (a : Axis) (id : StableId)
    (t : Timestamp) :
    t ∈ axisKeepTimes (insert e E) a id ↔
      t ∈ axisKeepTimes E a id ∨ (keepsAxis a id e = true ∧ e.1 = t) ∨
      (∃ m : Purge, e.action = .purge m ∧ ∃ entry ∈ m.covered, entry.1 = t ∧
        (match a with
          | .row => entry.2.1 == id
          | .column => entry.2.2 == id) = true) := by
  rw [mem_axisKeepTimes, mem_axisKeepTimes]
  simp only [Finset.mem_insert, exists_eq_or_imp]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

theorem axisTokenRemoved_insert (E : Finset Event) (e : Event) (a : Axis) (id : StableId)
    (t : Timestamp) :
    axisTokenRemoved (insert e E) a id t = true ↔
      axisTokenRemoved E a id t = true ∨ (removesAxis a id e = true ∧ t ∈ e.seen) := by
  rw [axisTokenRemoved_iff, axisTokenRemoved_iff]
  simp only [Finset.mem_insert, exists_eq_or_imp]
  exact or_comm

theorem axisTokenRemoved_insert_false (E : Finset Event) (e : Event) (a : Axis)
    (id : StableId) (t : Timestamp) :
    axisTokenRemoved (insert e E) a id t = false ↔
      axisTokenRemoved E a id t = false ∧ ¬ (removesAxis a id e = true ∧ t ∈ e.seen) := by
  rw [Bool.eq_false_iff, Bool.eq_false_iff]
  show ¬ (axisTokenRemoved (insert e E) a id t = true) ↔
    ¬ (axisTokenRemoved E a id t = true) ∧ ¬ (removesAxis a id e = true ∧ t ∈ e.seen)
  rw [axisTokenRemoved_insert, not_or]

/-- **Live tokens after an applicable insertion.** A token is live afterwards
exactly when it was live before and the new event does not remove its
identifier, or the new event keeps the identifier at its own timestamp. The
purge contribution to the keep set is absorbed: every covered entry names a
cell event already in the history. -/
theorem mem_liveAxisTokens_insert {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) (a : Axis) (id : StableId) (t : Timestamp) :
    t ∈ liveAxisTokens (insert e E) a id ↔
      (t ∈ liveAxisTokens E a id ∧ removesAxis a id e = false) ∨
      (keepsAxis a id e = true ∧ t = e.1) := by
  rw [mem_liveAxisTokens, mem_axisKeepTimes_insert, axisTokenRemoved_insert_false,
    mem_liveAxisTokens]
  have hseen := applicable_seen h
  have hfresh := applicable_fresh h
  constructor
  · rintro ⟨hkeep, hnr, hne⟩
    rcases hkeep with hkeep | ⟨hk, rfl⟩ | ⟨m, hm, entry, hentry, rfl, hcond⟩
    · left
      refine ⟨⟨hkeep, hnr⟩, ?_⟩
      rw [Bool.eq_false_iff]
      intro hr
      exact hne ⟨hr, hseen ▸ keepTime_mem_eventTimes hkeep⟩
    · right; exact ⟨hk, rfl⟩
    · left
      obtain ⟨c, hc, w, hcw, hct, hcoord⟩ := covered_of_applicable h hm hentry
      refine ⟨⟨?_, hnr⟩, ?_⟩
      · rw [mem_axisKeepTimes]
        left
        exact ⟨c, hc, keeps_of_covered hcw hcoord hcond, hct⟩
      · simp [removesAxis, hm]
  · rintro (⟨⟨hkeep, hnr⟩, hne⟩ | ⟨hk, rfl⟩)
    · refine ⟨Or.inl hkeep, hnr, ?_⟩
      rintro ⟨hr, _⟩
      rw [hne] at hr
      cases hr
    · refine ⟨Or.inr (Or.inl ⟨hk, rfl⟩), ?_, ?_⟩
      · rw [Bool.eq_false_iff]
        intro hr
        rw [axisTokenRemoved_iff] at hr
        obtain ⟨r, hr, _, ht⟩ := hr
        exact hfresh (hH.seen_sub r hr ht)
      · rintro ⟨_, ht⟩
        rw [hseen] at ht
        exact hfresh ht

theorem canon_tokens (E : Finset Event) : (canon E).tokens = canonTokens E := rfl

theorem toM_kills (E : Finset Event) (e : Event) : (toM E e).2.2.kills = killsOf E e := rfl

theorem tokens_preserved {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) :
    (mupdate (canon E) (toM E e)).tokens = canonTokens (insert e E) := by
  have hH' := hH.insert h
  have hlive := mem_liveAxisTokens_insert hH h
  rw [tokens_step, canon_tokens]
  ext ⟨xa, xid, xt⟩
  rw [mem_canonTokens' hH', hlive]
  cases hu : e.action with
  | axis u =>
    cases hp : u.after with
    | some p =>
      simp only [NR.step, tokNR, tokRemoves, tokAdds, removesAxis, keepsAxis,
        MEvent.action_toM, hu, hp, Finset.mem_union, Finset.mem_filter, List.mem_toFinset,
        List.mem_singleton, mem_canonTokens' hH, Option.isSome_some, if_true,
        decide_eq_false_iff_not, decide_eq_true_eq, Prod.mk.injEq, reduceCtorEq,
        false_and, and_false, not_false_eq_true, and_true]
      constructor
      · rintro (hl | ⟨rfl, rfl, rfl⟩)
        · exact Or.inl hl
        · exact Or.inr ⟨⟨rfl, rfl⟩, rfl⟩
      · rintro (hl | ⟨⟨rfl, rfl⟩, rfl⟩)
        · exact Or.inl hl
        · exact Or.inr ⟨rfl, rfl, rfl⟩
    | none =>
      simp only [NR.step, tokNR, tokRemoves, tokAdds, removesAxis, keepsAxis, killsOf, toM_kills,
        MEvent.action_toM, hu, hp, Finset.mem_union, Finset.mem_filter, List.mem_toFinset,
        List.not_mem_nil, or_false, Option.isSome_none, Option.isNone_none, if_true, if_false,
        mem_canonTokens' hH, decide_eq_false_iff_not, decide_eq_true_eq, true_and,
        eq_self_iff_true, and_true, Bool.false_eq_true, false_and, and_false, or_false]
      constructor
      · rintro ⟨hl, hnr⟩
        refine ⟨hl, ?_⟩
        rintro ⟨rfl, rfl⟩
        exact hnr ⟨rfl, rfl, hl⟩
      · rintro ⟨hl, hnr⟩
        refine ⟨hl, ?_⟩
        rintro ⟨rfl, rfl, _⟩
        exact hnr ⟨rfl, rfl⟩
  | cell u =>
    simp only [NR.step, tokNR, tokRemoves, tokAdds, removesAxis, keepsAxis, killsOf,
      MEvent.action_toM, hu, Finset.mem_union, Finset.mem_filter, List.mem_toFinset,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, mem_canonTokens' hH,
      decide_eq_false_iff_not, decide_eq_true_eq, Prod.mk.injEq, Bool.false_eq_true,
      not_false_eq_true, and_true]
    cases xa
    · simp only [decide_eq_true_eq, reduceCtorEq, false_and, or_false, true_and]
      constructor
      · rintro (hl | ⟨rfl, rfl⟩)
        · exact Or.inl hl
        · exact Or.inr ⟨rfl, rfl⟩
      · rintro (hl | ⟨rfl, rfl⟩)
        · exact Or.inl hl
        · exact Or.inr ⟨rfl, rfl⟩
    · simp only [decide_eq_true_eq, reduceCtorEq, false_and, false_or, true_and]
      constructor
      · rintro (hl | ⟨rfl, rfl⟩)
        · exact Or.inl hl
        · exact Or.inr ⟨rfl, rfl⟩
      · rintro (hl | ⟨rfl, rfl⟩)
        · exact Or.inl hl
        · exact Or.inr ⟨rfl, rfl⟩
  | range u =>
    simp [NR.step, tokNR, tokRemoves, tokAdds, removesAxis, keepsAxis, MEvent.action_toM, hu,
      mem_canonTokens' hH]
  | purge m =>
    simp [NR.step, tokNR, tokRemoves, tokAdds, removesAxis, keepsAxis, MEvent.action_toM, hu,
      mem_canonTokens' hH]

/-! ## Assembly -/

/-- **Update preserves the representation.** The materialised update of the
canonical state of an honest history by the erased event is the canonical state
of the extended history. -/
theorem update_preserves_canon {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) : mupdate (canon E) (toM E e) = canon (insert e E) :=
  MState.ext' (known_preserved h) (tokens_preserved hH h) (pos_preserved h)
    (cells_preserved hH h) (ranges_preserved hH h)

theorem updatePreservesCanon : UpdatePreservesCanon :=
  fun _ _ hH h => update_preserves_canon hH h

/-! ## Histories reached by applicable insertions -/

/-- Union-model histories reached from the empty history by applicable insertions. -/
inductive Reach : Finset Event → Prop
  | empty : Reach ∅
  | step {E : Finset Event} {e : Event} : Reach E → applicable e E → Reach (insert e E)

theorem HonestHistory.empty : HonestHistory ∅ where
  seen_sub := by intro r hr; simp at hr
  ts_unique := by intro a ha; simp at ha
  valid := by intro r hr; simp at hr
  covered_valid := by intro r hr; simp at hr

theorem Reach.honest {E : Finset Event} (h : Reach E) : HonestHistory E := by
  induction h with
  | empty => exact HonestHistory.empty
  | step _ ha ih => exact ih.insert ha

theorem canon_empty : canon ∅ = MState.empty := by
  apply MState.ext' <;> simp [canon, MState.empty, canonKnown, canonTokens, canonPos, canonCells,
    canonRanges, axisKeys]

/-- **The materialised replica tracks the union model.** For every reachable
union-model history there is a sequence of erased operations whose
materialised fold from the initial state is the canonical state of that
history: the operations of the history, erased at their issuing states, in
issue order. -/
theorem Reach.materialised {E : Finset Event} (h : Reach E) :
    ∃ ρ : List MEvent, applySeq M.toUpdateSig M.init ρ = canon E := by
  induction h with
  | empty => exact ⟨[], by simp [applySeq, M, canon_empty]⟩
  | @step E e hr ha ih =>
    obtain ⟨ρ, hρ⟩ := ih
    refine ⟨ρ ++ [toM E e], ?_⟩
    have hstep : applySeq M.toUpdateSig M.init (ρ ++ [toM E e])
        = mupdate (applySeq M.toUpdateSig M.init ρ) (toM E e) := by
      unfold applySeq
      rw [List.foldl_append]
      rfl
    rw [hstep, hρ]
    exact update_preserves_canon hr.honest ha

#print axioms update_preserves_canon
#print axioms Reach.materialised

end Sal.MRDTs.Instances.AegisSheet.Materialised
