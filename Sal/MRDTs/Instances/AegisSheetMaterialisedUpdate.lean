import Sal.MRDTs.Instances.AegisSheetMaterialisedEquivalence
import Sal.MRDTs.Instances.AegisSheetMaterialisedJoin

/-!
# Update preservation for the materialised AegisSheet

An honest update of the union model commutes with the canonical state:
`mupdate (canon E) (toM P e) = canon (insert e E)` whenever `e` is applicable
at a past `P ⊆ E`, its timestamp is fresh in `E`, and `E` satisfies the
invariants the union model maintains along honest executions (seen sets within
the history's timestamps, unique timestamps, valid metadata, covered entries
naming cell events). The past need not be the whole history: an event issued
concurrently with part of `E` is covered, which is what a concurrent execution
needs. Without the invariants the statement is false: a removal whose `seen`
set names a fresh timestamp would kill a token the materialised update adds,
and an overwrite list naming a timestamp at another coordinate would mask a
version the materialised update keeps. Folding the erased operations of any
issue-ordered history therefore yields its canonical state.
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

theorem not_mem_of_fresh {E : Finset Event} {e : Event} (hfresh : e.1 ∉ eventTimes E) : e ∉ E :=
  fun he => hfresh (mem_eventTimes_of_mem he)

theorem eventTimes_mono_subset {P E : Finset Event} (h : P ⊆ E) :
    eventTimes P ⊆ eventTimes E := by
  unfold eventTimes
  apply Finset.union_subset_union
  · exact Finset.image_subset_image h
  · exact Finset.biUnion_subset_biUnion_of_subset_left _ h

/-! ## The `known` component -/

theorem canonKnown_insert (P E : Finset Event) (e : Event) (he : e ∉ E) :
    canonKnown (insert e E) = canonKnown E ∪ (knownAdds (toM P e)).toFinset := by
  unfold canonKnown
  rw [Finset.biUnion_insert, Finset.union_comm]
  congr 1
  unfold knownAdds axisUpdate?
  rw [MEvent.action_toM]
  cases e.action <;> simp

theorem known_preserved {P E : Finset Event} {e : Event} (he : e ∉ E) :
    (mupdate (canon E) (toM P e)).known = canonKnown (insert e E) := by
  rw [known_step, canonKnown_insert P E e he]
  rfl

/-! ## The position register -/

theorem laterAxisCandidate_insert (E : Finset Event) (e : Event) (he : e ∉ E)
    (axis : Axis) (id : StableId) (c : Event) :
    laterAxisCandidate (insert e E) axis id c =
      (laterAxisCandidate E axis id c || (axisCandidate axis id e && decide (c.1 < e.1))) := by
  unfold laterAxisCandidate
  rw [Finset.fold_insert he, Bool.or_comm]

theorem laterAxisCandidate_iff {E : Finset Event} {a : Axis} {id : StableId} {c : Event} :
    laterAxisCandidate E a id c = true ↔ ∃ l ∈ E, axisCandidate a id l = true ∧ c.1 < l.1 := by
  unfold laterAxisCandidate
  rw [fold_or_eq_true_iff']
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Among the candidates of an identifier, a latest one has no later candidate. -/
theorem exists_nolater {E : Finset Event} {a : Axis} {id : StableId} {l : Event} (hl : l ∈ E)
    (hc : axisCandidate a id l = true) :
    ∃ m ∈ E, axisCandidate a id m = true ∧ laterAxisCandidate E a id m = false ∧ l.1 ≤ m.1 := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (E.filter fun x => axisCandidate a id x = true)
    (fun x => x.1) ⟨l, Finset.mem_filter.mpr ⟨hl, hc⟩⟩
  rw [Finset.mem_filter] at hm
  refine ⟨m, hm.1, hm.2, ?_, hmax l (Finset.mem_filter.mpr ⟨hl, hc⟩)⟩
  rw [Bool.eq_false_iff]
  intro hf
  rw [laterAxisCandidate_iff] at hf
  obtain ⟨l', hl', hc', hlt⟩ := hf
  exact absurd (hmax l' (Finset.mem_filter.mpr ⟨hl', hc'⟩)) (not_le.mpr hlt)

theorem mem_canonPos_of {E : Finset Event} {a : Axis} {id : StableId} {m : Event} (hm : m ∈ E)
    (hc : axisCandidate a id m = true) (hnl : laterAxisCandidate E a id m = false) :
    ∃ q, (a, id, m.1, q) ∈ canonPos E := by
  rw [axisCandidate_iff] at hc
  obtain ⟨u, hu, rfl, rfl, hsome⟩ := hc
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨q, mem_canonPos.mpr ⟨m, hm, u, hu, q, hq, hnl, rfl⟩⟩

theorem posCand_toM (E : Finset Event) (e : Event) :
    posCand (toM E e) = match axisUpdate? e with
      | some u => match u.after with
          | some p => some (u.axis, u.id, e.1, p)
          | none => none
      | none => none := by
  unfold posCand axisUpdate?
  rw [MEvent.action_toM]
  cases e.action <;> rfl

theorem pos_preserved {P E : Finset Event} {e : Event} (hfresh : e.1 ∉ eventTimes E) :
    (mupdate (canon E) (toM P e)).pos = canonPos (insert e E) := by
  have he : e ∉ E := not_mem_of_fresh hfresh
  have hne : ∀ c ∈ E, c.1 ≠ e.1 := fun c hc h => hfresh (h ▸ mem_eventTimes_of_mem hc)
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
      unfold posInsert
      split
      next hlater =>
        -- a later candidate is already registered: neither side changes
        obtain ⟨x, hx, hkey, hlt⟩ := hlater
        rw [mem_canonPos] at hx
        obtain ⟨c, hc, v, hcv, q, hq, _, rfl⟩ := hx
        simp only [posKey, posTs, Prod.mk.injEq] at hkey hlt
        obtain ⟨hva, hvi⟩ := hkey
        have hcc : axisCandidate u.axis u.id c = true := by
          rw [← hva, ← hvi]
          exact axisCandidate_iff.mpr ⟨v, hcv, rfl, rfl, by rw [hq]; rfl⟩
        ext y
        rw [mem_canonPos, mem_canonPos]
        constructor
        · rintro ⟨d, hd, w, hdw, r, hr, hl, rfl⟩
          refine ⟨d, Finset.mem_insert_of_mem hd, w, hdw, r, hr, ?_, rfl⟩
          rw [laterAxisCandidate_insert E e he, hl, Bool.false_or]
          by_cases hk : w.axis = u.axis ∧ w.id = u.id
          · obtain ⟨hk1, hk2⟩ := hk
            rw [hk1, hk2, hcand, Bool.true_and, decide_eq_false_iff_not, not_lt]
            have hnlt : ¬ d.1 < c.1 := by
              intro hlt'
              have hcc' : axisCandidate w.axis w.id c = true := by rw [hk1, hk2]; exact hcc
              have := laterAxisCandidate_iff.mpr ⟨c, hc, hcc', hlt'⟩
              rw [this] at hl
              cases hl
            exact le_trans (le_of_lt hlt) (not_lt.mp hnlt)
          · have hwe : axisCandidate w.axis w.id e = false := by
              rw [Bool.eq_false_iff]
              intro hf
              rw [axisCandidate_iff] at hf
              obtain ⟨u', hu', h1, h2, _⟩ := hf
              rw [hu] at hu'
              cases hu'
              exact hk ⟨h1.symm, h2.symm⟩
            rw [hwe, Bool.false_and]
        · rintro ⟨d, hd, w, hdw, r, hr, hl, rfl⟩
          rw [Finset.mem_insert] at hd
          rcases hd with rfl | hd
          · exfalso
            rw [hu] at hdw
            cases hdw
            rw [laterAxisCandidate_insert E _ he] at hl
            have hl' := Bool.or_eq_false_iff.mp hl
            have := laterAxisCandidate_iff.mpr ⟨c, hc, hcc, hlt⟩
            rw [this] at hl'
            exact Bool.noConfusion hl'.1
          · refine ⟨d, hd, w, hdw, r, hr, ?_, rfl⟩
            rw [laterAxisCandidate_insert E e he] at hl
            exact (Bool.or_eq_false_iff.mp hl).1
      next hlater =>
        have hnl : laterAxisCandidate E u.axis u.id e = false := by
          rw [Bool.eq_false_iff]
          intro hf
          rw [laterAxisCandidate_iff] at hf
          obtain ⟨l, hl, hlc, hlt⟩ := hf
          obtain ⟨m, hm, hmc, hmnl, hle⟩ := exists_nolater hl hlc
          obtain ⟨q, hq⟩ := mem_canonPos_of hm hmc hmnl
          exact hlater ⟨_, hq, rfl, lt_of_lt_of_le hlt hle⟩
        ext x
        rw [Finset.mem_insert, Finset.mem_filter, mem_canonPos, mem_canonPos]
        constructor
        · rintro (rfl | ⟨⟨c, hc, v, hcv, q, hq, hl, rfl⟩, hk⟩)
          · refine ⟨e, Finset.mem_insert_self e E, u, hu, p, ha, ?_, rfl⟩
            rw [laterAxisCandidate_insert E e he, hnl]
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
            have hlt : e.1 < c.1 := lt_of_le_of_ne this (hne c hc).symm
            exact hlater ⟨(v.axis, v.id, c.1, q),
              mem_canonPos.mpr ⟨c, hc, v, hcv, q, hq, hl'.1, rfl⟩, by simp [posKey, h1, h2], hlt⟩

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
    (hfresh : e.1 ∉ eventTimes E) : rangeOverwritten E e = false := by
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
    exact hfresh (hpt ▸ mem_eventTimes_of_mem hp)

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

theorem ranges_preserved {P E : Finset Event} {e : Event} (hH : HonestHistory E)
    (hP : P ⊆ E) (hfresh : e.1 ∉ eventTimes E) (h : applicable e P) :
    (mupdate (canon E) (toM P e)).ranges = canonRanges (insert e E) := by
  have he := not_mem_of_fresh hfresh
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
        have hpc : prior = c := hH.ts_unique prior (hP hp) c hc hpt
        subst hpc
        have hww : w' = w := Action.range.inj ((rangeUpdate?_eq_some.mp hcw).symm.trans hpw').symm
        subst hww
        exact hnr ⟨hid, hmem⟩
      · refine ⟨e, Finset.mem_insert_self e E, u, hru, ?_, rfl⟩
        rw [rangeOverwritten_insert E e he, not_rangeOverwritten_fresh hH hfresh, hru]
        simp only [Bool.false_or, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨_, prior, hp, _, _, hpt, _⟩ := hvalid_e e.1 hmem
        exact hfresh (hpt ▸ mem_eventTimes_of_mem (hP hp))
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
    (hfresh : e.1 ∉ eventTimes E) : cellOverwrittenD2 E e = false := by
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
    exact hfresh (hpt ▸ mem_eventTimes_of_mem hp)
  | purge m =>
    rw [hw] at hlo
    cases hc : cellUpdate? e with
    | none => rw [hc] at hlo; simp at hlo
    | some u =>
      rw [hc] at hlo
      simp only [decide_eq_true_eq] at hlo
      exact hfresh (covered_time_mem_eventTimes hl hw hlo)
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

theorem cells_preserved {P E : Finset Event} {e : Event} (hH : HonestHistory E)
    (hP : P ⊆ E) (hfresh : e.1 ∉ eventTimes E) (h : applicable e P) :
    (mupdate (canon E) (toM P e)).cells = canonCells (insert e E) := by
  have he := not_mem_of_fresh hfresh
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
        have hpc : prior = c := hH.ts_unique prior (hP hp) c hc hpt
        subst hpc
        have hww : w' = w := Action.cell.inj ((cellUpdate?_eq_some.mp hcw).symm.trans hpw').symm
        subst hww
        exact hnr ⟨hrow, hcol, hmem⟩
      · refine ⟨e, Finset.mem_insert_self e E, u, hcu, ?_, rfl⟩
        rw [cellOverwrittenD2_insert E e he, not_cellOverwrittenD2_fresh hH hfresh, hu]
        simp only [Bool.false_or, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨_, prior, hp, _, _, hpt, _, _⟩ := hvalid_e e.1 hmem
        exact hfresh (hpt ▸ mem_eventTimes_of_mem (hP hp))
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
    eventTimes E ⊆ eventTimes (insert e E) :=
  eventTimes_mono_subset (Finset.subset_insert e E)

theorem metadataValidB_mono_subset {P E : Finset Event} {r : Event} (hsub : P ⊆ E)
    (hv : metadataValidB P r = true) : metadataValidB E r = true := by
  unfold metadataValidB at hv ⊢
  cases hc : cellUpdate? r with
  | some u =>
    simp only [hc] at hv ⊢
    rw [fold_and_eq_true_iff'] at hv ⊢
    intro t ht
    have := hv t ht
    rw [Bool.and_eq_true, fold_or_eq_true_iff'] at this ⊢
    obtain ⟨hlt, prior, hp, hpr⟩ := this
    exact ⟨hlt, prior, hsub hp, hpr⟩
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
      exact ⟨hlt, prior, hsub hp, hpr⟩
    | none =>
      simp only [hr] at hv ⊢
      exact hv

/-- Honesty is preserved by inserting an event applicable at a past of the
history with a fresh timestamp. -/
theorem HonestHistory.insert {P E : Finset Event} {e : Event} (hH : HonestHistory E) (hP : P ⊆ E)
    (hfresh : e.1 ∉ eventTimes E) (h : applicable e P) : HonestHistory (insert e E) where
  seen_sub := by
    intro r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · rw [applicable_seen h]; exact (eventTimes_mono_subset hP).trans eventTimes_mono
    · exact (hH.seen_sub r hr).trans eventTimes_mono
  ts_unique := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (hab ▸ mem_eventTimes_of_mem hb) hfresh
    · exact absurd (hab ▸ mem_eventTimes_of_mem ha) hfresh
    · exact hH.ts_unique a ha b hb hab
  valid := by
    intro r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact metadataValidB_mono_subset (hP.trans (Finset.subset_insert _ _)) (applicable_valid h)
    · exact metadataValidB_mono_subset (Finset.subset_insert _ _) (hH.valid r hr)
  covered_valid := by
    intro r hr m hm entry hentry
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · obtain ⟨c, hc, w, hcw, hct, hco⟩ := covered_of_applicable h hm hentry
      exact ⟨c, Finset.mem_insert_of_mem (hP hc), w, hcw, hct, hco⟩
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

/-- In an honest history every keep time is the timestamp of an event keeping
the identifier. -/
theorem keepTime_event {E : Finset Event} (hH : HonestHistory E) {a : Axis} {id : StableId}
    {t : Timestamp} (h : t ∈ axisKeepTimes E a id) :
    ∃ c ∈ E, c.1 = t ∧ keepsAxis a id c = true := by
  rw [mem_axisKeepTimes] at h
  rcases h with ⟨c, hc, hk, hct⟩ | ⟨r, hr, m, hm, entry, hentry, rfl, hcond⟩
  · exact ⟨c, hc, hct, hk⟩
  · obtain ⟨c, hc, w, hcw, hct, hcoord⟩ := hH.covered_valid r hr m hm entry hentry
    exact ⟨c, hc, hct, keeps_of_covered hcw hcoord hcond⟩

theorem axisTokenRemoved_mono {P E : Finset Event} (hP : P ⊆ E) {a : Axis} {id : StableId}
    {t : Timestamp} (h : axisTokenRemoved P a id t = true) : axisTokenRemoved E a id t = true := by
  rw [axisTokenRemoved_iff] at h ⊢
  obtain ⟨r, hr, hra, ht⟩ := h
  exact ⟨r, hP hr, hra, ht⟩

/-- The covered coordinate's component along an axis matches an identifier. -/
def axisCond (a : Axis) (entry : Timestamp × Coordinate) (id : StableId) : Bool :=
  match a with
  | .row => entry.2.1 == id
  | .column => entry.2.2 == id

theorem cond_of_keeps {a : Axis} {id : StableId} {c : Event} {w : CellUpdate}
    {entry : Timestamp × Coordinate} (hcw : c.action = .cell w)
    (hcoord : (w.row, w.column) = entry.2) (hk : keepsAxis a id c = true) :
    axisCond a entry id = true := by
  unfold keepsAxis at hk
  rw [hcw] at hk
  unfold axisCond
  cases a
  · simp only [decide_eq_true_eq] at hk
    simp only [beq_iff_eq]
    rw [← hcoord]
    exact hk
  · simp only [decide_eq_true_eq] at hk
    simp only [beq_iff_eq]
    rw [← hcoord]
    exact hk

/-- A token live in the history is live in an issuing past exactly when the
past knows its timestamp. -/
theorem live_past_iff {P E : Finset Event} (hH : HonestHistory E) (hP : P ⊆ E) {a : Axis}
    {id : StableId} {t : Timestamp} (hlive : t ∈ liveAxisTokens E a id) :
    t ∈ liveAxisTokens P a id ↔ t ∈ eventTimes P := by
  rw [mem_liveAxisTokens] at hlive ⊢
  constructor
  · rintro ⟨hkeep, _⟩
    exact keepTime_mem_eventTimes hkeep
  · intro ht
    obtain ⟨c, hc, hct, hk⟩ := keepTime_event hH hlive.1
    refine ⟨?_, ?_⟩
    · unfold eventTimes at ht
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at ht
      rw [mem_axisKeepTimes]
      rcases ht with ⟨r, hr, hrt⟩ | ⟨r, hr, hrt⟩
      · have hrc : r = c := hH.ts_unique r (hP hr) c hc (hrt.trans hct.symm)
        exact Or.inl ⟨r, hr, hrc ▸ hk, hrt⟩
      · cases hp : purge? r with
        | none => rw [hp] at hrt; simp at hrt
        | some m =>
          rw [hp, Finset.mem_image] at hrt
          obtain ⟨entry, hentry, het⟩ := hrt
          have hm := purge?_eq_some.mp hp
          obtain ⟨c', hc', w, hcw, hct', hcoord⟩ := hH.covered_valid r (hP hr) m hm entry hentry
          have hcc : c' = c := hH.ts_unique c' hc' c hc (hct'.trans (het.trans hct.symm))
          have hk' : keepsAxis a id c' = true := hcc ▸ hk
          exact Or.inr ⟨r, hr, m, hm, entry, hentry, het, cond_of_keeps hcw hcoord hk'⟩
    · rw [Bool.eq_false_iff]
      intro hr
      have := axisTokenRemoved_mono hP hr
      rw [hlive.2] at this
      cases this

/-- **Live tokens after an insertion.** A token is live afterwards exactly
when it was live before and the new event does not remove its identifier
while knowing the token, or the new event keeps the identifier at its own
timestamp. The purge contribution to the keep set is absorbed: every covered
entry names a cell event already in the history. -/
theorem mem_liveAxisTokens_insert {P E : Finset Event} {e : Event} (hH : HonestHistory E)
    (hP : P ⊆ E) (hfresh : e.1 ∉ eventTimes E) (h : applicable e P) (a : Axis) (id : StableId)
    (t : Timestamp) :
    t ∈ liveAxisTokens (insert e E) a id ↔
      (t ∈ liveAxisTokens E a id ∧ ¬ (removesAxis a id e = true ∧ t ∈ eventTimes P)) ∨
      (keepsAxis a id e = true ∧ t = e.1) := by
  rw [mem_liveAxisTokens, mem_axisKeepTimes_insert, axisTokenRemoved_insert_false,
    mem_liveAxisTokens]
  have hseen := applicable_seen h
  constructor
  · rintro ⟨hkeep, hnr, hne⟩
    rcases hkeep with hkeep | ⟨hk, rfl⟩ | ⟨m, hm, entry, hentry, rfl, hcond⟩
    · left
      refine ⟨⟨hkeep, hnr⟩, ?_⟩
      rintro ⟨hr, ht⟩
      exact hne ⟨hr, hseen ▸ ht⟩
    · right; exact ⟨hk, rfl⟩
    · left
      obtain ⟨c, hc, w, hcw, hct, hcoord⟩ := covered_of_applicable h hm hentry
      refine ⟨⟨?_, hnr⟩, ?_⟩
      · rw [mem_axisKeepTimes]
        left
        exact ⟨c, hP hc, keeps_of_covered hcw hcoord hcond, hct⟩
      · simp [removesAxis, hm]
  · rintro (⟨⟨hkeep, hnr⟩, hne⟩ | ⟨hk, rfl⟩)
    · refine ⟨Or.inl hkeep, hnr, ?_⟩
      rintro ⟨hr, ht⟩
      exact hne ⟨hr, hseen ▸ ht⟩
    · refine ⟨Or.inr (Or.inl ⟨hk, rfl⟩), ?_, ?_⟩
      · rw [Bool.eq_false_iff]
        intro hr
        rw [axisTokenRemoved_iff] at hr
        obtain ⟨r, hr, _, ht⟩ := hr
        exact hfresh (hH.seen_sub r hr ht)
      · rintro ⟨_, ht⟩
        rw [hseen] at ht
        exact hfresh (eventTimes_mono_subset hP ht)

theorem canon_tokens (E : Finset Event) : (canon E).tokens = canonTokens E := rfl

theorem toM_kills (E : Finset Event) (e : Event) : (toM E e).2.2.kills = killsOf E e := rfl

theorem tokens_preserved {P E : Finset Event} {e : Event} (hH : HonestHistory E)
    (hP : P ⊆ E) (hfresh : e.1 ∉ eventTimes E) (h : applicable e P) :
    (mupdate (canon E) (toM P e)).tokens = canonTokens (insert e E) := by
  have hH' := hH.insert hP hfresh h
  have hlive := mem_liveAxisTokens_insert hH hP hfresh h
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
        eq_self_iff_true, and_true, Bool.false_eq_true, false_and, and_false, or_false,
        and_assoc]
      constructor
      · rintro ⟨hl, hnr⟩
        refine ⟨hl, ?_⟩
        rintro ⟨rfl, rfl, ht⟩
        exact hnr ⟨rfl, rfl, (live_past_iff hH hP hl).mpr ht⟩
      · rintro ⟨hl, hnr⟩
        refine ⟨hl, ?_⟩
        rintro ⟨rfl, rfl, ht⟩
        exact hnr ⟨rfl, rfl, (live_past_iff hH hP hl).mp ht⟩
  | cell u =>
    simp only [NR.step, tokNR, tokRemoves, tokAdds, removesAxis, keepsAxis, killsOf,
      MEvent.action_toM, hu, Finset.mem_union, Finset.mem_filter, List.mem_toFinset,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, mem_canonTokens' hH,
      decide_eq_false_iff_not, decide_eq_true_eq, Prod.mk.injEq, Bool.false_eq_true,
      false_and, not_false_eq_true, and_true]
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
canonical state of an honest history by an event erased at its issuing past
is the canonical state of the extended history. -/
theorem update_preserves_canon_of_past {P E : Finset Event} {e : Event} (hH : HonestHistory E)
    (hP : P ⊆ E) (hfresh : e.1 ∉ eventTimes E) (h : applicable e P) :
    mupdate (canon E) (toM P e) = canon (insert e E) :=
  MState.ext' (known_preserved (not_mem_of_fresh hfresh)) (tokens_preserved hH hP hfresh h)
    (pos_preserved hfresh) (cells_preserved hH hP hfresh h) (ranges_preserved hH hP hfresh h)

/-- The sequential case: the past is the whole history. -/
theorem update_preserves_canon {E : Finset Event} {e : Event} (hH : HonestHistory E)
    (h : applicable e E) : mupdate (canon E) (toM E e) = canon (insert e E) :=
  update_preserves_canon_of_past hH (Finset.Subset.refl E) (applicable_fresh h) h

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
  | step _ ha ih => exact ih.insert (Finset.Subset.refl _) (applicable_fresh ha) ha

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

/-! ## Issue-ordered histories -/

/-- An issue-ordered history: events paired with the pasts they were issued
at, such that every past lies among the earlier events, every timestamp is
fresh among the earlier events' times, and every event is applicable at its
past. Any causality-respecting enumeration of an honest concurrent execution
of the union model is of this form. -/
inductive Issued : List (Event × Finset Event) → Prop
  | nil : Issued []
  | snoc {ρ : List (Event × Finset Event)} {e : Event} {P : Finset Event} :
      Issued ρ → P ⊆ (ρ.map Prod.fst).toFinset →
      e.1 ∉ eventTimes (ρ.map Prod.fst).toFinset → applicable e P →
      Issued (ρ ++ [(e, P)])

/-- The events of an issue-ordered history. -/
def histEvents (ρ : List (Event × Finset Event)) : Finset Event := (ρ.map Prod.fst).toFinset

/-- The erased operations of an issue-ordered history, each carrying the kills
computed at its past. -/
def erase (ρ : List (Event × Finset Event)) : List MEvent := ρ.map fun x => toM x.2 x.1

theorem histEvents_nil : histEvents [] = ∅ := by simp [histEvents]

theorem histEvents_snoc (ρ : List (Event × Finset Event)) (x : Event × Finset Event) :
    histEvents (ρ ++ [x]) = insert x.1 (histEvents ρ) := by
  ext y; simp [histEvents]

theorem Issued.honest {ρ : List (Event × Finset Event)} (h : Issued ρ) :
    HonestHistory (histEvents ρ) := by
  induction h with
  | nil => rw [histEvents_nil]; exact HonestHistory.empty
  | snoc _ hP hfresh ha ih => rw [histEvents_snoc]; exact ih.insert hP hfresh ha

/-- **The materialised fold of an issue-ordered history is its canonical
state.** With the restricted Join, which exhibits every reachable materialised
state as such a fold, this connects the port's reachable states to the union
model's event sets. -/
theorem Issued.fold {ρ : List (Event × Finset Event)} (h : Issued ρ) :
    applySeq M.toUpdateSig M.init (erase ρ) = canon (histEvents ρ) := by
  induction h with
  | nil => rw [histEvents_nil, canon_empty]; rfl
  | @snoc ρ e P hr hP hfresh ha ih =>
    rw [histEvents_snoc]
    have hstep : applySeq M.toUpdateSig M.init (erase (ρ ++ [(e, P)]))
        = mupdate (applySeq M.toUpdateSig M.init (erase ρ)) (toM P e) := by
      unfold erase applySeq
      rw [List.map_append, List.foldl_append]
      rfl
    rw [hstep, ih]
    exact update_preserves_canon_of_past hr.honest hP hfresh ha

#print axioms update_preserves_canon_of_past
#print axioms Reach.materialised
#print axioms Issued.fold

end Sal.MRDTs.Instances.AegisSheet.Materialised
