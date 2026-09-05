import Sal.MRDTs.Instances.AegisSheetMaterialisedBridge

/-!
# From the port's executions to the union model

Every version of a certified execution of the materialised sheet `M`, with
no purge and with every undo naming an operation of the issuer's causal past,
is the canonical state of an issue-ordered union-model history whose events
are the version's events lifted with their causal summaries. The port's
issuance at the materialised state implies the union model's issuance at the
lifted past: the effect clauses give the named tokens and versions, the
before-image clauses give the union model's guards through the materialised
observers, and undo validity is the separate premise `UndoHonest`, which the
materialised state cannot decide. Together with the bridge in the other
direction this is the cross-model theorem for the port's own concurrent
executions.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs Sal.MRDTs.Foundation
open Classical

/-! ## Fold independence at an honest context -/

/-- Two `loOn`-respecting enumerations of one closed, supported event set fold
to the same materialised state at an honest replay context. -/
theorem fold_eq_of_enums {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig} (hHon : Honest C)
    (hir : ∀ a : MEvent, ¬ C.vis a a) {ev : Set MEvent} (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ ev → a ∈ ev)
    {ρ ρ' : List MEvent} (hp : listPermOf ρ ev) (hr : respects ρ (loOn C ev))
    (hp' : listPermOf ρ' ev) (hr' : respects ρ' (loOn C ev)) :
    applySeq M.toUpdateSig M.init ρ = applySeq M.toUpdateSig M.init ρ' := by
  apply MState.ext'
  · rw [known_fold, known_fold]
    ext k
    rw [mem_knownL_perm hp, mem_knownL_perm hp']
  · rw [tokNR.fold_canon MState.tokens tokens_init tokens_step ρ
        (tokNR.wf_of_enum (tokNR_honest hHon) hir hin hcl hp hr),
      tokNR.fold_canon MState.tokens tokens_init tokens_step ρ'
        (tokNR.wf_of_enum (tokNR_honest hHon) hir hin hcl hp' hr')]
    ext x
    rw [tokNR.mem_canonL_perm hp, tokNR.mem_canonL_perm hp']
  · rw [pos_fold ρ (ts_nodup_of_enum hin hp), pos_fold ρ' (ts_nodup_of_enum hin hp')]
    ext x
    rw [mem_posL_perm hp, mem_posL_perm hp']
  · rw [cellNR.fold_canon MState.cells cells_init cells_step ρ
        (cellNR.wf_of_enum (cellNR_honest hHon) hir hin hcl hp hr),
      cellNR.fold_canon MState.cells cells_init cells_step ρ'
        (cellNR.wf_of_enum (cellNR_honest hHon) hir hin hcl hp' hr')]
    ext x
    rw [cellNR.mem_canonL_perm hp, cellNR.mem_canonL_perm hp']
  · rw [rangeNR.fold_canon MState.ranges ranges_init ranges_step ρ
        (rangeNR.wf_of_enum (rangeNR_honest hHon) hir hin hcl hp hr),
      rangeNR.fold_canon MState.ranges ranges_init ranges_step ρ'
        (rangeNR.wf_of_enum (rangeNR_honest hHon) hir hin hcl hp' hr')]
    ext x
    rw [rangeNR.mem_canonL_perm hp, rangeNR.mem_canonL_perm hp']

/-! ## Issue-ordered histories: pasts, injectivity, restriction -/

theorem mem_histEvents {ρ : List (Event × Finset Event)} {z : Event} :
    z ∈ histEvents ρ ↔ ∃ y ∈ ρ, y.1 = z := by
  simp [histEvents]

theorem histEvents_filter_sub (ρ : List (Event × Finset Event)) (p : Event × Finset Event → Bool) :
    histEvents (ρ.filter p) ⊆ histEvents ρ := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_histEvents.mp hz
  exact mem_histEvents.mpr ⟨y, (List.mem_filter.mp hy).1, rfl⟩

theorem Issued.past_sub {ρ : List (Event × Finset Event)} (h : Issued ρ) :
    ∀ x ∈ ρ, x.2 ⊆ histEvents ρ := by
  induction h with
  | nil => intro x hx; simp at hx
  | @snoc ρ e P _ hP _ _ ih =>
    intro x hx
    have hsub : histEvents ρ ⊆ histEvents (ρ ++ [(e, P)]) := by
      rw [histEvents_snoc]; exact Finset.subset_insert _ _
    rcases List.mem_append.mp hx with hx | hx
    · exact (ih x hx).trans hsub
    · rw [List.mem_singleton] at hx
      subst hx
      exact hP.trans hsub

theorem Issued.ts_inj {ρ : List (Event × Finset Event)} (h : Issued ρ) :
    ∀ x ∈ ρ, ∀ y ∈ ρ, x.1.1 = y.1.1 → x = y := by
  induction h with
  | nil => intro x hx; simp at hx
  | @snoc ρ e P _ _ hfresh _ ih =>
    intro x hx y hy hxy
    have hnew : ∀ x ∈ ρ, x.1.1 ≠ e.1 := fun x hx h => hfresh (by
      rw [← h]; exact mem_eventTimes_of_mem (mem_histEvents.mpr ⟨x, hx, rfl⟩))
    rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
    · exact ih x hx y hy hxy
    · rw [List.mem_singleton] at hy; subst hy; exact absurd hxy (hnew x hx)
    · rw [List.mem_singleton] at hx; subst hx; exact absurd hxy.symm (hnew y hy)
    · rw [List.mem_singleton] at hx hy; rw [hx, hy]

/-- Restricting an issue-ordered history to a predicate closed under pasts
yields an issue-ordered history. -/
theorem Issued.restrict {ρ : List (Event × Finset Event)} (h : Issued ρ)
    (p : Event × Finset Event → Bool)
    (hp : ∀ x ∈ ρ, p x = true → ∀ z ∈ x.2, ∃ y ∈ ρ, p y = true ∧ y.1 = z) :
    Issued (ρ.filter p) := by
  induction h with
  | nil => exact Issued.nil
  | @snoc ρ e P hr hP hfresh ha ih =>
    have hnew : e ∉ histEvents ρ := fun hm => hfresh (mem_eventTimes_of_mem hm)
    have hold : ∀ x ∈ ρ, p x = true → ∀ z ∈ x.2, ∃ y ∈ ρ, p y = true ∧ y.1 = z := by
      intro x hx hpx z hz
      obtain ⟨y, hy, hpy, hyz⟩ := hp x (List.mem_append_left _ hx) hpx z hz
      rcases List.mem_append.mp hy with hy | hy
      · exact ⟨y, hy, hpy, hyz⟩
      · exfalso
        rw [List.mem_singleton] at hy
        subst hy
        have hez : e = z := hyz
        exact hnew (by rw [hez]; exact hr.past_sub x hx hz)
    rw [List.filter_append, List.filter_singleton]
    by_cases hpe : p (e, P) = true
    · simp only [hpe, cond_true]
      refine Issued.snoc (ih hold) ?_ ?_ ha
      · intro z hz
        obtain ⟨y, hy, hpy, hyz⟩ := hp (e, P) (by simp) hpe z hz
        rcases List.mem_append.mp hy with hy | hy
        · rw [List.mem_toFinset, List.mem_map]
          exact ⟨y, List.mem_filter.mpr ⟨hy, hpy⟩, hyz⟩
        · exfalso
          rw [List.mem_singleton] at hy
          subst hy
          have hez : e = z := hyz
          exact hnew (by rw [hez]; exact hP hz)
      · intro ht
        exact hfresh (eventTimes_mono_subset (histEvents_filter_sub ρ p) ht)
    · have hpe' : p (e, P) = false := Bool.eq_false_iff.mpr hpe
      simp only [hpe', cond_false, List.append_nil]
      exact ih hold

/-! ## Lifting the port's events -/

/-- A port event lifted to the union model at a past: the causal summary is
the past's timestamps. -/
def liftAt (P : Finset Event) (k : MEvent) : Event :=
  (k.1, k.2.1, ⟨eventTimes P, k.2.2.command⟩)

theorem liftAt_action (P : Finset Event) (k : MEvent) : (liftAt P k).action = MEvent.action k := rfl

/-- The inverse of a port event, as the union model computes it from the
target's action and timestamp. -/
def inverseForM (target : MEvent) : Action :=
  match invertAction (MEvent.action target) with
  | .cell u => .cell { u with overwrites := {target.1} }
  | .range u => .range { u with overwrites := {target.1} }
  | other => other

theorem inverseFor_liftAt (P : Finset Event) (k : MEvent) :
    inverseFor (liftAt P k) = inverseForM k := rfl

theorem toM_liftAt {P : Finset Event} {k : MEvent}
    (hk : k.2.2.kills = killsOf P (liftAt P k)) : toM P (liftAt P k) = k := by
  obtain ⟨t, r, ⟨cmd, kills⟩⟩ := k
  unfold toM
  rw [← hk]
  rfl

/-! ## Observers at the canonical state -/

theorem liveTokensOf_canon {P : Finset Event} (hH : HonestHistory P) (a : Axis) (id : StableId) :
    liveTokensOf (canon P) a id = liveAxisTokens P a id := by
  ext t
  unfold liveTokensOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter, canon_tokens, mem_canonTokens' hH] at hx
    obtain ⟨hx, h1, h2⟩ := hx
    rw [← h1, ← h2]
    exact hx
  · intro ht
    refine ⟨(a, id, t), ?_, rfl⟩
    rw [Finset.mem_filter, canon_tokens, mem_canonTokens' hH]
    exact ⟨ht, rfl, rfl⟩

theorem activeCellTimesOf_canon {P : Finset Event} (hp : ∀ e ∈ P, purge? e = none)
    (r c : StableId) : activeCellTimesOf (canon P) r c = activeCellTimes P r c := by
  ext t
  unfold activeCellTimesOf activeCellTimes
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Finset.mem_filter, canon_cells, mem_canonCells] at hv
    obtain ⟨⟨e, he, u, hcu, ho, rfl⟩, h1, h2⟩ := hv
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    rw [Bool.and_eq_true, cellMatches_iff, Bool.not_eq_true', ← cellOverwrittenD2_eq_of_purgeFree hp e]
    exact ⟨⟨u, hcu, h1, h2⟩, ho⟩
  · rintro ⟨e, he, rfl⟩
    rw [Finset.mem_filter, Bool.and_eq_true, cellMatches_iff, Bool.not_eq_true',
      ← cellOverwrittenD2_eq_of_purgeFree hp e] at he
    obtain ⟨he, ⟨u, hcu, h1, h2⟩, ho⟩ := he
    refine ⟨(u.row, u.column, e.1, u.after), ?_, rfl⟩
    rw [Finset.mem_filter, canon_cells, mem_canonCells]
    exact ⟨⟨e, he, u, hcu, ho, rfl⟩, h1, h2⟩

theorem activeRangeTimesOf_canon (P : Finset Event) (id : RangeId) :
    activeRangeTimesOf (canon P) id = activeRangeTimes P id := by
  ext t
  unfold activeRangeTimesOf activeRangeTimes
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Finset.mem_filter, canon_ranges, mem_canonRanges] at hv
    obtain ⟨⟨e, he, u, hcu, ho, rfl⟩, h1⟩ := hv
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    rw [Bool.and_eq_true, rangeMatches_iff, Bool.not_eq_true']
    exact ⟨⟨u, hcu, h1⟩, ho⟩
  · rintro ⟨e, he, rfl⟩
    rw [Finset.mem_filter, Bool.and_eq_true, rangeMatches_iff, Bool.not_eq_true'] at he
    obtain ⟨he, ⟨u, hcu, h1⟩, ho⟩ := he
    refine ⟨(u.id, e.1, u.after), ?_, rfl⟩
    rw [Finset.mem_filter, canon_ranges, mem_canonRanges]
    exact ⟨⟨e, he, u, hcu, ho, rfl⟩, h1⟩

theorem eventTimes_purgeFree {P : Finset Event} (hp : ∀ e ∈ P, purge? e = none) :
    eventTimes P = P.image (·.1) := by
  unfold eventTimes
  rw [Finset.union_eq_left]
  intro t ht
  rw [Finset.mem_biUnion] at ht
  obtain ⟨r, hr, ht⟩ := ht
  rw [hp r hr] at ht
  simp at ht

/-! ## The union model's issuance from the port's -/

theorem metadataValidB_of_cell {P : Finset Event} {e : Event} {u : CellUpdate}
    (hu : e.action = .cell u)
    (h : ∀ t ∈ u.overwrites, t < e.1 ∧ ∃ prior ∈ P, ∃ w : CellUpdate,
      prior.action = .cell w ∧ prior.1 = t ∧ w.row = u.row ∧ w.column = u.column) :
    metadataValidB P e = true := by
  unfold metadataValidB
  simp only [cellUpdate?_eq_some.mpr hu]
  rw [fold_and_eq_true_iff']
  intro t ht
  obtain ⟨hlt, prior, hp, w, hw, hpt, hr, hc⟩ := h t ht
  rw [Bool.and_eq_true, decide_eq_true_eq, fold_or_eq_true_iff']
  refine ⟨hlt, prior, hp, ?_⟩
  simp only [cellUpdate?_eq_some.mpr hw, decide_eq_true_eq]
  exact ⟨hpt, hr, hc⟩

theorem metadataValidB_of_range {P : Finset Event} {e : Event} {u : RangeUpdate}
    (hu : e.action = .range u)
    (h : ∀ t ∈ u.overwrites, t < e.1 ∧ ∃ prior ∈ P, ∃ w : RangeUpdate,
      prior.action = .range w ∧ prior.1 = t ∧ w.id = u.id) :
    metadataValidB P e = true := by
  unfold metadataValidB
  have h1 : cellUpdate? e = none := by simp [cellUpdate?, hu]
  simp only [h1, rangeUpdate?_eq_some.mpr hu]
  rw [fold_and_eq_true_iff']
  intro t ht
  obtain ⟨hlt, prior, hp, w, hw, hpt, hid⟩ := h t ht
  rw [Bool.and_eq_true, decide_eq_true_eq, fold_or_eq_true_iff']
  refine ⟨hlt, prior, hp, ?_⟩
  simp only [rangeUpdate?_eq_some.mpr hw, decide_eq_true_eq]
  exact ⟨hpt, hid⟩

theorem metadataValidB_of_axis {P : Finset Event} {e : Event} {u : AxisUpdate}
    (hu : e.action = .axis u) : metadataValidB P e = true := by
  simp [metadataValidB, cellUpdate?, rangeUpdate?, purge?, hu]

theorem validUndo_of {P : Finset Event} {issuer : Replica} {target : Timestamp}
    {inverse : Action} {z : Event} (hz : z ∈ P) (ht : z.1 = target) (hi : z.2.1 = issuer)
    (hnp : ∀ m, z.action ≠ .purge m) (hinv : inverse = inverseFor z) :
    validUndo P issuer target inverse = true := by
  unfold validUndo
  rw [fold_or_eq_true_iff']
  refine ⟨z, hz, ?_⟩
  cases hza : z.action with
  | purge m => exact absurd hza (hnp m)
  | axis u => simp only [decide_eq_true_eq]; exact ⟨ht, hi, hinv⟩
  | cell u => simp only [decide_eq_true_eq]; exact ⟨ht, hi, hinv⟩
  | range u => simp only [decide_eq_true_eq]; exact ⟨ht, hi, hinv⟩

theorem applicableB_of {e : Event} {P : Finset Event} (hfresh : e.1 ∉ eventTimes P)
    (hseen : e.seen = eventTimes P) (hvalid : metadataValidB P e = true)
    (hdirect : ∀ a, e.2.2.command = .direct a → directApplicable P e.2.1 a = true)
    (hundo : ∀ target inverse, e.2.2.command = .undo target inverse →
      target ∈ e.seen ∧ validUndo P e.2.1 target inverse = true) :
    applicableB e P = true := by
  unfold applicableB
  cases hc : e.2.2.command with
  | direct a =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    exact ⟨⟨⟨hfresh, hseen⟩, hvalid⟩, hdirect a hc⟩
  | undo target inverse =>
    obtain ⟨ht, hv⟩ := hundo target inverse hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    exact ⟨⟨⟨hfresh, hseen⟩, hvalid⟩, ht, hv⟩

/-- The union model's direct guard at an honest purge-free past, from the
port's effect and before-image clauses at the canonical state. -/
theorem directApplicable_of {P : Finset Event} (hH : HonestHistory P)
    (hpf : ∀ z ∈ P, purge? z = none) {e : MEvent} {a : Action} (ha : MEvent.action e = a)
    (hnp : ∀ m, a ≠ .purge m) (heff : mEffect e (canon P)) (hb : mBefore (canon P) a)
    (issuer : Replica) : directApplicable P issuer a = true := by
  unfold mEffect at heff
  rw [ha] at heff
  cases a with
  | axis u =>
    simp only [mBefore] at hb
    unfold directApplicable
    cases hk : u.kind with
    | insert =>
      simp only [hk] at hb ⊢
      obtain ⟨hb1, hb2⟩ := hb
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hb2
      simp only [hp] at heff
      obtain ⟨_, hknown, _⟩ := heff
      have hnk := hknown hk
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
      refine ⟨⟨fun hak => hnk (mem_canonKnown.mpr hak), ?_⟩, ?_⟩
      · rw [hb1]; rfl
      · rw [hp]; rfl
    | move =>
      simp only [hk] at hb ⊢
      obtain ⟨hb1, hb2, hb3⟩ := hb
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hb3
      simp only [hp] at heff
      obtain ⟨_, _, hlive⟩ := heff
      have hl := hlive hk
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨?_, hb2⟩, hb3⟩
      unfold currentAxisPositions
      rw [← mLive_canon, hl, if_pos rfl, ← mPositions_canon]
      exact hb1
    | remove =>
      simp only [hk] at hb ⊢
      obtain ⟨hb1, hb2, hb3⟩ := hb
      simp only [hb3] at heff
      obtain ⟨hl, _⟩ := heff
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨?_, hb2⟩, by rw [hb3]; rfl⟩
      unfold currentAxisPositions
      rw [← mLive_canon, hl, if_pos rfl, ← mPositions_canon]
      exact hb1
    | restore =>
      simp only [hk] at hb
  | cell u =>
    simp only [mBefore] at hb
    obtain ⟨hr, hc, hov, _⟩ := heff
    unfold directApplicable
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [← mLive_canon]; exact hr
    · rw [← mLive_canon]; exact hc
    · rw [← mCellValues_canon hpf]; exact hb
    · rw [← activeCellTimesOf_canon hpf]; exact hov.symm
  | range u =>
    simp only [mBefore] at hb
    obtain ⟨hov, _⟩ := heff
    unfold directApplicable
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rw [← mRangeValues_canon]; exact hb
    · rw [← activeRangeTimesOf_canon]; exact hov.symm
  | purge m => exact absurd rfl (hnp m)

/-- **Issuance transfer.** The lifted event is applicable at an honest,
purge-free past whose times precede it, given the port's guard at the
canonical state and the undo premise. -/
theorem applicable_of_mApplicable {P : Finset Event} {e : MEvent} (hH : HonestHistory P)
    (hpf : ∀ z ∈ P, purge? z = none) (hclock : ∀ t ∈ eventTimes P, t < e.1)
    (hnp : ∀ m, MEvent.action e ≠ .purge m) (happ : mApplicable e (canon P))
    (hundo : ∀ target inverse, e.2.2.command = .undo target inverse →
      ∃ z ∈ P, z.1 = target ∧ z.2.1 = e.2.1 ∧ (∀ m, z.action ≠ .purge m) ∧
        inverse = inverseFor z) :
    applicable (liftAt P e) P := by
  obtain ⟨heff, hbefore⟩ := happ
  have hfresh : (liftAt P e).1 ∉ eventTimes P := fun h => lt_irrefl _ (hclock _ h)
  have hvalid : metadataValidB P (liftAt P e) = true := by
    cases ha : MEvent.action e with
    | axis u =>
      have ha' : (liftAt P e).action = .axis u := ha
      exact metadataValidB_of_axis ha'
    | cell u =>
      have heff' := heff
      unfold mEffect at heff'
      simp only [ha] at heff'
      obtain ⟨_, _, hov, _⟩ := heff'
      have ha' : (liftAt P e).action = .cell u := ha
      apply metadataValidB_of_cell ha'
      intro t ht
      rw [hov, activeCellTimesOf_canon hpf] at ht
      unfold activeCellTimes at ht
      rw [Finset.mem_image] at ht
      obtain ⟨prior, hp, rfl⟩ := ht
      rw [Finset.mem_filter, Bool.and_eq_true, cellMatches_iff] at hp
      obtain ⟨hp, ⟨w, hw, hr, hc⟩, _⟩ := hp
      exact ⟨hclock _ (mem_eventTimes_of_mem hp), prior, hp, w, cellUpdate?_eq_some.mp hw, rfl, hr, hc⟩
    | range u =>
      have heff' := heff
      unfold mEffect at heff'
      simp only [ha] at heff'
      obtain ⟨hov, _⟩ := heff'
      have ha' : (liftAt P e).action = .range u := ha
      apply metadataValidB_of_range ha'
      intro t ht
      rw [hov, activeRangeTimesOf_canon] at ht
      unfold activeRangeTimes at ht
      rw [Finset.mem_image] at ht
      obtain ⟨prior, hp, rfl⟩ := ht
      rw [Finset.mem_filter, Bool.and_eq_true, rangeMatches_iff] at hp
      obtain ⟨hp, ⟨w, hw, hid⟩, _⟩ := hp
      exact ⟨hclock _ (mem_eventTimes_of_mem hp), prior, hp, w, rangeUpdate?_eq_some.mp hw, rfl, hid⟩
    | purge m => exact absurd ha (hnp m)
  have hdirect : ∀ a, (liftAt P e).2.2.command = .direct a →
      directApplicable P (liftAt P e).2.1 a = true := by
    intro a hc
    have hc' : e.2.2.command = .direct a := hc
    have ha : MEvent.action e = a := by
      unfold MEvent.action
      rw [hc']
      rfl
    have hb : mBefore (canon P) a := by
      have h := hbefore
      simp only [hc'] at h
      exact h
    exact directApplicable_of hH hpf ha (fun m h => hnp m (ha ▸ h)) heff hb _
  have hundo' : ∀ target inverse, (liftAt P e).2.2.command = .undo target inverse →
      target ∈ (liftAt P e).seen ∧ validUndo P (liftAt P e).2.1 target inverse = true := by
    intro target inverse hc
    obtain ⟨z, hz, hzt, hzi, hznp, hinv⟩ := hundo target inverse hc
    refine ⟨?_, validUndo_of hz hzt hzi hznp hinv⟩
    show target ∈ eventTimes P
    rw [← hzt]
    exact mem_eventTimes_of_mem hz
  refine ⟨applicableB_of hfresh rfl hvalid hdirect hundo', ?_⟩
  show clockedB (liftAt P e) P = true
  unfold clockedB
  rw [fold_and_eq_true_iff']
  intro t ht
  rw [decide_eq_true_eq]
  exact hclock t ht

/-! ## Executions of the port -/

section Converse

variable {C : Configuration M}

/-- Distinct events of a configuration have distinct timestamps. -/
theorem ts_ne_of_events_M {a b : MEvent} (ha : a ∈ C.events) (hb : b ∈ C.events) (hne : a ≠ b) :
    a.1 ≠ b.1 := by
  obtain ⟨r, s, hrs, hsa⟩ := ha
  obtain ⟨r', s', hrs', hsb⟩ := hb
  exact C.timestamps_distinct hrs hsa hrs' hsb hne

/-- No event of the configuration is a purge. -/
def PurgeFree (C : Configuration M) : Prop :=
  ∀ k ∈ C.events, ∀ m : Purge, MEvent.action k ≠ .purge m

/-- Every undo names an operation of the issuer's causal past, by the same
issuer, whose computed inverse it carries. The materialised state cannot decide
this; the union model decides it against its event set. -/
def UndoHonest (C : Configuration M) : Prop :=
  ∀ e ∈ C.events, ∀ target inverse, e.2.2.command = .undo target inverse →
    ∃ prior ∈ C.events, C.vis prior e ∧ prior.1 = target ∧ prior.2.1 = e.2.1 ∧
      (∀ m : Purge, MEvent.action prior ≠ .purge m) ∧ inverse = inverseForM prior

/-- The mint-time past of an event, as the list `MintHonest` provides. -/
noncomputable def pastList (hmint : MintHonest M mApplicable C) (k : MEvent) : List MEvent :=
  if hk : k ∈ C.events then Classical.choose (hmint k hk) else []

theorem pastList_spec (hmint : MintHonest M mApplicable C) {k : MEvent} (hk : k ∈ C.events) :
    listPermOf (pastList hmint k) {e' ∈ C.events | C.vis e' k} ∧
      respects (pastList hmint k) C.vis ∧
      mApplicable k (applySeq M.toUpdateSig M.init (pastList hmint k)) := by
  unfold pastList
  rw [dif_pos hk]
  exact Classical.choose_spec (hmint k hk)

theorem mem_pastList (hmint : MintHonest M mApplicable C) {k : MEvent} (hk : k ∈ C.events)
    {x : MEvent} : x ∈ pastList hmint k ↔ x ∈ C.events ∧ C.vis x k :=
  (pastList_spec hmint hk).1.2 x

theorem respects_of_sorted {ev : Set MEvent} {l : List MEvent}
    (hl : l.Pairwise fun a b => a.1 ≤ b.1) : respects l (loOn C.replayContext ev) := by
  unfold respects
  refine hl.imp fun {a b} hle hlo => ?_
  exact absurd (C.causal_mono ((m_loOn_iff _ _ _ _).mp hlo).1) (not_lt.mpr hle)

theorem exists_sorted_M (π : List MEvent) :
    ∃ π' : List MEvent, π'.Perm π ∧ π'.Pairwise (fun a b => a.1 ≤ b.1) := by
  refine ⟨π.mergeSort (fun a b => decide (a.1 ≤ b.1)), List.mergeSort_perm _ _, ?_⟩
  have := List.pairwise_mergeSort (le := fun a b : MEvent => decide (a.1 ≤ b.1))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total a.1 b.1) π
  exact this.imp fun h => by simpa using h

/-- The erasure of one paired event. -/
def erase1 (x : Event × Finset Event) : MEvent := toM x.2 x.1

theorem erase_eq_map (ρ : List (Event × Finset Event)) : erase ρ = ρ.map erase1 := rfl

/-- An issue-ordered history aligned with a list of port events: its erasure
is the list, each event is the lift of its erasure at its past, and each past
is the lift of the erasure's mint-time past. -/
structure Aligned (hmint : MintHonest M mApplicable C) (ρ : List (Event × Finset Event))
    (τ : List MEvent) : Prop where
  issued : Issued ρ
  erase_eq : ρ.map erase1 = τ
  lift_eq : ∀ x ∈ ρ, x.1 = liftAt x.2 (erase1 x)
  past_eq : ∀ x ∈ ρ, x.2 =
    histEvents (ρ.filter fun y => decide (erase1 y ∈ pastList hmint (erase1 x)))

theorem Aligned.purgeFree {hmint : MintHonest M mApplicable C} (hpf : PurgeFree C)
    {ρ : List (Event × Finset Event)} {τ : List MEvent} (hA : Aligned hmint ρ τ)
    (hτ : ∀ k ∈ τ, k ∈ C.events) : ∀ z ∈ histEvents ρ, purge? z = none := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_histEvents.mp hz
  cases hp : purge? y.1 with
  | none => rfl
  | some m =>
    exfalso
    have hact : y.1.action = .purge m := purge?_eq_some.mp hp
    have hyτ : erase1 y ∈ τ := by rw [← hA.erase_eq]; exact List.mem_map_of_mem hy
    exact hpf (erase1 y) (hτ _ hyτ) m hact

/-- One step of the alignment: the next event in timestamp order, lifted at
the lift of its mint-time past. -/
theorem aligned_step (hcan : CanonicalConfig C) (hmint : MintHonest M mApplicable C)
    (hpf : PurgeFree C) (hundo : UndoHonest C)
    {Eset : Set MEvent} (hsupp : ∀ a ∈ Eset, a ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ Eset → a ∈ Eset)
    {π' : List MEvent} (hnodup : π'.Nodup) (hsorted : π'.Pairwise fun a b => a.1 ≤ b.1)
    (hmem : ∀ x, x ∈ π' ↔ x ∈ Eset)
    {τ : List MEvent} {e : MEvent} {rest : List MEvent} (hsplit : τ ++ e :: rest = π')
    {ρ : List (Event × Finset Event)} (hA : Aligned hmint ρ τ) :
    Aligned hmint
      (ρ ++ [(liftAt (histEvents (ρ.filter fun y => decide (erase1 y ∈ pastList hmint e))) e,
        histEvents (ρ.filter fun y => decide (erase1 y ∈ pastList hmint e)))])
      (τ ++ [e]) := by
  set ρe := ρ.filter fun y => decide (erase1 y ∈ pastList hmint e) with hρe
  set Pe := histEvents ρe with hPe
  -- position of `e` in the sorted enumeration
  have hπτ : ∀ x ∈ τ, x ∈ π' := fun x hx => by
    rw [← hsplit]; exact List.mem_append_left _ hx
  have heπ : e ∈ π' := by rw [← hsplit]; simp
  have heE : e ∈ C.events := hsupp e ((hmem e).mp heπ)
  have hτE : ∀ x ∈ τ, x ∈ C.events := fun x hx => hsupp x ((hmem x).mp (hπτ x hx))
  have hnd : (τ ++ e :: rest).Nodup := by rw [hsplit]; exact hnodup
  rw [List.nodup_append] at hnd
  have hsort : (τ ++ e :: rest).Pairwise (fun a b => a.1 ≤ b.1) := by
    rw [hsplit]; exact hsorted
  rw [List.pairwise_append] at hsort
  have hτlt : ∀ x ∈ τ, x.1 < e.1 := fun x hx =>
    lt_of_le_of_ne (hsort.2.2 x hx e (by simp))
      (ts_ne_of_events_M (hτE x hx) heE (hnd.2.2 x hx e (by simp)))
  -- the alignment so far
  have hmemτ : ∀ k, k ∈ τ ↔ ∃ y ∈ ρ, erase1 y = k := by
    intro k; rw [← hA.erase_eq, List.mem_map]
  have hρτ : ∀ y ∈ ρ, erase1 y ∈ τ := fun y hy => (hmemτ _).mpr ⟨y, hy, rfl⟩
  have hρE : ∀ y ∈ ρ, erase1 y ∈ C.events := fun y hy => hτE _ (hρτ y hy)
  have hρpf : ∀ z ∈ histEvents ρ, purge? z = none := hA.purgeFree hpf hτE
  have hτ_fresh : e.1 ∉ eventTimes (histEvents ρ) := by
    rw [eventTimes_purgeFree hρpf, Finset.mem_image]
    rintro ⟨z, hz, hzt⟩
    obtain ⟨y, hy, rfl⟩ := mem_histEvents.mp hz
    exact absurd hzt (ne_of_lt (hτlt _ (hρτ y hy)))
  -- the past of `e` lies in the prefix
  have hpast_τ : ∀ k ∈ pastList hmint e, k ∈ τ := by
    intro k hk
    rw [mem_pastList hmint heE] at hk
    have hkπ : k ∈ π' := (hmem k).mpr (hclosed k e hk.2 ((hmem e).mp heπ))
    rw [← hsplit, List.mem_append, List.mem_cons] at hkπ
    rcases hkπ with h | rfl | h
    · exact h
    · exact absurd hk.2 (hcan.vis_irrefl _)
    · exfalso
      have hle : e.1 ≤ k.1 := (List.pairwise_cons.mp hsort.2.1).1 k h
      exact absurd (C.causal_mono hk.2) (not_lt.mpr hle)
  -- the past as a sorted enumeration
  set τe := τ.filter fun k => decide (k ∈ pastList hmint e) with hτe
  have hρe_map : ρe.map erase1 = τe := by
    rw [hτe, ← hA.erase_eq, List.filter_map]
    rfl
  set ev : Set MEvent := {k ∈ C.events | C.vis k e} with hev
  have hτe_mem : ∀ k, k ∈ τe ↔ k ∈ ev := by
    intro k
    rw [hτe, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hk⟩; exact (mem_pastList hmint heE).mp hk
    · intro h
      have hk : k ∈ pastList hmint e := (mem_pastList hmint heE).mpr h
      exact ⟨hpast_τ k hk, hk⟩
  have hτe_perm : listPermOf τe ev := ⟨List.Sublist.nodup List.filter_sublist hnd.1, hτe_mem⟩
  have hτe_sorted : τe.Pairwise (fun a b => a.1 ≤ b.1) :=
    List.Pairwise.sublist List.filter_sublist hsort.1
  have hin : ∀ a ∈ ev, a ∈ C.replayContext.events := fun a ha => ha.1
  have hcl : ∀ a b, C.replayContext.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ ev → a ∈ ev :=
    fun a b hab _ hb => ⟨C.vis_src hab, hcan.vis_trans hab hb.2⟩
  obtain ⟨hp_e, hr_e, happ⟩ := pastList_spec hmint heE
  have hr_e' : respects (pastList hmint e) (loOn C.replayContext ev) :=
    hr_e.imp fun hn hlo => hn ((m_loOn_iff _ _ _ _).mp hlo).1
  have hHon := honest_of_mint hmint
  have hfold : applySeq M.toUpdateSig M.init (pastList hmint e) = applySeq M.toUpdateSig M.init τe :=
    fold_eq_of_enums hHon hcan.vis_irrefl hin hcl hp_e hr_e' hτe_perm (respects_of_sorted hτe_sorted)
  -- the restricted history
  have hρe_issued : Issued ρe := by
    refine hA.issued.restrict _ ?_
    intro x hx hpx z hz
    rw [decide_eq_true_eq, mem_pastList hmint heE] at hpx
    rw [hA.past_eq x hx] at hz
    obtain ⟨y, hy, rfl⟩ := mem_histEvents.mp hz
    rw [List.mem_filter, decide_eq_true_eq, mem_pastList hmint (hρE x hx)] at hy
    refine ⟨y, hy.1, ?_, rfl⟩
    rw [decide_eq_true_eq, mem_pastList hmint heE]
    exact ⟨hy.2.1, hcan.vis_trans hy.2.2 hpx.2⟩
  have hfold_e : applySeq M.toUpdateSig M.init (pastList hmint e) = canon Pe := by
    rw [hfold, ← hρe_map, ← erase_eq_map]
    exact hρe_issued.fold
  have happ' : mApplicable e (canon Pe) := hfold_e ▸ happ
  have hHPe : HonestHistory Pe := hρe_issued.honest
  have hPe_sub : Pe ⊆ histEvents ρ := histEvents_filter_sub ρ _
  have hPe_pf : ∀ z ∈ Pe, purge? z = none := fun z hz => hρpf z (hPe_sub hz)
  have hPe_clock : ∀ t ∈ eventTimes Pe, t < e.1 := by
    intro t ht
    rw [eventTimes_purgeFree hPe_pf, Finset.mem_image] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    obtain ⟨y, hy, rfl⟩ := mem_histEvents.mp hz
    rw [List.mem_filter, decide_eq_true_eq, mem_pastList hmint heE] at hy
    exact C.causal_mono hy.2.2
  have hnp_e : ∀ m, MEvent.action e ≠ .purge m := hpf e heE
  have hundo_e : ∀ target inverse, e.2.2.command = .undo target inverse →
      ∃ z ∈ Pe, z.1 = target ∧ z.2.1 = e.2.1 ∧ (∀ m, z.action ≠ .purge m) ∧
        inverse = inverseFor z := by
    intro target inverse hc
    obtain ⟨prior, hpE, hvis, hpt, hpi, hpnp, hinv⟩ := hundo e heE target inverse hc
    have hpτ : prior ∈ τ := hpast_τ prior ((mem_pastList hmint heE).mpr ⟨hpE, hvis⟩)
    obtain ⟨y, hy, hye⟩ := (hmemτ prior).mp hpτ
    refine ⟨y.1, ?_, ?_, ?_, ?_, ?_⟩
    · refine mem_histEvents.mpr ⟨y, List.mem_filter.mpr ⟨hy, ?_⟩, rfl⟩
      rw [decide_eq_true_eq, hye, mem_pastList hmint heE]
      exact ⟨hpE, hvis⟩
    · rw [← hpt, ← hye]; rfl
    · rw [← hpi, ← hye]; rfl
    · intro m h
      exact hpnp m (by rw [← hye]; exact h)
    · rw [hinv, hA.lift_eq y hy, inverseFor_liftAt, hye]
  have happl : applicable (liftAt Pe e) Pe :=
    applicable_of_mApplicable hHPe hPe_pf hPe_clock hnp_e happ' hundo_e
  -- the erased new event is `e`
  have hkills : e.2.2.kills = killsOf Pe (liftAt Pe e) := by
    obtain ⟨heff, _⟩ := happ'
    unfold mEffect at heff
    unfold killsOf
    rw [liftAt_action]
    cases ha : MEvent.action e with
    | axis u =>
      simp only [ha] at heff
      cases hu : u.after with
      | none =>
        simp only [hu] at heff
        simp only [hu, Option.isNone_none, if_true]
        rw [heff.2, liveTokensOf_canon hHPe]
      | some p =>
        simp only [hu] at heff
        simp only [hu, Option.isNone_some, Bool.false_eq_true, if_false]
        exact heff.1
    | cell u => simp only [ha] at heff; exact heff.2.2.2
    | range u => simp only [ha] at heff; exact heff.2
    | purge m => exact absurd ha (hnp_e m)
  have hnew : erase1 (liftAt Pe e, Pe) = e := toM_liftAt hkills
  have hnot : ∀ k ∈ τ, decide (e ∈ pastList hmint k) = false := by
    intro k hk
    rw [decide_eq_false_iff_not, mem_pastList hmint (hτE k hk)]
    rintro ⟨_, hv⟩
    exact absurd (C.causal_mono hv) (not_lt.mpr (le_of_lt (hτlt k hk)))
  have hself : decide (e ∈ pastList hmint e) = false := by
    rw [decide_eq_false_iff_not, mem_pastList hmint heE]
    rintro ⟨_, hv⟩
    exact hcan.vis_irrefl e hv
  refine ⟨Issued.snoc hA.issued hPe_sub hτ_fresh happl, ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_singleton, hA.erase_eq, hnew]
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hA.lift_eq x hx
    · rw [List.mem_singleton] at hx
      subst hx
      show liftAt Pe e = liftAt Pe (erase1 (liftAt Pe e, Pe))
      rw [hnew]
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.filter_append, List.filter_singleton]
      simp only [hnew, hnot _ (hρτ x hx), cond_false, List.append_nil]
      exact hA.past_eq x hx
    · rw [List.mem_singleton] at hx
      subst hx
      show Pe = histEvents (List.filter
        (fun y => decide (erase1 y ∈ pastList hmint (erase1 (liftAt Pe e, Pe))))
        (ρ ++ [(liftAt Pe e, Pe)]))
      rw [hnew, List.filter_append, List.filter_singleton]
      simp only [hnew, hself, cond_false, List.append_nil]
      rfl

theorem aligned_of_prefix (hcan : CanonicalConfig C) (hmint : MintHonest M mApplicable C)
    (hpf : PurgeFree C) (hundo : UndoHonest C)
    {Eset : Set MEvent} (hsupp : ∀ a ∈ Eset, a ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ Eset → a ∈ Eset)
    {π' : List MEvent} (hnodup : π'.Nodup) (hsorted : π'.Pairwise fun a b => a.1 ≤ b.1)
    (hmem : ∀ x, x ∈ π' ↔ x ∈ Eset) :
    ∀ τ rest, τ ++ rest = π' → ∃ ρ, Aligned hmint ρ τ := by
  intro τ
  induction τ using List.reverseRecOn with
  | nil =>
    intro rest _
    exact ⟨[], ⟨Issued.nil, rfl, fun x hx => absurd hx (List.not_mem_nil),
      fun x hx => absurd hx (List.not_mem_nil)⟩⟩
  | append_singleton τ e ih =>
    intro rest hsplit
    have hsplit' : τ ++ (e :: rest) = π' := by rw [← hsplit]; simp
    obtain ⟨ρ, hA⟩ := ih (e :: rest) hsplit'
    exact ⟨_, aligned_step hcan hmint hpf hundo hsupp hclosed hnodup hsorted hmem hsplit' hA⟩

/-- **The converse cross-model theorem.** For every version of a certified
execution of the port with no purge and honest undo, the version's events are
the erasure of an issue-ordered union-model history, the version's state is
the canonical state of that history, and the materialised observation is the
union model's view of it. -/
theorem converse (hC : CertifiedExecution M generation C) (hpf : PurgeFree C)
    (hundo : UndoHonest C) {v : Version} {s : MState} {Eset : Set MEvent}
    (hv : C.ver v = some (s, Eset)) :
    ∃ ρ : List (Event × Finset Event), Issued ρ ∧ listPermOf (erase ρ) Eset ∧
      (∀ z ∈ histEvents ρ, purge? z = none) ∧ canon (histEvents ρ) = s ∧
      M.query s () = D.query (histEvents ρ) () := by
  have hmint : MintHonest M mApplicable C := hC.mintHonest
  have hcan : CanonicalConfig C := hC.canonicalConfig (fun _ h => m_join_at (honest_of_mint h))
  obtain ⟨π, hperm, hresp, hfold⟩ := hasReplayWitness_of_canonical hcan v s Eset hv
  obtain ⟨π', hp, hsorted⟩ := exists_sorted_M π
  have hnodup : π'.Nodup := hp.nodup_iff.mpr hperm.1
  have hmem : ∀ x, x ∈ π' ↔ x ∈ Eset := fun x => hp.mem_iff.trans (hperm.2 x)
  have hsupp := hcan.version_events_supported v s Eset hv
  have hclosed : ∀ a b, C.vis a b → b ∈ Eset → a ∈ Eset := hcan.version_events_causal v s Eset hv
  obtain ⟨ρ, hA⟩ :=
    aligned_of_prefix hcan hmint hpf hundo hsupp hclosed hnodup hsorted hmem π' [] (by simp)
  have herase : erase ρ = π' := hA.erase_eq
  have hpf' : ∀ z ∈ histEvents ρ, purge? z = none :=
    hA.purgeFree hpf fun k hk => hsupp k ((hmem k).mp hk)
  have hHon := honest_of_mint hmint
  have hcl : ∀ a b, C.replayContext.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ Eset → a ∈ Eset :=
    fun a b hab _ hb => hclosed a b hab hb
  have hresp' : respects π (loOn C.replayContext Eset) :=
    hresp.imp fun hn hlo => hn (Or.inl ((m_loOn_iff _ _ _ _).mp hlo))
  have hfold' : applySeq M.toUpdateSig M.init π' = s := by
    rw [← hfold]
    exact fold_eq_of_enums hHon hcan.vis_irrefl hsupp hcl ⟨hnodup, hmem⟩
      (respects_of_sorted hsorted) hperm hresp'
  have hcanon : canon (histEvents ρ) = s := by
    rw [← hA.issued.fold, herase, hfold']
  refine ⟨ρ, hA.issued, ⟨by rw [herase]; exact hnodup, fun a => by rw [herase]; exact hmem a⟩,
    hpf', hcanon, ?_⟩
  show mview s = view (histEvents ρ)
  rw [← hcanon]
  exact observationEquivalence _ hpf'

end Converse

#print axioms converse

end Sal.MRDTs.Instances.AegisSheet.Materialised
