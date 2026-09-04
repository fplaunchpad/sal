import Sal.MRDTs.Instances.AegisSheetMaterialised

/-!
# Join for the materialised AegisSheet: component theory

The materialised state has two kinds of component. A *named-removal set*
(tokens, cell versions, range versions) is a finite set of entries that events
add, each entry carrying its event's timestamp, and that later events remove by
naming the entry. A *last-writer-wins register* (positions) keeps, per key, the
candidate with the greatest timestamp. `known` is grow-only.

This file develops the named-removal shape once: the canonical content of an
enumeration as a function of its elements, the fold lemma under
well-formedness, the set-level membership characterisation, and the
observed-remove merge identity under honesty and weak closure. The
instantiations and the register follow.
-/

namespace Sal.MRDTs.Instances.AegisSheet.Materialised

open Sal.MRDTs.Foundation

/-! ## Named-removal components -/

/-- A named-removal component over entry type `α`. `adds e` are the entries
`e` contributes, each with `ts x = e.1`; `removes r x` says `r` names `x`. -/
structure NR (α : Type) where
  adds : MEvent → List α
  removes : MEvent → α → Bool
  ts : α → Timestamp
  ts_adds : ∀ e x, x ∈ adds e → ts x = e.1

variable {α : Type} [DecidableEq α] (N : NR α)

/-- One update step on the component. -/
def NR.step (s : Finset α) (e : MEvent) : Finset α :=
  (s.filter fun x => N.removes e x = false) ∪ (N.adds e).toFinset

/-- The canonical content of an enumeration: entries added by some element and
named by none. -/
def NR.canonL (ρ : List MEvent) : Finset α :=
  (ρ.flatMap N.adds).toFinset.filter fun x => ∀ r ∈ ρ, N.removes r x = false

theorem NR.mem_canonL {ρ : List MEvent} {x : α} :
    x ∈ N.canonL ρ ↔ (∃ e ∈ ρ, x ∈ N.adds e) ∧ ∀ r ∈ ρ, N.removes r x = false := by
  simp [NR.canonL, List.mem_flatMap]

/-- Well-formed enumerations: timestamps are unique and every removal names
an entry added strictly earlier. -/
structure NR.Wf (ρ : List MEvent) : Prop where
  ts_nodup : (ρ.map Prod.fst).Nodup
  names_earlier : ∀ (l₁ : List MEvent) (r : MEvent), l₁ ++ [r] <+: ρ →
    ∀ x, (∃ e ∈ ρ, x ∈ N.adds e) → N.removes r x = true → ∃ e ∈ l₁, x ∈ N.adds e

theorem NR.Wf.prefix {ρ : List MEvent} {e : MEvent} (h : N.Wf (ρ ++ [e])) : N.Wf ρ := by
  refine ⟨?_, ?_⟩
  · have := h.ts_nodup
    rw [List.map_append] at this
    exact (List.nodup_append.mp this).1
  · intro l₁ r hpre x ⟨e', he', hxe'⟩ hx
    exact h.names_earlier l₁ r (hpre.trans (List.prefix_append ρ [e])) x
      ⟨e', List.mem_append_left _ he', hxe'⟩ hx

/-- Distinct elements of a timestamp-nodup enumeration have distinct
timestamps. -/
theorem ts_inj_of_nodup {ρ : List MEvent} (h : (ρ.map Prod.fst).Nodup)
    {a b : MEvent} (ha : a ∈ ρ) (hb : b ∈ ρ) (hab : a.1 = b.1) : a = b :=
  List.inj_on_of_nodup_map h ha hb hab

/-- In a well-formed enumeration, nothing before `e` (nor `e` itself) names an
entry that `e` adds. -/
theorem NR.Wf.fresh_last {ρ : List MEvent} {e : MEvent} (h : N.Wf (ρ ++ [e])) :
    ∀ r ∈ ρ ++ [e], ∀ x ∈ N.adds e, N.removes r x = false := by
  intro r hr x hx
  by_contra hne
  have hrem : N.removes r x = true := by simpa using hne
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hr
  have hpre : l₁ ++ [r] <+: ρ ++ [e] := ⟨l₂, by rw [hsplit]; simp⟩
  obtain ⟨e', he', hxe'⟩ := h.names_earlier l₁ r hpre x
    ⟨e, List.mem_append_right _ (List.mem_singleton_self e), hx⟩ hrem
  have hts : e'.1 = e.1 := by rw [← N.ts_adds e' x hxe', N.ts_adds e x hx]
  have hmem_e' : e' ∈ ρ ++ [e] := hpre.subset (List.mem_append_left _ he')
  have hee' : e' = e :=
    ts_inj_of_nodup h.ts_nodup hmem_e' (List.mem_append_right _ (by simp)) hts
  subst hee'
  have hnd : (ρ ++ [e']).Nodup := List.Nodup.of_map _ h.ts_nodup
  have hdisj := List.disjoint_of_nodup_append hnd
  have hl₁ : l₁ ⊆ ρ := by
    rcases List.prefix_concat_iff.mp hpre with heq | hpre'
    · obtain ⟨hl, _⟩ := List.append_inj' heq rfl
      rw [hl]
      exact fun _ hm => hm
    · exact ((List.prefix_append l₁ [r]).trans hpre').subset
  exact hdisj (hl₁ he') (List.mem_singleton_self e')

/-- Appending one element to a well-formed enumeration applies one step. -/
theorem NR.canonL_snoc {ρ : List MEvent} {e : MEvent} (h : N.Wf (ρ ++ [e])) :
    N.canonL (ρ ++ [e]) = N.step (N.canonL ρ) e := by
  have hfresh := h.fresh_last
  ext x
  rw [NR.mem_canonL]
  simp only [NR.step, Finset.mem_union, Finset.mem_filter, List.mem_toFinset, NR.mem_canonL,
    List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨⟨e', he', hx⟩, hnone⟩
    rcases he' with he' | rfl
    · left
      exact ⟨⟨⟨e', he', hx⟩, fun r hr => hnone r (Or.inl hr)⟩, hnone e (Or.inr rfl)⟩
    · right; exact hx
  · rintro (⟨⟨⟨e', he', hx⟩, hnone⟩, hlast⟩ | hx)
    · refine ⟨⟨e', Or.inl he', hx⟩, ?_⟩
      rintro r (hr | rfl)
      · exact hnone r hr
      · exact hlast
    · refine ⟨⟨e, Or.inr rfl, hx⟩, ?_⟩
      rintro r (hr | heq)
      · exact hfresh r (List.mem_append_left _ hr) x hx
      · exact heq ▸ hfresh e (List.mem_append_right _ (List.mem_singleton_self e)) x hx

/-- The fold lemma: if a projection of the state advances by `step`, then
over a well-formed enumeration its fold from the empty state is the canonical
content. -/
theorem NR.fold_canon (proj : MState → Finset α)
    (hinit : proj MState.empty = ∅)
    (hstep : ∀ s e, proj (mupdate s e) = N.step (proj s) e) :
    ∀ ρ : List MEvent, N.Wf ρ → proj (applySeq M.toUpdateSig M.init ρ) = N.canonL ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro _; simpa [applySeq, M, NR.canonL] using hinit
  | append_singleton ρ e ih =>
    intro h
    have hstep' : applySeq M.toUpdateSig M.init (ρ ++ [e])
        = mupdate (applySeq M.toUpdateSig M.init ρ) e := by
      unfold applySeq
      rw [List.foldl_append]
      rfl
    rw [hstep', hstep, ih h.prefix, N.canonL_snoc h]

/-! ### Set level -/

/-- Membership in the canonical content of an event set. -/
def NR.inSet (ev : Set MEvent) (x : α) : Prop :=
  (∃ e ∈ ev, x ∈ N.adds e) ∧ ∀ r ∈ ev, N.removes r x = false

theorem NR.mem_canonL_perm {ρ : List MEvent} {ev : Set MEvent} (hperm : listPermOf ρ ev)
    {x : α} : x ∈ N.canonL ρ ↔ N.inSet ev x := by
  rw [NR.mem_canonL, NR.inSet]
  constructor
  · rintro ⟨⟨e, he, hx⟩, hnone⟩
    exact ⟨⟨e, (hperm.2 e).mp he, hx⟩, fun r hr => hnone r ((hperm.2 r).mpr hr)⟩
  · rintro ⟨⟨e, he, hx⟩, hnone⟩
    exact ⟨⟨e, (hperm.2 e).mpr he, hx⟩, fun r hr => hnone r ((hperm.2 r).mp hr)⟩

/-- Honesty of a replay context for one component: every named entry was added
`vis`-before the naming event, adders are unique per entry, and an adder does
not commute with a namer of its entry. -/
structure NR.HonestFor (C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig) : Prop where
  named_seen : ∀ r ∈ C.events, ∀ e ∈ C.events, ∀ x, x ∈ N.adds e →
    N.removes r x = true → C.vis e r
  adder_unique : ∀ e ∈ C.events, ∀ e' ∈ C.events, ∀ x, x ∈ N.adds e → x ∈ N.adds e' → e = e'
  not_comm : ∀ e ∈ C.events, ∀ r ∈ C.events, e ≠ r → ∀ x, x ∈ N.adds e →
    N.removes r x = true → ¬ M.toUpdateSig.commutes e r

/-- Non-commutation of an adder with a namer of its entry, from the step
lemma: witnessed at the empty state. -/
theorem NR.not_comm_of_step (proj : MState → Finset α)
    (hinit : proj MState.empty = ∅)
    (hstep : ∀ s e, proj (mupdate s e) = N.step (proj s) e)
    {e r : MEvent} {x : α} (hx : x ∈ N.adds e) (hr : N.removes r x = true)
    (hxr : x ∉ N.adds r) : ¬ M.toUpdateSig.commutes e r := by
  intro hc
  have h := congrArg proj (hc MState.empty)
  change proj (mupdate (mupdate MState.empty e) r) = proj (mupdate (mupdate MState.empty r) e) at h
  rw [hstep, hstep, hstep, hstep, hinit] at h
  have h1 : x ∉ N.step (N.step ∅ e) r := by
    simp [NR.step, hr, hxr]
  have h2 : x ∈ N.step (N.step ∅ r) e := by
    simp [NR.step, hx]
  exact h1 (h ▸ h2)

/-- **The observed-remove merge identity** for one component: the canonical
content of the union is `mvr` of the contents of the intersection and the
two sides, at any honest context with weakly closed sides. -/
theorem NR.inSet_union_iff {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig}
    (hHon : N.HonestFor C) (hir : ∀ a : MEvent, ¬ C.vis a a) {ev₁ ev₂ : Set MEvent}
    (hin₁ : ∀ a ∈ ev₁, a ∈ C.events) (hin₂ : ∀ a ∈ ev₂, a ∈ C.events)
    (hcl₁ : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl₂ : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (x : α) :
    N.inSet (ev₁ ∪ ev₂) x ↔
      (N.inSet (ev₁ ∩ ev₂) x ∧ N.inSet ev₁ x ∧ N.inSet ev₂ x) ∨
      (N.inSet ev₁ x ∧ ¬ N.inSet (ev₁ ∩ ev₂) x) ∨
      (N.inSet ev₂ x ∧ ¬ N.inSet (ev₁ ∩ ev₂) x) := by
  constructor
  · rintro ⟨⟨e, he, hx⟩, hnone⟩
    have hn₁ : ∀ r ∈ ev₁, N.removes r x = false := fun r hr => hnone r (Or.inl hr)
    have hn₂ : ∀ r ∈ ev₂, N.removes r x = false := fun r hr => hnone r (Or.inr hr)
    have hn₀ : ∀ r ∈ ev₁ ∩ ev₂, N.removes r x = false := fun r hr => hn₁ r hr.1
    -- the adder is unique in C.events
    have huniq : ∀ e' ∈ ev₁ ∪ ev₂, x ∈ N.adds e' → e' = e := by
      intro e' he' hx'
      have hce : e ∈ C.events := by
        rcases he with h | h
        · exact hin₁ e h
        · exact hin₂ e h
      have hce' : e' ∈ C.events := by
        rcases he' with h | h
        · exact hin₁ e' h
        · exact hin₂ e' h
      exact hHon.adder_unique e' hce' e hce x hx' hx
    by_cases h1 : e ∈ ev₁ <;> by_cases h2 : e ∈ ev₂
    · left
      exact ⟨⟨⟨e, ⟨h1, h2⟩, hx⟩, hn₀⟩, ⟨⟨e, h1, hx⟩, hn₁⟩, ⟨⟨e, h2, hx⟩, hn₂⟩⟩
    · right; left
      refine ⟨⟨⟨e, h1, hx⟩, hn₁⟩, ?_⟩
      rintro ⟨⟨e', he', hx'⟩, _⟩
      have := huniq e' (Or.inl he'.1) hx'
      subst this
      exact h2 he'.2
    · right; right
      refine ⟨⟨⟨e, h2, hx⟩, hn₂⟩, ?_⟩
      rintro ⟨⟨e', he', hx'⟩, _⟩
      have := huniq e' (Or.inr he'.2) hx'
      subst this
      exact h1 he'.1
    · exfalso
      rcases he with h | h
      · exact h1 h
      · exact h2 h
  · -- from the three-way membership to the union
    have key : ∀ {evA evB : Set MEvent},
        (∀ a ∈ evA, a ∈ C.events) → (∀ a ∈ evB, a ∈ C.events) →
        (∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ evB → a ∈ evB) →
        N.inSet evA x → ¬ N.inSet (evA ∩ evB) x →
        ∀ r ∈ evB, N.removes r x = false := by
      intro evA evB hinA hinB hclB hA hnot r hr
      by_contra hne
      have hrem : N.removes r x = true := by simpa using hne
      obtain ⟨⟨e, he, hx⟩, hnoneA⟩ := hA
      have hvis : C.vis e r := hHon.named_seen r (hinB r hr) e (hinA e he) x hx hrem
      have hne : e ≠ r := fun h => hir r (h ▸ hvis)
      have heB : e ∈ evB := hclB e r hvis (hHon.not_comm e (hinA e he) r (hinB r hr) hne x hx hrem) hr
      apply hnot
      refine ⟨⟨e, ⟨he, heB⟩, hx⟩, ?_⟩
      intro r' hr'
      exact hnoneA r' hr'.1
    rintro (⟨_, ⟨⟨e, he, hx⟩, hn₁⟩, ⟨_, hn₂⟩⟩ | ⟨hA, hnot⟩ | ⟨hB, hnot⟩)
    · refine ⟨⟨e, Or.inl he, hx⟩, ?_⟩
      rintro r (hr | hr)
      · exact hn₁ r hr
      · exact hn₂ r hr
    · obtain ⟨⟨e, he, hx⟩, hn₁⟩ := hA
      refine ⟨⟨e, Or.inl he, hx⟩, ?_⟩
      rintro r (hr | hr)
      · exact hn₁ r hr
      · exact key hin₁ hin₂ hcl₂ ⟨⟨e, he, hx⟩, hn₁⟩ hnot r hr
    · obtain ⟨⟨e, he, hx⟩, hn₂⟩ := hB
      refine ⟨⟨e, Or.inr he, hx⟩, ?_⟩
      rintro r (hr | hr)
      · have hnot' : ¬ N.inSet (ev₂ ∩ ev₁) x := by
          intro h; apply hnot
          obtain ⟨⟨e', he', hx'⟩, hn⟩ := h
          exact ⟨⟨e', ⟨he'.2, he'.1⟩, hx'⟩, fun r' hr' => hn r' ⟨hr'.2, hr'.1⟩⟩
        exact key hin₂ hin₁ hcl₁ ⟨⟨e, he, hx⟩, hn₂⟩ hnot' r hr
      · exact hn₂ r hr

/-- The merge identity on finite contents: with `mvr` on the canonical
contents of well-formed enumerations of the intersection and the sides, the
result is the canonical content of any enumeration of the union. -/
theorem NR.mvr_canonL {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig}
    (hHon : N.HonestFor C) (hir : ∀ a : MEvent, ¬ C.vis a a) {ev₁ ev₂ : Set MEvent}
    (hin₁ : ∀ a ∈ ev₁, a ∈ C.events) (hin₂ : ∀ a ∈ ev₂, a ∈ C.events)
    (hcl₁ : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl₂ : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    {ρ₀ ρ₁ ρ₂ ρU : List MEvent}
    (hp₀ : listPermOf ρ₀ (ev₁ ∩ ev₂)) (hp₁ : listPermOf ρ₁ ev₁) (hp₂ : listPermOf ρ₂ ev₂)
    (hpU : listPermOf ρU (ev₁ ∪ ev₂)) :
    N.canonL ρU = mvr (N.canonL ρ₀) (N.canonL ρ₁) (N.canonL ρ₂) := by
  ext x
  rw [N.mem_canonL_perm hpU, N.inSet_union_iff hHon hir hin₁ hin₂ hcl₁ hcl₂]
  simp only [mvr, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
    N.mem_canonL_perm hp₀, N.mem_canonL_perm hp₁, N.mem_canonL_perm hp₂, and_assoc, or_assoc]

/-! ## Instantiation: keep tokens -/

def tokAdds (e : MEvent) : List TokenEntry :=
  match MEvent.action e with
  | .axis u => if u.after.isSome then [(u.axis, u.id, e.1)] else []
  | .cell u => [(Axis.row, u.row, e.1), (Axis.column, u.column, e.1)]
  | _ => []

def tokRemoves (r : MEvent) (x : TokenEntry) : Bool :=
  match MEvent.action r with
  | .axis u => decide (u.after = none ∧ x.1 = u.axis ∧ x.2.1 = u.id ∧ x.2.2 ∈ r.2.2.kills)
  | _ => false

theorem tokAdds_ts (e : MEvent) (x : TokenEntry) (hx : x ∈ tokAdds e) : x.2.2 = e.1 := by
  unfold tokAdds at hx
  split at hx
  · split at hx
    · simp at hx; subst hx; rfl
    · simp at hx
  · simp at hx; rcases hx with rfl | rfl <;> rfl
  · simp at hx

def tokNR : NR TokenEntry where
  adds := tokAdds
  removes := tokRemoves
  ts := fun x => x.2.2
  ts_adds := tokAdds_ts

theorem tokens_init : MState.tokens MState.empty = ∅ := rfl

theorem tokens_step (s : MState) (e : MEvent) :
    (mupdate s e).tokens = tokNR.step s.tokens e := by
  unfold mupdate NR.step tokNR tokAdds tokRemoves
  cases h : MEvent.action e with
  | axis u =>
    cases hu : u.after with
    | some p =>
      ext x
      simp [h, hu, or_comm]
    | none =>
      ext x
      simp [h, hu]
  | cell u =>
    ext x
    simp [h]
  | range u => ext x; simp [h]
  | purge m => ext x; simp [h]

/-! ## Instantiation: cell versions (D2 purge) -/

def cellAdds (e : MEvent) : List CellEntry :=
  match MEvent.action e with
  | .cell u => [(u.row, u.column, e.1, u.after)]
  | _ => []

def cellRemoves (r : MEvent) (x : CellEntry) : Bool :=
  match MEvent.action r with
  | .cell w => decide (x.1 = w.row ∧ x.2.1 = w.column ∧ x.2.2.1 ∈ w.overwrites)
  | .purge m => decide ((x.2.2.1, (x.1, x.2.1)) ∈ m.covered)
  | _ => false

theorem cellAdds_ts (e : MEvent) (x : CellEntry) (hx : x ∈ cellAdds e) : x.2.2.1 = e.1 := by
  unfold cellAdds at hx
  split at hx
  · simp at hx; subst hx; rfl
  · simp at hx

def cellNR : NR CellEntry where
  adds := cellAdds
  removes := cellRemoves
  ts := fun x => x.2.2.1
  ts_adds := cellAdds_ts

theorem cells_init : MState.cells MState.empty = ∅ := rfl

theorem cells_step (s : MState) (e : MEvent) :
    (mupdate s e).cells = cellNR.step s.cells e := by
  unfold mupdate NR.step cellNR cellAdds cellRemoves
  cases h : MEvent.action e with
  | axis u =>
    cases hu : u.after with
    | some p => ext x; simp [h, hu]
    | none => ext x; simp [h, hu]
  | cell u => ext x; simp [h, or_comm]
  | range u => ext x; simp [h]
  | purge m => ext x; simp [h]

/-! ## Instantiation: range versions -/

def rangeAdds (e : MEvent) : List RangeEntry :=
  match MEvent.action e with
  | .range u => [(u.id, e.1, u.after)]
  | _ => []

def rangeRemoves (r : MEvent) (x : RangeEntry) : Bool :=
  match MEvent.action r with
  | .range w => decide (x.1 = w.id ∧ x.2.1 ∈ w.overwrites)
  | _ => false

theorem rangeAdds_ts (e : MEvent) (x : RangeEntry) (hx : x ∈ rangeAdds e) : x.2.1 = e.1 := by
  unfold rangeAdds at hx
  split at hx
  · simp at hx; subst hx; rfl
  · simp at hx

def rangeNR : NR RangeEntry where
  adds := rangeAdds
  removes := rangeRemoves
  ts := fun x => x.2.1
  ts_adds := rangeAdds_ts

theorem ranges_init : MState.ranges MState.empty = ∅ := rfl

theorem ranges_step (s : MState) (e : MEvent) :
    (mupdate s e).ranges = rangeNR.step s.ranges e := by
  unfold mupdate NR.step rangeNR rangeAdds rangeRemoves
  cases h : MEvent.action e with
  | axis u =>
    cases hu : u.after with
    | some p => ext x; simp [h, hu]
    | none => ext x; simp [h, hu]
  | cell u => ext x; simp [h]
  | range u => ext x; simp [h, or_comm]
  | purge m => ext x; simp [h]

/-! ## The grow-only `known` component -/

def knownAdds (e : MEvent) : List (Axis × StableId) :=
  match MEvent.action e with
  | .axis u => [(u.axis, u.id)]
  | _ => []

def knownL (ρ : List MEvent) : Finset (Axis × StableId) := (ρ.flatMap knownAdds).toFinset

theorem mem_knownL {ρ : List MEvent} {k : Axis × StableId} :
    k ∈ knownL ρ ↔ ∃ e ∈ ρ, k ∈ knownAdds e := by
  simp [knownL, List.mem_flatMap]

theorem known_step (s : MState) (e : MEvent) :
    (mupdate s e).known = s.known ∪ (knownAdds e).toFinset := by
  unfold mupdate knownAdds
  cases h : MEvent.action e with
  | axis u =>
    cases hu : u.after with
    | some p => ext x; simp [h, hu, or_comm]
    | none => ext x; simp [h, hu, or_comm]
  | cell u => ext x; simp [h]
  | range u => ext x; simp [h]
  | purge m => ext x; simp [h]

theorem knownL_snoc (ρ : List MEvent) (e : MEvent) :
    knownL (ρ ++ [e]) = knownL ρ ∪ (knownAdds e).toFinset := by
  ext k
  simp only [mem_knownL, List.mem_append, List.mem_singleton, Finset.mem_union,
    List.mem_toFinset]
  constructor
  · rintro ⟨e', he' | heq, hk⟩
    · exact Or.inl ⟨e', he', hk⟩
    · exact Or.inr (heq ▸ hk)
  · rintro (⟨e', he', hk⟩ | hk)
    · exact ⟨e', Or.inl he', hk⟩
    · exact ⟨e, Or.inr rfl, hk⟩

theorem known_fold : ∀ ρ : List MEvent,
    (applySeq M.toUpdateSig M.init ρ).known = knownL ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ e ih =>
    have hstep' : applySeq M.toUpdateSig M.init (ρ ++ [e])
        = mupdate (applySeq M.toUpdateSig M.init ρ) e := by
      unfold applySeq
      rw [List.foldl_append]
      rfl
    rw [hstep', known_step, ih, knownL_snoc]

theorem mem_knownL_perm {ρ : List MEvent} {ev : Set MEvent} (hperm : listPermOf ρ ev)
    {k : Axis × StableId} : k ∈ knownL ρ ↔ ∃ e ∈ ev, k ∈ knownAdds e := by
  rw [mem_knownL]
  constructor
  · rintro ⟨e, he, hk⟩; exact ⟨e, (hperm.2 e).mp he, hk⟩
  · rintro ⟨e, he, hk⟩; exact ⟨e, (hperm.2 e).mpr he, hk⟩

/-- `known` of the union is the union of the sides' `known` (the base's is
contained in both). -/
theorem knownL_union {ev₁ ev₂ : Set MEvent} {ρ₀ ρ₁ ρ₂ ρU : List MEvent}
    (hp₀ : listPermOf ρ₀ (ev₁ ∩ ev₂)) (hp₁ : listPermOf ρ₁ ev₁) (hp₂ : listPermOf ρ₂ ev₂)
    (hpU : listPermOf ρU (ev₁ ∪ ev₂)) :
    knownL ρU = knownL ρ₀ ∪ knownL ρ₁ ∪ knownL ρ₂ := by
  ext k
  simp only [Finset.mem_union, mem_knownL_perm hpU, mem_knownL_perm hp₀, mem_knownL_perm hp₁,
    mem_knownL_perm hp₂]
  constructor
  · rintro ⟨e, he | he, hk⟩
    · exact Or.inl (Or.inr ⟨e, he, hk⟩)
    · exact Or.inr ⟨e, he, hk⟩
  · rintro ((⟨e, he, hk⟩ | ⟨e, he, hk⟩) | ⟨e, he, hk⟩)
    · exact ⟨e, Or.inl he.1, hk⟩
    · exact ⟨e, Or.inl he, hk⟩
    · exact ⟨e, Or.inr he, hk⟩

/-! ## The last-writer-wins position register -/

/-- The position candidate an event contributes, if any. -/
def posCand (e : MEvent) : Option PosEntry :=
  match MEvent.action e with
  | .axis u =>
      match u.after with
      | some p => some (u.axis, u.id, e.1, p)
      | none => none
  | _ => none

theorem posCand_ts {e : MEvent} {x : PosEntry} (h : posCand e = some x) : posTs x = e.1 := by
  unfold posCand at h
  split at h
  · split at h
    · simp at h; subst h; rfl
    · simp at h
  · simp at h

/-- All candidates of an enumeration. -/
def cands (ρ : List MEvent) : Finset PosEntry := (ρ.filterMap posCand).toFinset

theorem mem_cands {ρ : List MEvent} {x : PosEntry} :
    x ∈ cands ρ ↔ ∃ e ∈ ρ, posCand e = some x := by
  simp [cands, List.mem_filterMap]

/-- The register content: candidates with no later candidate for their key. -/
def posL (ρ : List MEvent) : Finset PosEntry :=
  (cands ρ).filter fun x => ∀ y ∈ cands ρ, posKey y = posKey x → posTs y ≤ posTs x

theorem mem_posL {ρ : List MEvent} {x : PosEntry} :
    x ∈ posL ρ ↔ x ∈ cands ρ ∧ ∀ y ∈ cands ρ, posKey y = posKey x → posTs y ≤ posTs x := by
  simp [posL]

theorem pos_step (s : MState) (e : MEvent) :
    (mupdate s e).pos = match posCand e with
      | some x => posInsert s.pos x.1 x.2.1 (posTs x) (posVal x)
      | none => s.pos := by
  unfold mupdate posCand
  cases h : MEvent.action e with
  | axis u =>
    cases hu : u.after with
    | some p => simp [h, hu, posTs, posVal]
    | none => simp [h, hu]
  | cell u => simp [h]
  | range u => simp [h]
  | purge m => simp [h]

theorem cands_snoc (ρ : List MEvent) (e : MEvent) :
    cands (ρ ++ [e]) = cands ρ ∪ (posCand e).toList.toFinset := by
  ext x
  simp only [mem_cands, List.mem_append, List.mem_singleton, Finset.mem_union,
    List.mem_toFinset, Option.mem_toList, Option.mem_def]
  constructor
  · rintro ⟨e', he' | heq, hx⟩
    · exact Or.inl ⟨e', he', hx⟩
    · exact Or.inr (heq ▸ hx)
  · rintro (⟨e', he', hx⟩ | hx)
    · exact ⟨e', Or.inl he', hx⟩
    · exact ⟨e, Or.inr rfl, hx⟩

/-- A key with a candidate has a maximal candidate, which lies in the
register. -/
theorem exists_max_cand {ρ : List MEvent} {k : Axis × StableId}
    (h : ∃ c ∈ cands ρ, posKey c = k) : ∃ m ∈ posL ρ, posKey m = k := by
  classical
  obtain ⟨c, hc, hck⟩ := h
  have hne : ((cands ρ).filter fun y => posKey y = k).Nonempty :=
    ⟨c, Finset.mem_filter.mpr ⟨hc, hck⟩⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ posTs hne
  rw [Finset.mem_filter] at hm
  refine ⟨m, ?_, hm.2⟩
  rw [mem_posL]
  refine ⟨hm.1, fun y hy hky => ?_⟩
  exact hmax y (Finset.mem_filter.mpr ⟨hy, hky.trans hm.2⟩)

/-- Appending one element advances the register by `posInsert`. -/
theorem posL_snoc {ρ : List MEvent} {e : MEvent}
    (hnd : ((ρ ++ [e]).map Prod.fst).Nodup) :
    posL (ρ ++ [e]) = match posCand e with
      | some z => posInsert (posL ρ) z.1 z.2.1 (posTs z) (posVal z)
      | none => posL ρ := by
  cases hz : posCand e with
  | none =>
    have hC : cands (ρ ++ [e]) = cands ρ := by
      rw [cands_snoc, hz]; simp
    unfold posL; rw [hC]
  | some z =>
    have hC : cands (ρ ++ [e]) = insert z (cands ρ) := by
      rw [cands_snoc, hz]
      ext w; simp [or_comm]
    have hz_ts : posTs z = e.1 := posCand_ts hz
    have hfresh : ∀ c ∈ cands ρ, posTs c ≠ posTs z := by
      intro c hc heq
      obtain ⟨e', he', hce'⟩ := mem_cands.mp hc
      have h1 : e'.1 = e.1 := by rw [← posCand_ts hce', heq, hz_ts]
      have hee : e' = e := ts_inj_of_nodup hnd (List.mem_append_left _ he')
        (List.mem_append_right _ (List.mem_singleton_self e)) h1
      have hnd' : (ρ ++ [e]).Nodup := List.Nodup.of_map _ hnd
      exact (List.disjoint_of_nodup_append hnd') (hee ▸ he') (List.mem_singleton_self e)
    have hkey : posKey z = (z.1, z.2.1) := rfl
    show posL (ρ ++ [e]) = posInsert (posL ρ) z.1 z.2.1 (posTs z) (posVal z)
    unfold posInsert
    split_ifs with hlater
    · obtain ⟨y, hy, hyk, hyt⟩ := hlater
      have hy' := (mem_posL.mp hy)
      ext x
      rw [mem_posL, mem_posL, hC]
      simp only [Finset.mem_insert]
      constructor
      · rintro ⟨hx | hx, hmax⟩
        · exfalso
          have := hmax y (Or.inr hy'.1) (by rw [hx, hkey]; exact hyk)
          rw [hx] at this
          exact absurd this (not_le.mpr hyt)
        · exact ⟨hx, fun w hw hwk => hmax w (Or.inr hw) hwk⟩
      · rintro ⟨hx, hmax⟩
        refine ⟨Or.inr hx, ?_⟩
        rintro w (hw | hw) hwk
        · subst hw
          have hyx : posTs y ≤ posTs x := hmax y hy'.1 (by rw [hyk, ← hkey]; exact hwk)
          exact le_of_lt (lt_of_lt_of_le hyt hyx)
        · exact hmax w hw hwk
    · have hall : ∀ c ∈ cands ρ, posKey c = posKey z → posTs c < posTs z := by
        intro c hc hck
        rcases lt_or_ge (posTs c) (posTs z) with hlt | hge
        · exact hlt
        · exfalso
          have hgt : posTs z < posTs c := lt_of_le_of_ne hge (fun h => hfresh c hc h.symm)
          obtain ⟨m, hm, hmk⟩ := exists_max_cand ⟨c, hc, hck⟩
          have hm' := mem_posL.mp hm
          have hmc : posTs c ≤ posTs m := hm'.2 c hc (hck.trans hmk.symm)
          exact hlater ⟨m, hm, by rw [hmk, hkey], lt_of_lt_of_le hgt hmc⟩
      have hz_eta : (z.1, z.2.1, posTs z, posVal z) = z := rfl
      rw [hz_eta]
      ext x
      rw [mem_posL, hC]
      simp only [Finset.mem_insert, Finset.mem_filter, mem_posL]
      constructor
      · rintro ⟨hx | hx, hmax⟩
        · exact Or.inl hx
        · right
          have hxk : posKey x ≠ (z.1, z.2.1) := by
            intro hk
            have h1 := hmax z (Or.inl rfl) (by rw [hkey]; exact hk.symm)
            have h2 := hall x hx (by rw [hk, hkey])
            exact absurd h1 (not_le.mpr h2)
          exact ⟨⟨hx, fun w hw hwk => hmax w (Or.inr hw) hwk⟩, hxk⟩
      · rintro (hx | ⟨⟨hx, hmax⟩, hxk⟩)
        · subst hx
          refine ⟨Or.inl rfl, ?_⟩
          rintro w (hw | hw) hwk
          · subst hw; exact le_refl _
          · exact le_of_lt (hall w hw hwk)
        · refine ⟨Or.inr hx, ?_⟩
          rintro w (hw | hw) hwk
          · subst hw
            exact absurd (by rw [← hwk, hkey]) hxk
          · exact hmax w hw hwk

theorem pos_fold : ∀ ρ : List MEvent, (ρ.map Prod.fst).Nodup →
    (applySeq M.toUpdateSig M.init ρ).pos = posL ρ := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil => intro _; simp [applySeq, M, MState.empty, posL, cands]
  | append_singleton ρ e ih =>
    intro hnd
    have hnd' : (ρ.map Prod.fst).Nodup := by
      rw [List.map_append] at hnd; exact (List.nodup_append.mp hnd).1
    have hstep' : applySeq M.toUpdateSig M.init (ρ ++ [e])
        = mupdate (applySeq M.toUpdateSig M.init ρ) e := by
      unfold applySeq
      rw [List.foldl_append]
      rfl
    rw [hstep', pos_step, ih hnd', posL_snoc hnd]

/-- Set-level register membership. -/
def posSet (ev : Set MEvent) (x : PosEntry) : Prop :=
  (∃ e ∈ ev, posCand e = some x) ∧
    ∀ e ∈ ev, ∀ y, posCand e = some y → posKey y = posKey x → posTs y ≤ posTs x

theorem mem_posL_perm {ρ : List MEvent} {ev : Set MEvent} (hperm : listPermOf ρ ev)
    {x : PosEntry} : x ∈ posL ρ ↔ posSet ev x := by
  rw [mem_posL, mem_cands, posSet]
  constructor
  · rintro ⟨⟨e, he, hx⟩, hmax⟩
    exact ⟨⟨e, (hperm.2 e).mp he, hx⟩, fun e' he' y hy hk =>
      hmax y (mem_cands.mpr ⟨e', (hperm.2 e').mpr he', hy⟩) hk⟩
  · rintro ⟨⟨e, he, hx⟩, hmax⟩
    refine ⟨⟨e, (hperm.2 e).mpr he, hx⟩, fun y hy hk => ?_⟩
    obtain ⟨e', he', hy'⟩ := mem_cands.mp hy
    exact hmax e' ((hperm.2 e').mp he') y hy' hk

theorem mem_posMerge {l a b : Finset PosEntry} {x : PosEntry} :
    x ∈ posMerge l a b ↔
      x ∈ l ∪ a ∪ b ∧ ∀ y ∈ l ∪ a ∪ b, posKey y = posKey x → posTs y ≤ posTs x := by
  simp [posMerge]

/-- The register of the union is the last-writer-wins merge of the registers
of the base and the two sides. -/
theorem posL_union {ev₁ ev₂ : Set MEvent} {ρ₀ ρ₁ ρ₂ ρU : List MEvent}
    (hp₀ : listPermOf ρ₀ (ev₁ ∩ ev₂)) (hp₁ : listPermOf ρ₁ ev₁) (hp₂ : listPermOf ρ₂ ev₂)
    (hpU : listPermOf ρU (ev₁ ∪ ev₂)) :
    posL ρU = posMerge (posL ρ₀) (posL ρ₁) (posL ρ₂) := by
  ext x
  rw [mem_posL_perm hpU, mem_posMerge]
  simp only [Finset.mem_union, mem_posL_perm hp₀, mem_posL_perm hp₁, mem_posL_perm hp₂]
  constructor
  · rintro ⟨⟨e, he, hx⟩, hmax⟩
    refine ⟨?_, ?_⟩
    · rcases he with he | he
      · exact Or.inl (Or.inr ⟨⟨e, he, hx⟩, fun e' he' y hy hk => hmax e' (Or.inl he') y hy hk⟩)
      · exact Or.inr ⟨⟨e, he, hx⟩, fun e' he' y hy hk => hmax e' (Or.inr he') y hy hk⟩
    · rintro y ((⟨⟨e', he', hy⟩, _⟩ | ⟨⟨e', he', hy⟩, _⟩) | ⟨⟨e', he', hy⟩, _⟩) hk
      · exact hmax e' (Or.inl he'.1) y hy hk
      · exact hmax e' (Or.inl he') y hy hk
      · exact hmax e' (Or.inr he') y hy hk
  · rintro ⟨hmem, hall⟩
    have hx : ∃ e ∈ ev₁ ∪ ev₂, posCand e = some x := by
      rcases hmem with (⟨⟨e, he, hx⟩, _⟩ | ⟨⟨e, he, hx⟩, _⟩) | ⟨⟨e, he, hx⟩, _⟩
      · exact ⟨e, Or.inl he.1, hx⟩
      · exact ⟨e, Or.inl he, hx⟩
      · exact ⟨e, Or.inr he, hx⟩
    refine ⟨hx, ?_⟩
    intro e' he' y hy hk
    by_contra hlt
    push_neg at hlt
    rcases he' with he' | he'
    · have hc : ∃ c ∈ cands ρ₁, posKey c = posKey x :=
        ⟨y, mem_cands.mpr ⟨e', (hp₁.2 e').mpr he', hy⟩, hk⟩
      obtain ⟨m, hm, hmk⟩ := exists_max_cand hc
      have hmy : posTs y ≤ posTs m :=
        (mem_posL.mp hm).2 y (mem_cands.mpr ⟨e', (hp₁.2 e').mpr he', hy⟩) (hk.trans hmk.symm)
      have hmx : posTs m ≤ posTs x := hall m (Or.inl (Or.inr ((mem_posL_perm hp₁).mp hm))) hmk
      exact absurd (lt_of_lt_of_le hlt hmy) (not_lt.mpr hmx)
    · have hc : ∃ c ∈ cands ρ₂, posKey c = posKey x :=
        ⟨y, mem_cands.mpr ⟨e', (hp₂.2 e').mpr he', hy⟩, hk⟩
      obtain ⟨m, hm, hmk⟩ := exists_max_cand hc
      have hmy : posTs y ≤ posTs m :=
        (mem_posL.mp hm).2 y (mem_cands.mpr ⟨e', (hp₂.2 e').mpr he', hy⟩) (hk.trans hmk.symm)
      have hmx : posTs m ≤ posTs x := hall m (Or.inr ((mem_posL_perm hp₂).mp hm)) hmk
      exact absurd (lt_of_lt_of_le hlt hmy) (not_lt.mpr hmx)

/-! ## From honesty to well-formedness -/

theorem m_loOn_iff (C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig)
    (ev : Set MEvent) (e₁ e₂ : MEvent) :
    loOn C ev e₁ e₂ ↔ C.vis e₁ e₂ ∧ ¬ M.toUpdateSig.commutes e₁ e₂ :=
  loOn_iff_of_rc_either M_rc_either C ev e₁ e₂

theorem m_respects_transfer {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig}
    {ev ev' : Set MEvent} {ρ : List MEvent}
    (h : respects ρ (loOn C ev)) : respects ρ (loOn C ev') :=
  respects_transfer_of_rc_either (D' := M.toUpdateSig) M_rc_either h

theorem ts_nodup_of_enum {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig}
    {ρ : List MEvent} {ev : Set MEvent}
    (hin : ∀ a ∈ ev, a ∈ C.events) (hperm : listPermOf ρ ev) :
    (ρ.map Prod.fst).Nodup :=
  hperm.1.map_on fun a ha b hb hab =>
    C.ts_unique (hin a ((hperm.2 a).mp ha)) (hin b ((hperm.2 b).mp hb)) hab

/-- A `loOn`-respecting enumeration of a closed set is well-formed at an honest
context. -/
theorem NR.wf_of_enum {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig}
    (hHon : N.HonestFor C) (hir : ∀ a : MEvent, ¬ C.vis a a)
    {ev : Set MEvent} {ρ : List MEvent}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b → b ∈ ev → a ∈ ev)
    (hperm : listPermOf ρ ev) (hresp : respects ρ (loOn C ev)) : N.Wf ρ := by
  refine ⟨ts_nodup_of_enum hin hperm, ?_⟩
  intro l₁ r hpre x ⟨e, heρ, hx⟩ hrem
  obtain ⟨l₂, hsplit⟩ := hpre
  have hrρ : r ∈ ρ := by rw [← hsplit]; simp
  have hrC : r ∈ C.events := hin r ((hperm.2 r).mp hrρ)
  have heC : e ∈ C.events := hin e ((hperm.2 e).mp heρ)
  have hvis : C.vis e r := hHon.named_seen r hrC e heC x hx hrem
  have hne : e ≠ r := fun h => hir r (h ▸ hvis)
  have hnc : ¬ M.toUpdateSig.commutes e r := hHon.not_comm e heC r hrC hne x hx hrem
  have heρ' : e ∈ l₁ ++ [r] ++ l₂ := by rw [hsplit]; exact heρ
  rcases List.mem_append.mp heρ' with h | h
  · rcases List.mem_append.mp h with h | h
    · exact ⟨e, h, hx⟩
    · exact absurd (List.mem_singleton.mp h) hne
  · exfalso
    have hpw := hresp
    unfold respects at hpw
    rw [← hsplit] at hpw
    have hcross := (List.pairwise_append.mp hpw).2.2 r
      (List.mem_append_right _ (List.mem_singleton_self r)) e h
    exact hcross ((m_loOn_iff C ev e r).mpr ⟨hvis, hnc⟩)

/-! ## Honesty instances -/

section Instances
variable {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig}

theorem tokNR_honest (hHon : Honest C) : tokNR.HonestFor C where
  named_seen := by
    intro r hr e he x hx hrem
    have hrem' : tokRemoves r x = true := hrem
    unfold tokRemoves at hrem'
    cases hu : MEvent.action r with
    | axis u =>
      rw [hu] at hrem'
      simp only [decide_eq_true_eq] at hrem'
      obtain ⟨hafter, _, _, hkill⟩ := hrem'
      obtain ⟨k, hk, hkt, hvis, _⟩ := hHon.kills_seen r hr u hu hafter x.2.2 hkill
      have hke : k = e := C.ts_unique hk he (by rw [hkt, tokAdds_ts e x hx])
      subst hke; exact hvis
    | cell _ => rw [hu] at hrem'; simp at hrem'
    | range _ => rw [hu] at hrem'; simp at hrem'
    | purge _ => rw [hu] at hrem'; simp at hrem'
  adder_unique := by
    intro e he e' he' x hx hx'
    exact C.ts_unique he he' ((tokAdds_ts e x hx).symm.trans (tokAdds_ts e' x hx'))
  not_comm := by
    intro e he r hr hne x hx hrem
    exact tokNR.not_comm_of_step MState.tokens tokens_init tokens_step hx hrem
      (fun hxr => hne (C.ts_unique he hr ((tokAdds_ts e x hx).symm.trans (tokAdds_ts r x hxr))))

theorem cellNR_honest (hHon : Honest C) : cellNR.HonestFor C where
  named_seen := by
    intro r hr e he x hx hrem
    have hrem' : cellRemoves r x = true := hrem
    unfold cellRemoves at hrem'
    cases hu : MEvent.action r with
    | axis _ => rw [hu] at hrem'; simp at hrem'
    | cell w =>
      rw [hu] at hrem'
      simp only [decide_eq_true_eq] at hrem'
      obtain ⟨_, _, hov⟩ := hrem'
      obtain ⟨k, hk, hkt, hvis, _⟩ := hHon.overwrites_seen r hr w hu x.2.2.1 hov
      have hke : k = e := C.ts_unique hk he (by rw [hkt, cellAdds_ts e x hx])
      subst hke; exact hvis
    | range _ => rw [hu] at hrem'; simp at hrem'
    | purge m =>
      rw [hu] at hrem'
      simp only [decide_eq_true_eq] at hrem'
      obtain ⟨k, hk, hkt, hvis, _⟩ := hHon.covered_seen r hr m hu (x.2.2.1, (x.1, x.2.1)) hrem'
      have hke : k = e := C.ts_unique hk he (by rw [hkt, cellAdds_ts e x hx])
      subst hke; exact hvis
  adder_unique := by
    intro e he e' he' x hx hx'
    exact C.ts_unique he he' ((cellAdds_ts e x hx).symm.trans (cellAdds_ts e' x hx'))
  not_comm := by
    intro e he r hr hne x hx hrem
    exact cellNR.not_comm_of_step MState.cells cells_init cells_step hx hrem
      (fun hxr => hne (C.ts_unique he hr ((cellAdds_ts e x hx).symm.trans (cellAdds_ts r x hxr))))

theorem rangeNR_honest (hHon : Honest C) : rangeNR.HonestFor C where
  named_seen := by
    intro r hr e he x hx hrem
    have hrem' : rangeRemoves r x = true := hrem
    unfold rangeRemoves at hrem'
    cases hu : MEvent.action r with
    | axis _ => rw [hu] at hrem'; simp at hrem'
    | cell _ => rw [hu] at hrem'; simp at hrem'
    | range w =>
      rw [hu] at hrem'
      simp only [decide_eq_true_eq] at hrem'
      obtain ⟨_, hov⟩ := hrem'
      obtain ⟨k, hk, hkt, hvis, _⟩ := hHon.range_overwrites_seen r hr w hu x.2.1 hov
      have hke : k = e := C.ts_unique hk he (by rw [hkt, rangeAdds_ts e x hx])
      subst hke; exact hvis
    | purge _ => rw [hu] at hrem'; simp at hrem'
  adder_unique := by
    intro e he e' he' x hx hx'
    exact C.ts_unique he he' ((rangeAdds_ts e x hx).symm.trans (rangeAdds_ts e' x hx'))
  not_comm := by
    intro e he r hr hne x hx hrem
    exact rangeNR.not_comm_of_step MState.ranges ranges_init ranges_step hx hrem
      (fun hxr => hne (C.ts_unique he hr ((rangeAdds_ts e x hx).symm.trans (rangeAdds_ts r x hxr))))

end Instances

theorem MState.ext' {a b : MState} (h1 : a.known = b.known) (h2 : a.tokens = b.tokens)
    (h3 : a.pos = b.pos) (h4 : a.cells = b.cells) (h5 : a.ranges = b.ranges) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-! ## The Join at an honest context -/

/-- **`JoinAt` for the materialised sheet.** The witness enumeration is the
base's enumeration, then the first side's delta, then the second's; every
component of the fold is the component's canonical content, and the
componentwise merge identities close the goal. -/
theorem m_join_at {C : Sal.MRDTs.Foundation.ReplayContext M.toUpdateSig}
    (hHon : Honest C) : JoinAt M C := by
  intro ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ h₀ h₁ h₂
  classical
  obtain ⟨ρ₀, hp₀, hr₀, hf₀⟩ := h₀
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  set ev₀ := ev₁ ∩ ev₂ with hev₀
  have hin₀ : ∀ a ∈ ev₀, a ∈ C.events := fun a ha => hin₁ a ha.1
  have hcl₀ : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b →
      b ∈ ev₀ → a ∈ ev₀ :=
    fun a b hv hc hb => ⟨hcl₁ a b hv hc hb.1, hcl₂ a b hv hc hb.2⟩
  have hinU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
    rintro a (ha | ha)
    · exact hin₁ a ha
    · exact hin₂ a ha
  have hclU : ∀ a b, C.vis a b → ¬ M.toUpdateSig.commutes a b →
      b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
    rintro a b hv hc (hb | hb)
    · exact Or.inl (hcl₁ a b hv hc hb)
    · exact Or.inr (hcl₂ a b hv hc hb)
  -- the witness enumeration
  set Δ₁ := ρ₁.filter (fun e => decide (e ∉ ev₀)) with hΔ₁
  set Δ₂ := ρ₂.filter (fun e => decide (e ∉ ev₀)) with hΔ₂
  have hmem₀ : ∀ x ∈ ρ₀, x ∈ ev₀ := fun x hx => (hp₀.2 x).mp hx
  have hmemΔ₁ : ∀ x ∈ Δ₁, x ∈ ev₁ ∧ x ∉ ev₀ := by
    intro x hx
    rw [hΔ₁, List.mem_filter] at hx
    exact ⟨(hp₁.2 x).mp hx.1, by simpa using hx.2⟩
  have hmemΔ₂ : ∀ x ∈ Δ₂, x ∈ ev₂ ∧ x ∉ ev₀ := by
    intro x hx
    rw [hΔ₂, List.mem_filter] at hx
    exact ⟨(hp₂.2 x).mp hx.1, by simpa using hx.2⟩
  have hΔ₂ev₁ : ∀ x ∈ Δ₂, x ∉ ev₁ := by
    intro x hx hx1
    exact (hmemΔ₂ x hx).2 ⟨hx1, (hmemΔ₂ x hx).1⟩
  have hpermU : listPermOf (ρ₀ ++ Δ₁ ++ Δ₂) (ev₁ ∪ ev₂) := by
    constructor
    · rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hp₀.1, hp₁.1.filter _, ?_⟩
        intro a ha b hb hab
        exact (hmemΔ₁ b hb).2 (hab ▸ hmem₀ a ha)
      · exact hp₂.1.filter _
      · intro a ha b hb hab
        rcases List.mem_append.mp ha with ha | ha
        · exact (hmemΔ₂ b hb).2 (hab ▸ hmem₀ a ha)
        · exact hΔ₂ev₁ b hb (hab ▸ (hmemΔ₁ a ha).1)
    · intro x
      constructor
      · intro hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl (hmem₀ x hx).1
          · exact Or.inl (hmemΔ₁ x hx).1
        · exact Or.inr (hmemΔ₂ x hx).1
      · intro hx
        by_cases hx0 : x ∈ ev₀
        · exact List.mem_append_left _
            (List.mem_append_left _ ((hp₀.2 x).mpr hx0))
        · rcases hx with hx | hx
          · refine List.mem_append_left _ (List.mem_append_right _ ?_)
            rw [hΔ₁, List.mem_filter]
            exact ⟨(hp₁.2 x).mpr hx, by simpa using hx0⟩
          · by_cases hx1 : x ∈ ev₁
            · exact absurd ⟨hx1, hx⟩ hx0
            · refine List.mem_append_right _ ?_
              rw [hΔ₂, List.mem_filter]
              exact ⟨(hp₂.2 x).mpr hx, by simpa using hx0⟩
  have hrespU : respects (ρ₀ ++ Δ₁ ++ Δ₂) (loOn C (ev₁ ∪ ev₂)) := by
    unfold respects
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨m_respects_transfer hr₀, ?_, ?_⟩
      · rw [hΔ₁]
        exact m_respects_transfer (List.Pairwise.sublist List.filter_sublist hr₁)
      · intro x hx y hy hlo
        rw [m_loOn_iff] at hlo
        have hyev : y ∈ ev₂ := hcl₂ y x hlo.1 hlo.2 (hmem₀ x hx).2
        exact (hmemΔ₁ y hy).2 ⟨(hmemΔ₁ y hy).1, hyev⟩
    · rw [hΔ₂]
      exact m_respects_transfer (List.Pairwise.sublist List.filter_sublist hr₂)
    · intro x hx y hy hlo
      rw [m_loOn_iff] at hlo
      rcases List.mem_append.mp hx with hx | hx
      · have hyev : y ∈ ev₁ := hcl₁ y x hlo.1 hlo.2 (hmem₀ x hx).1
        exact hΔ₂ev₁ y hy hyev
      · have hyev : y ∈ ev₁ := hcl₁ y x hlo.1 hlo.2 (hmemΔ₁ x hx).1
        exact hΔ₂ev₁ y hy hyev
  refine ⟨ρ₀ ++ Δ₁ ++ Δ₂, hpermU, hrespU, ?_⟩
  -- component-wise
  have hT := tokNR_honest hHon
  have hCe := cellNR_honest hHon
  have hR := rangeNR_honest hHon
  have nd₀ := ts_nodup_of_enum hin₀ hp₀
  have nd₁ := ts_nodup_of_enum hin₁ hp₁
  have nd₂ := ts_nodup_of_enum hin₂ hp₂
  have ndU := ts_nodup_of_enum hinU hpermU
  have foldT := fun (ρ : List MEvent) (w : tokNR.Wf ρ) =>
    tokNR.fold_canon MState.tokens tokens_init tokens_step ρ w
  have foldC := fun (ρ : List MEvent) (w : cellNR.Wf ρ) =>
    cellNR.fold_canon MState.cells cells_init cells_step ρ w
  have foldR := fun (ρ : List MEvent) (w : rangeNR.Wf ρ) =>
    rangeNR.fold_canon MState.ranges ranges_init ranges_step ρ w
  rw [← hf₀, ← hf₁, ← hf₂]
  apply MState.ext'
  · show (applySeq M.toUpdateSig M.init (ρ₀ ++ Δ₁ ++ Δ₂)).known =
      (applySeq M.toUpdateSig M.init ρ₀).known ∪ (applySeq M.toUpdateSig M.init ρ₁).known ∪
        (applySeq M.toUpdateSig M.init ρ₂).known
    rw [known_fold, known_fold, known_fold, known_fold]
    exact knownL_union hp₀ hp₁ hp₂ hpermU
  · show (applySeq M.toUpdateSig M.init (ρ₀ ++ Δ₁ ++ Δ₂)).tokens =
      mvr (applySeq M.toUpdateSig M.init ρ₀).tokens (applySeq M.toUpdateSig M.init ρ₁).tokens
        (applySeq M.toUpdateSig M.init ρ₂).tokens
    rw [foldT _ (tokNR.wf_of_enum hT hir hinU hclU hpermU hrespU),
      foldT _ (tokNR.wf_of_enum hT hir hin₀ hcl₀ hp₀ hr₀),
      foldT _ (tokNR.wf_of_enum hT hir hin₁ hcl₁ hp₁ hr₁),
      foldT _ (tokNR.wf_of_enum hT hir hin₂ hcl₂ hp₂ hr₂)]
    exact tokNR.mvr_canonL hT hir hin₁ hin₂ hcl₁ hcl₂ hp₀ hp₁ hp₂ hpermU
  · show (applySeq M.toUpdateSig M.init (ρ₀ ++ Δ₁ ++ Δ₂)).pos =
      posMerge (applySeq M.toUpdateSig M.init ρ₀).pos (applySeq M.toUpdateSig M.init ρ₁).pos
        (applySeq M.toUpdateSig M.init ρ₂).pos
    rw [pos_fold _ ndU, pos_fold _ nd₀, pos_fold _ nd₁, pos_fold _ nd₂]
    exact posL_union hp₀ hp₁ hp₂ hpermU
  · show (applySeq M.toUpdateSig M.init (ρ₀ ++ Δ₁ ++ Δ₂)).cells =
      mvr (applySeq M.toUpdateSig M.init ρ₀).cells (applySeq M.toUpdateSig M.init ρ₁).cells
        (applySeq M.toUpdateSig M.init ρ₂).cells
    rw [foldC _ (cellNR.wf_of_enum hCe hir hinU hclU hpermU hrespU),
      foldC _ (cellNR.wf_of_enum hCe hir hin₀ hcl₀ hp₀ hr₀),
      foldC _ (cellNR.wf_of_enum hCe hir hin₁ hcl₁ hp₁ hr₁),
      foldC _ (cellNR.wf_of_enum hCe hir hin₂ hcl₂ hp₂ hr₂)]
    exact cellNR.mvr_canonL hCe hir hin₁ hin₂ hcl₁ hcl₂ hp₀ hp₁ hp₂ hpermU
  · show (applySeq M.toUpdateSig M.init (ρ₀ ++ Δ₁ ++ Δ₂)).ranges =
      mvr (applySeq M.toUpdateSig M.init ρ₀).ranges (applySeq M.toUpdateSig M.init ρ₁).ranges
        (applySeq M.toUpdateSig M.init ρ₂).ranges
    rw [foldR _ (rangeNR.wf_of_enum hR hir hinU hclU hpermU hrespU),
      foldR _ (rangeNR.wf_of_enum hR hir hin₀ hcl₀ hp₀ hr₀),
      foldR _ (rangeNR.wf_of_enum hR hir hin₁ hcl₁ hp₁ hr₁),
      foldR _ (rangeNR.wf_of_enum hR hir hin₂ hcl₂ hp₂ hr₂)]
    exact rangeNR.mvr_canonL hR hir hin₁ hin₂ hcl₁ hcl₂ hp₀ hp₁ hp₂ hpermU

/-- The restricted Join: the target `JoinTarget` of the signature file. -/
theorem m_joinOn : JoinOn M Honest := fun _ hHon => m_join_at hHon

theorem joinTarget : JoinTarget := m_joinOn

#print axioms joinTarget

end Sal.MRDTs.Instances.AegisSheet.Materialised
