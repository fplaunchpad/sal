import Sal.Emulation.Labeled_TS

/-!
# Weak simulation and weak traces

Generic machinery for comparing two labeled transition systems modulo
silent (τ) transitions. Follows Liittschwager et al. §2.2 + §4 and
Milner's standard presentation.

The first API preserves the historical same-label interface. The second,
label-morphic API at the end of the file is the general Liittschwager form and
proves trace transport, two-way trace equivalence, and representation
independence.
-/

namespace Sal.Emulation

namespace LabeledTS

/-- A silent step: a transition whose label is silent. -/
def silentStep (T : LabeledTS) (s s' : T.State) : Prop :=
  ∃ ℓ, T.silent ℓ ∧ T.step s ℓ s'

/-- Reflexive-transitive closure of silent steps: `s =τ*=> s'`. -/
def silentClosure (T : LabeledTS) : T.State → T.State → Prop :=
  Relation.ReflTransGen T.silentStep

/-- Weak step `s =ℓ=> s'`.
* If `ℓ` is silent, it's just `silentClosure s s'`.
* Otherwise: `silentClosure s s₁`, `step s₁ ℓ s₂`, `silentClosure s₂ s'`. -/
inductive weakStep (T : LabeledTS) (s : T.State) : T.Label → T.State → Prop where
  | ofSilent {ℓ : T.Label} {s' : T.State}
      (hs : T.silent ℓ) (hcl : T.silentClosure s s') :
      weakStep T s ℓ s'
  | ofObs {ℓ : T.Label} {s₁ s₂ s' : T.State}
      (hobs : ¬ T.silent ℓ)
      (h₁ : T.silentClosure s s₁)
      (hst : T.step s₁ ℓ s₂)
      (h₂ : T.silentClosure s₂ s') :
      weakStep T s ℓ s'

/-- Chain of weak observable steps. `isWeakExecution s trail` holds
when consecutive `weakStep`s chained through `trail` start at `s` and
each label is observable. -/
inductive isWeakExecution (T : LabeledTS) : T.State → List (T.Label × T.State) → Prop where
  | nil (s : T.State) : isWeakExecution T s []
  | cons {s s' : T.State} {ℓ : T.Label}
      {rest : List (T.Label × T.State)}
      (hobs : ¬ T.silent ℓ)
      (hw   : T.weakStep s ℓ s')
      (hrest : isWeakExecution T s' rest) :
      isWeakExecution T s ((ℓ, s') :: rest)

/-- Weak trace set of `s`: observable label lists reachable from `s`
via weak executions. Paper notation: `wtrace(s)`. -/
def weakTrace (T : LabeledTS) (s : T.State) : Set (List T.Label) :=
  fun labels => ∃ trail, T.isWeakExecution s trail ∧ trail.map Prod.fst = labels

end LabeledTS

/-- Explicit label coercion under a type equality. Use instead of
raw `hLabel ▸ ℓ` when Lean needs help with type inference
(particularly in lambdas and `List.map` arguments). -/
def coerceLabel {T₁ T₂ : LabeledTS} (hLabel : T₁.Label = T₂.Label)
    (ℓ : T₁.Label) : T₂.Label := hLabel ▸ ℓ

/-- Silent-preservation assumption: the label coercion respects silent
classifications. Required by all lift lemmas below so a silent T₁ step
lifts to a silent-closure in T₂ (rather than a potentially observable
path). -/
abbrev SilentPreserving {T₁ T₂ : LabeledTS} (hLabel : T₁.Label = T₂.Label) :=
  ∀ ℓ : T₁.Label, T₁.silent ℓ ↔ T₂.silent (coerceLabel hLabel ℓ)

/-- **Weak simulation** of `T₁` by `T₂`, restricted to LTSs sharing a
common label type. A relation `R ⊆ T₁.State × T₂.State` is a weak
simulation when, for every `R s t` and every `T₁`-step `s -ℓ→ s'`,
there is a matching `T₂`-weak step `t =ℓ=> t'` with `R s' t'`.

This equality-based form remains for compatibility; new emulation proofs use
`WeakSimM` and `LabelMorphism` below. -/
structure WeakSim (T₁ T₂ : LabeledTS)
    (hLabel : T₁.Label = T₂.Label) where
  rel : T₁.State → T₂.State → Prop
  -- The simulation diagram. Stated pointwise; specialises to silent
  -- and observable cases via `weakStep`.
  step :
    ∀ {s s' : T₁.State} {t : T₂.State} {ℓ : T₁.Label},
      rel s t → T₁.step s ℓ s' →
      ∃ t' : T₂.State, T₂.weakStep t (coerceLabel hLabel ℓ) t' ∧ rel s' t'

/-- Lift a `silentClosure` in `T₁` through a weak simulation. -/
theorem silentClosure_lift {T₁ T₂ : LabeledTS}
    {hLabel : T₁.Label = T₂.Label}
    (hSil : SilentPreserving hLabel)
    (R : WeakSim T₁ T₂ hLabel)
    {s s' : T₁.State} {t : T₂.State}
    (hR : R.rel s t) (hcl : T₁.silentClosure s s') :
    ∃ t', T₂.silentClosure t t' ∧ R.rel s' t' := by
  induction hcl with
  | refl => exact ⟨t, Relation.ReflTransGen.refl, hR⟩
  | tail _ hss ih =>
    obtain ⟨t', hcl', hR'⟩ := ih
    obtain ⟨ℓ, hsℓ, hst⟩ := hss
    obtain ⟨t'', hw, hR''⟩ := R.step hR' hst
    have hsℓ₂ : T₂.silent (coerceLabel hLabel ℓ) := (hSil ℓ).mp hsℓ
    cases hw with
    | ofSilent _ hcl'' => exact ⟨t'', hcl'.trans hcl'', hR''⟩
    | ofObs hobs _ _ _ => exact absurd hsℓ₂ hobs

/-- Lift a `weakStep` in `T₁` through a weak simulation. -/
theorem weakStep_lift {T₁ T₂ : LabeledTS}
    {hLabel : T₁.Label = T₂.Label}
    (hSil : SilentPreserving hLabel)
    (R : WeakSim T₁ T₂ hLabel)
    {s s' : T₁.State} {t : T₂.State} {ℓ : T₁.Label}
    (hR : R.rel s t) (hw : T₁.weakStep s ℓ s') :
    ∃ t', T₂.weakStep t (coerceLabel hLabel ℓ) t' ∧ R.rel s' t' := by
  cases hw with
  | ofSilent hsℓ hcl =>
    obtain ⟨t', hcl', hR'⟩ := silentClosure_lift hSil R hR hcl
    refine ⟨t', ?_, hR'⟩
    exact LabeledTS.weakStep.ofSilent ((hSil ℓ).mp hsℓ) hcl'
  | ofObs hobs h₁ hst h₂ =>
    -- s =τ*=> s₁ -ℓ→ s₂ =τ*=> s'
    obtain ⟨t₁, hcl_pre, hR₁⟩ := silentClosure_lift hSil R hR h₁
    obtain ⟨t₂, hw_mid, hR₂⟩ := R.step hR₁ hst
    obtain ⟨t', hcl_post, hR'⟩ := silentClosure_lift hSil R hR₂ h₂
    refine ⟨t', ?_, hR'⟩
    -- Glue: t =τ*=> t₁ =hLabel▸ℓ=> t₂ =τ*=> t'. The middle is a
    -- weakStep itself (already has τ-prefix/suffix built in), so we
    -- need to compose three weakStep/silentClosure pieces. Easier:
    -- case-split on hw_mid's variant.
    cases hw_mid with
    | ofSilent hsℓ₂ _ =>
      have : ¬ T₂.silent (coerceLabel hLabel ℓ) :=
        fun h => hobs ((hSil ℓ).mpr h)
      exact absurd hsℓ₂ this
    | ofObs hobs₂ hcl_a hst_mid hcl_b =>
      exact LabeledTS.weakStep.ofObs hobs₂
        (hcl_pre.trans hcl_a) hst_mid (hcl_b.trans hcl_post)

/-- Lift a weak execution in `T₁` through a weak simulation. The
label list of the lifted execution is the coerced label list of the
original. -/
theorem isWeakExecution_lift {T₁ T₂ : LabeledTS}
    {hLabel : T₁.Label = T₂.Label}
    (hSil : SilentPreserving hLabel)
    (R : WeakSim T₁ T₂ hLabel)
    {s : T₁.State} {t : T₂.State}
    (hR : R.rel s t) {trail : List (T₁.Label × T₁.State)}
    (hex : T₁.isWeakExecution s trail) :
    ∃ trail' : List (T₂.Label × T₂.State),
      T₂.isWeakExecution t trail' ∧
      trail'.map Prod.fst =
        (trail.map Prod.fst).map (coerceLabel hLabel) := by
  induction hex generalizing t with
  | nil => exact ⟨[], LabeledTS.isWeakExecution.nil _, rfl⟩
  | @cons _ _ ℓ _ hobs hw _ ih =>
    obtain ⟨t', hw', hR'⟩ := weakStep_lift hSil R hR hw
    obtain ⟨trail', hex', hlbl⟩ := ih hR'
    refine ⟨(coerceLabel hLabel ℓ, t') :: trail', ?_, ?_⟩
    · refine LabeledTS.isWeakExecution.cons ?_ hw' hex'
      intro h
      exact hobs ((hSil _).mpr h)
    · simp [hlbl]

/-- **Soundness of weak simulation for weak-trace inclusion.** If
`R` is a weak simulation (with silent-preservation) and `R s t`, then
every observable trace of `s` (via the label coercion) is a trace of `t`. -/
theorem weakSim_sound {T₁ T₂ : LabeledTS}
    {hLabel : T₁.Label = T₂.Label}
    (hSil : SilentPreserving hLabel)
    (R : WeakSim T₁ T₂ hLabel)
    {s : T₁.State} {t : T₂.State} (hR : R.rel s t)
    (labels : List T₁.Label)
    (h : labels ∈ T₁.weakTrace s) :
    labels.map (coerceLabel hLabel) ∈ T₂.weakTrace t := by
  obtain ⟨trail, hex, hmap⟩ := h
  obtain ⟨trail', hex', hlbl⟩ := isWeakExecution_lift hSil R hR hex
  refine ⟨trail', hex', ?_⟩
  rw [hlbl, hmap]

end Sal.Emulation

/-! ## Label-morphic weak simulation

The equality-based API above is retained as a compatibility specialization.
The definitions below are the Liittschwager interface used by emulation:
labels may have different concrete grammars and are related by a
silence-preserving observation map. -/

namespace Sal.Emulation

open LabeledTS

/-- A label translation that preserves and reflects observability. -/
structure LabelMorphism (T₁ T₂ : LabeledTS) where
  map : T₁.Label → T₂.Label
  silent_iff : ∀ ℓ, T₁.silent ℓ ↔ T₂.silent (map ℓ)

/-- Weak simulation along a label morphism. -/
structure WeakSimM (T₁ T₂ : LabeledTS) (μ : LabelMorphism T₁ T₂) where
  rel : T₁.State → T₂.State → Prop
  step : ∀ {s s' : T₁.State} {t : T₂.State} {ℓ : T₁.Label},
    rel s t → T₁.step s ℓ s' →
    ∃ t', T₂.weakStep t (μ.map ℓ) t' ∧ rel s' t'

namespace WeakSimM

/-- Any concrete step is a weak step; silent steps inhabit the silent closure,
while observable steps use reflexive silent closures on both sides. -/
theorem weakStep_of_step {T : LabeledTS} {s s' : T.State} {ℓ : T.Label}
    (h : T.step s ℓ s') : T.weakStep s ℓ s' := by
  by_cases hs : T.silent ℓ
  · exact .ofSilent hs (.single ⟨ℓ, hs, h⟩)
  · exact .ofObs hs .refl h .refl

theorem silentClosure_lift {T₁ T₂ : LabeledTS} {μ : LabelMorphism T₁ T₂}
    (R : WeakSimM T₁ T₂ μ) {s s' : T₁.State} {t : T₂.State}
    (hR : R.rel s t) (hcl : T₁.silentClosure s s') :
    ∃ t', T₂.silentClosure t t' ∧ R.rel s' t' := by
  induction hcl with
  | refl => exact ⟨t, Relation.ReflTransGen.refl, hR⟩
  | tail _ hss ih =>
      obtain ⟨t', hcl', hR'⟩ := ih
      obtain ⟨ℓ, hsℓ, hst⟩ := hss
      obtain ⟨t'', hw, hR''⟩ := R.step hR' hst
      have hs₂ : T₂.silent (μ.map ℓ) := (μ.silent_iff ℓ).mp hsℓ
      cases hw with
      | ofSilent _ hcl'' => exact ⟨t'', hcl'.trans hcl'', hR''⟩
      | ofObs hobs _ _ _ => exact absurd hs₂ hobs

theorem weakStep_lift {T₁ T₂ : LabeledTS} {μ : LabelMorphism T₁ T₂}
    (R : WeakSimM T₁ T₂ μ) {s s' : T₁.State} {t : T₂.State}
    {ℓ : T₁.Label} (hR : R.rel s t) (hw : T₁.weakStep s ℓ s') :
    ∃ t', T₂.weakStep t (μ.map ℓ) t' ∧ R.rel s' t' := by
  cases hw with
  | ofSilent hs hcl =>
      obtain ⟨t', hcl', hR'⟩ := silentClosure_lift R hR hcl
      exact ⟨t', .ofSilent ((μ.silent_iff _).mp hs) hcl', hR'⟩
  | ofObs hobs hpre hst hpost =>
      obtain ⟨t₁, hc₁, hR₁⟩ := silentClosure_lift R hR hpre
      obtain ⟨t₂, hmid, hR₂⟩ := R.step hR₁ hst
      obtain ⟨t', hc₂, hR'⟩ := silentClosure_lift R hR₂ hpost
      cases hmid with
      | ofSilent hs _ =>
          exact absurd hs (fun hs' => hobs ((μ.silent_iff _).mpr hs'))
      | ofObs ho ha hm hb =>
          exact ⟨t', .ofObs ho (hc₁.trans ha) hm (hb.trans hc₂), hR'⟩

theorem execution_lift {T₁ T₂ : LabeledTS} {μ : LabelMorphism T₁ T₂}
    (R : WeakSimM T₁ T₂ μ) {s : T₁.State} {t : T₂.State}
    (hR : R.rel s t) {trail : List (T₁.Label × T₁.State)}
    (hex : T₁.isWeakExecution s trail) :
    ∃ trail' : List (T₂.Label × T₂.State),
      T₂.isWeakExecution t trail' ∧
      trail'.map Prod.fst = (trail.map Prod.fst).map μ.map := by
  induction hex generalizing t with
  | nil => exact ⟨[], .nil _, rfl⟩
  | @cons _ _ ℓ _ hobs hw _ ih =>
      obtain ⟨t', hw', hR'⟩ := weakStep_lift R hR hw
      obtain ⟨tail, htail, hmap⟩ := ih hR'
      refine ⟨(μ.map ℓ, t') :: tail, .cons ?_ hw' htail, ?_⟩
      · exact fun hs => hobs ((μ.silent_iff ℓ).mpr hs)
      · simp [hmap]

/-- Label-morphic weak simulation preserves all weak traces. -/
theorem trace_sound {T₁ T₂ : LabeledTS} {μ : LabelMorphism T₁ T₂}
    (R : WeakSimM T₁ T₂ μ) {s : T₁.State} {t : T₂.State}
    (hR : R.rel s t) {labels : List T₁.Label}
    (h : labels ∈ T₁.weakTrace s) :
    labels.map μ.map ∈ T₂.weakTrace t := by
  obtain ⟨trail, hex, hlabels⟩ := h
  obtain ⟨trail', hex', hmap⟩ := execution_lift R hR hex
  exact ⟨trail', hex', hmap.trans (congrArg (List.map μ.map) hlabels)⟩

end WeakSimM

/-- The two (not necessarily converse) simulations constituting CRDT
emulation, with independent label morphisms in each direction. -/
structure WeakTraceEquivalence (T₁ T₂ : LabeledTS) where
  forwardLabels : LabelMorphism T₁ T₂
  backwardLabels : LabelMorphism T₂ T₁
  forward : WeakSimM T₁ T₂ forwardLabels
  backward : WeakSimM T₂ T₁ backwardLabels

/-- Two label morphisms that are mutually inverse. -/
structure LabelIso (T₁ T₂ : LabeledTS) where
  forward : LabelMorphism T₁ T₂
  backward : LabelMorphism T₂ T₁
  left_inv : ∀ ℓ, backward.map (forward.map ℓ) = ℓ
  right_inv : ∀ ℓ, forward.map (backward.map ℓ) = ℓ

namespace LabelIso

theorem map_left {T₁ T₂ : LabeledTS} (e : LabelIso T₁ T₂)
    (labels : List T₁.Label) :
    (labels.map e.forward.map).map e.backward.map = labels := by
  induction labels with
  | nil => rfl
  | cons ℓ rest ih => simp only [List.map_cons]; rw [e.left_inv, ih]

end LabelIso

/-- Liittschwagger-style emulation at distinguished states: two weak
simulations with an observation-preserving label isomorphism. The relations
need not be converses. -/
structure EmulationEquivalence (T₁ T₂ : LabeledTS) where
  labels : LabelIso T₁ T₂
  forward : WeakSimM T₁ T₂ labels.forward
  backward : WeakSimM T₂ T₁ labels.backward

namespace EmulationEquivalence

theorem trace_iff {T₁ T₂ : LabeledTS} (E : EmulationEquivalence T₁ T₂)
    {s : T₁.State} {t : T₂.State}
    (hf : E.forward.rel s t) (hb : E.backward.rel t s)
    (labels : List T₁.Label) :
    labels ∈ T₁.weakTrace s ↔
      labels.map E.labels.forward.map ∈ T₂.weakTrace t := by
  constructor
  · exact E.forward.trace_sound hf
  · intro h
    have hback := E.backward.trace_sound hb h
    rwa [E.labels.map_left labels] at hback

/-- Representation independence for any predicate on observable traces:
clients see the same truth value after translating labels. -/
theorem representation_independence {T₁ T₂ : LabeledTS}
    (E : EmulationEquivalence T₁ T₂) {s : T₁.State} {t : T₂.State}
    (hf : E.forward.rel s t) (hb : E.backward.rel t s)
    (P : List T₁.Label → Prop) :
    (∀ tr, tr ∈ T₁.weakTrace s → P tr) ↔
    (∀ tr, tr ∈ T₂.weakTrace t → P (tr.map E.labels.backward.map)) := by
  constructor
  · intro hP tr htr
    have hsrc := E.backward.trace_sound hb htr
    exact hP _ hsrc
  · intro hP tr htr
    have htgt := E.forward.trace_sound hf htr
    have := hP _ htgt
    rwa [E.labels.map_left tr] at this

end EmulationEquivalence

end Sal.Emulation
