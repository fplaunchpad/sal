import Sal.Emulation.Labeled_TS

/-!
# Weak simulation and weak traces

Generic machinery for comparing two labeled transition systems modulo
silent (τ) transitions. Follows Liittschwager et al. §2.2 + §4 and
Milner's standard presentation.

This file lays down the types and soundness statement. The simulation
step diagram and the soundness proof are scaffolded with `sorry`s.
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

For Liittschwager-style emulation, `T₁` and `T₂` have the same label
grammar, so this shared-label restriction is harmless. The more
general case (with a label morphism) is a straightforward
generalization, deferred. -/
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
