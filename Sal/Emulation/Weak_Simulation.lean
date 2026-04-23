import Sal.Emulation.Labeled_TS

/-!
# Weak simulation and weak traces

Generic machinery for comparing two labeled transition systems modulo
silent (τ) transitions. Follows Liittschwager et al. §2.2 + §4 and
Milner's standard presentation.

This file lays down the types and soundness statement. The simulation
step diagram and the soundness proof are scaffolded with `sorry`s; see
PLAN.md step 8 for the remaining work.
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
      ∃ t' : T₂.State, T₂.weakStep t (hLabel ▸ ℓ) t' ∧ rel s' t'

/-- **Soundness of weak simulation for weak-trace inclusion.** If
`R` is a weak simulation and `R s t`, then every observable trace of
`s` is also a trace of `t` (modulo the label coercion).

Proof plan (Milner-style): induction on `isWeakExecution`.
* Nil: immediate.
* Cons: apply `R.step` to lift each `weakStep` in `T₁` to one in `T₂`;
  glue with the recursive call.

TODO: mechanise. Tracked as step 8 in PLAN.md. -/
theorem weakSim_sound {T₁ T₂ : LabeledTS}
    {hLabel : T₁.Label = T₂.Label}
    (_R : WeakSim T₁ T₂ hLabel)
    {s : T₁.State} {t : T₂.State} (_hR : _R.rel s t)
    (labels : List T₁.Label)
    (_h : labels ∈ T₁.weakTrace s) :
    (labels.map (fun ℓ => hLabel ▸ ℓ)) ∈ T₂.weakTrace t := by
  sorry

end Sal.Emulation
