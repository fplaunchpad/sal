import LeanProofs.Interface.Laws
import Artifact.MRDTs.Framework.MergeLaws

/-!
# The canonical join laws

The five verification conditions of Section 5, which every row discharges.
There is no other way to a join lemma here: nothing supplies one of its own
to `Soundness/`.

## These are the paper's conditions, as the paper states them

VC1 is over arbitrary states, as `proof_strategy.tex` has it, and the paper
notes it is the only one that is. VC2 to VC5 carry the paper's premises:
`Admissible`, `Maximal`, and the equalities pinning each state to the
canonical state of a particular event set. Nothing here is a universal
strengthening of a canonical statement.

The paper's notation maps onto the fields as follows.

* `can_C(E) = s` is `IsCanOn D C E s`.
* `Admissible_C(E)` is the pair of conditions that `E` lies in `C.events`
  and is weakly closed under `vis` at non-commuting pairs, which is
  `SupportedOn` and `WeaklyClosed`.
* `Maximal^C_{E}(e)` is `MaximalOn D C E e`: no other event of `E` is above
  `e` in `lo^C_E`.
* `downset C e \ {e}` is the paper's `(down e) \ {e}`, and `e(m)` is
  `D.do_ m e`.

## What is not here

`commuting_peel` used to be a sixth field. It is not one of the paper's
conditions, so it has been moved out: it is now a hypothesis of
`Metatheory.causalDelta_of_commuting`, the helper an all-commuting row uses
to discharge VC4 cheaply. The obligation set in this file is exactly VC1 to
VC5.
-/

namespace LeanProofs.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1

variable {type : MRDTType} (D : Impl type)

/-! ## The paper's side conditions, named -/

/-- A replay context of `D`, which is what the paper's `C` contributes to
the verification conditions. -/
abbrev Ctx (D : Impl type) : Type :=
  ReplayContext D.toMRDTSig.toUpdateSig

/-- `can_C(E) = s`. -/
abbrev IsCanOn (C : Ctx D) (E : Set D.Event) (s : D.Sigma) : Prop :=
  @IsCanonicalState D.toMRDTSig.toUpdateSig (rcOrder D) C E s

/-- Half of `Admissible_C(E)`: every event of `E` is observed in `C`. -/
abbrev SupportedOn (C : Ctx D) (E : Set D.Event) : Prop :=
  ∀ a ∈ E, a ∈ C.events

/-- The other half of `Admissible_C(E)`: `E` is closed under `vis`
predecessors that do not commute. This is the paper's `WeakClosed_C(E)`. -/
abbrev WeaklyClosed (C : Ctx D) (E : Set D.Event) : Prop :=
  ∀ a b, C.vis a b → ¬ D.Commutes a b → b ∈ E → a ∈ E

/-- `Maximal^C_E(e)`: no other event of `E` sits above `e` in `lo^C_E`. -/
abbrev MaximalOn (C : Ctx D) (E : Set D.Event) (e : D.Event) : Prop :=
  ∀ x ∈ E, x ≠ e → ¬ @loOn D.toMRDTSig.toUpdateSig (rcOrder D) C E e x

/-- `vis` is a strict partial order, which the paper assumes of every
configuration. -/
abbrev VisStrict (C : Ctx D) : Prop :=
  (∀ {a b c : D.Event}, C.vis a b → C.vis b c → C.vis a c) ∧
    (∀ a : D.Event, ¬ C.vis a a)

/-- The union of two weakly closed sets is weakly closed. -/
theorem weaklyClosed_union {D : Impl type} {C : Ctx D} {E₁ E₂ : Set D.Event}
    (c₁ : WeaklyClosed D C E₁) (c₂ : WeaklyClosed D C E₂) :
    WeaklyClosed D C (E₁ ∪ E₂) := by
  rintro a b hv hnc (hb | hb)
  · exact Or.inl (c₁ a b hv hnc hb)
  · exact Or.inr (c₂ a b hv hnc hb)

/-! ## VC1 to VC5 -/

/-- The *canonical join laws*, VC1 to VC5 of Section 5, in the paper's own
form. -/
structure CanonicalJoinLaws : Prop where
  /-- **VC1** MERGE-COMM, over arbitrary states as the paper states it:
  `merge(l,a,b) = merge(l,b,a)`. -/
  vc1_merge_comm : ∀ l a b : D.Sigma, D.merge l a b = D.merge l b a
  /-- **VC2** MERGE-INIT: `Admissible_C(E)` implies
  `merge(sigma0, sigma0, can(E)) = can(E)`. -/
  vc2_merge_init : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
    SupportedOn D C E → IsCanOn D C E s →
    D.merge D.sigma0 D.sigma0 s = s
  /-- **VC3** LOCAL-REDISTRIBUTE, for a maximal `e` in `E1` only:
  `merge(l, merge(m,x,e(m)), y) = merge(m, merge(l,x,y), e(m))`
  with `l = can(E1 n E2)`, `m = can(down(e) \ {e})`, `x = can(E1 \ {e})`
  and `y = can(E2)`. -/
  vc3_local_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (l m x y : D.Sigma) (e : D.Event),
    VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
    IsCanOn D C (E₁ ∩ E₂) l →
    IsCanOn D C (downset C e \ {e}) m →
    IsCanOn D C (E₁ \ {e}) x →
    IsCanOn D C E₂ y →
    D.merge l (D.merge m x (D.do_ m e)) y
      = D.merge m (D.merge l x y) (D.do_ m e)
  /-- **VC4** CAUSAL-DELTA, for a maximal `e` of `E`:
  `merge(B, A, e(B)) = e(A)` with `A = can(E \ {e})` and
  `B = can(down(e) \ {e})`.

  `Metatheory.causalDelta_of_commuting` discharges this for a row whose
  events all commute. -/
  vc4_causal_delta : @CausalDeltaLaw D.toMRDTSig (rcOrder D)
  /-- **VC5** REDISTRIBUTE, for a maximal `e` in both branches:
  `merge(merge(m,x0,e(m)), merge(m,x1,e(m)), merge(m,x2,e(m)))
   = merge(m, merge(x0,x1,x2), e(m))`
  with `m = can(down(e) \ {e})`, `x0 = can((E1 n E2) \ {e})`,
  `x1 = can(E1 \ {e})` and `x2 = can(E2 \ {e})`. -/
  vc5_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
    VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
    IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
    IsCanOn D C (downset C e \ {e}) m →
    IsCanOn D C (E₁ \ {e}) x₁ →
    IsCanOn D C (E₂ \ {e}) x₂ →
    D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))
      = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e)

/-- **The obligation bundle for the VC route**, for any implementation.

Nothing here asks the events to commute. A row that discharges `Laws` and
the five conditions of Section 5 takes this route, whether its operations
commute or not: the OR-set does, and so does the counter.

`rc_non_comm` and `cond_comm` are the unguarded readings that
`Laws.toRestricted` needs. `Laws` states the paper's guarded forms, which
say nothing about a pair one replica issued, so they are separate fields
rather than projections. A commuting row proves them in two lines; a
non-commuting row proves them along with the rest of its laws. -/
structure Obligations : Prop where
  /-- `Laws(D_type)`: RC-NON-COMM, NO-RC-CHAIN and COND-COMM. -/
  laws : Laws D
  /-- RC-NON-COMM without the concurrency guard. -/
  rc_non_comm : UniformRcNonComm D
  /-- COND-COMM without the concurrency guard. -/
  cond_comm : UniformCondComm D
  /-- VC1 to VC5 of Section 5. -/
  joinLaws : CanonicalJoinLaws D

/-! ## The same conditions under a side condition on the context

One row of Table 1 carries an issuance guard, and its join lemma is false
without it. The remove-wins set reserves timestamp `0` for the tags its
initial state carries, so a minted `remove` at timestamp `0` would be
indistinguishable from one of those. `G(e, s) <=> 0 < time(e)` excludes it.

A guard on events becomes a condition on contexts: every event the context
observes was minted honestly. The conditions below are VC1 to VC5 again,
each with that condition in front, and `Good = fun _ => True` recovers the
unguarded bundle above. VC1 is over arbitrary states and needs no context,
so it is unchanged.

A row that needs no guard takes `CanonicalJoinLaws` and `Obligations`, and
`toOn` below lifts those to this form for free. -/

/-- **VC1 to VC5 at the contexts `Good` admits.** Identical to
`CanonicalJoinLaws` except that every condition mentioning a context asks it
of `Good` contexts only. -/
structure CanonicalJoinLawsOn (Good : Ctx D → Prop) : Prop where
  /-- **VC1** MERGE-COMM. No context appears, so no side condition does. -/
  vc1_merge_comm : ∀ l a b : D.Sigma, D.merge l a b = D.merge l b a
  /-- **VC2** MERGE-INIT. -/
  vc2_merge_init : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
    Good C → SupportedOn D C E → IsCanOn D C E s →
    D.merge D.sigma0 D.sigma0 s = s
  /-- **VC3** LOCAL-REDISTRIBUTE. -/
  vc3_local_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (l m x y : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
    IsCanOn D C (E₁ ∩ E₂) l →
    IsCanOn D C (downset C e \ {e}) m →
    IsCanOn D C (E₁ \ {e}) x →
    IsCanOn D C E₂ y →
    D.merge l (D.merge m x (D.do_ m e)) y
      = D.merge m (D.merge l x y) (D.do_ m e)
  /-- **VC4** CAUSAL-DELTA, written out rather than taken from the framework,
  since the framework's `CausalDeltaLaw` admits every context. -/
  vc4_causal_delta : ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma)
    (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C U → WeaklyClosed D C U →
    e ∈ U → MaximalOn D C U e →
    IsCanOn D C (U \ {e}) A →
    IsCanOn D C (downset C e \ {e}) B →
    D.merge B A (D.do_ B e) = D.do_ A e
  /-- **VC5** REDISTRIBUTE. -/
  vc5_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
    e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
    IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
    IsCanOn D C (downset C e \ {e}) m →
    IsCanOn D C (E₁ \ {e}) x₁ →
    IsCanOn D C (E₂ \ {e}) x₂ →
    D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))
      = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e)

/-- **The obligation bundle for the guarded VC route.** The same four fields
as `Obligations`, with the conditions asked only of the contexts `Good`
admits. -/
structure ObligationsOn (Good : Ctx D → Prop) : Prop where
  /-- `Laws(D_type)`: RC-NON-COMM, NO-RC-CHAIN and COND-COMM. -/
  laws : Laws D
  /-- RC-NON-COMM without the concurrency guard. -/
  rc_non_comm : UniformRcNonComm D
  /-- COND-COMM without the concurrency guard. -/
  cond_comm : UniformCondComm D
  /-- VC1 to VC5 of Section 5, at the `Good` contexts. -/
  joinLaws : CanonicalJoinLawsOn D Good

/-- A row that discharges the conditions at every context discharges them at
the `Good` ones. VC4 is the only field that is rephrased, from the
framework's `CausalDeltaLaw` to the spelled-out form above. -/
theorem CanonicalJoinLaws.toOn {D : Impl type} (h : CanonicalJoinLaws D)
    (Good : Ctx D → Prop) : CanonicalJoinLawsOn D Good where
  vc1_merge_comm := h.vc1_merge_comm
  vc2_merge_init := fun C E s _ hsup hcan => h.vc2_merge_init C E s hsup hcan
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ hv h₁ h₂ hc₁ hc₂ he₁ he₂
      hmax hl hm hx hy =>
    h.vc3_local_redistribute C E₁ E₂ l m x y e hv h₁ h₂ hc₁ hc₂ he₁ he₂
      hmax hl hm hx hy
  vc4_causal_delta := fun C U A B e _ hv hsup hcl he hmax hA hB =>
    h.vc4_causal_delta C U A B e hv.1 hv.2 hsup hcl he hmax hA hB
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ hv h₁ h₂ hc₁ hc₂ he₁ he₂
      hmax hx₀ hm hx₁ hx₂ =>
    h.vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e hv h₁ h₂ hc₁ hc₂ he₁ he₂
      hmax hx₀ hm hx₁ hx₂

/-- The same lifting for the whole bundle. -/
theorem Obligations.toOn {D : Impl type} (h : Obligations D)
    (Good : Ctx D → Prop) : ObligationsOn D Good :=
  ⟨h.laws, h.rc_non_comm, h.cond_comm, h.joinLaws.toOn Good⟩

end LeanProofs.Interface
