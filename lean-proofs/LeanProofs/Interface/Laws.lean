import LeanProofs.Interface.Implementation
import Artifact.MRDTs.Framework.MergeLaws
import Artifact.MRDTs.Framework.Certificates

/-!
# The proof obligations

Two bundles, both named after the paper.

`Laws(D_type, Spec)` of Section 4 collects RC-NON-COMM, NO-RC-CHAIN,
COND-COMM and SPEC-NON-COMM.

The *canonical join laws* of Section 5 are VC1 to VC5.

## One place where these differ from the paper, deliberately

The paper states VC2 to VC5 over canonical states, under `Admissible` and
`Maximal` premises. `CanonicalJoinLaws` below states the arbitrary-state
strengthenings, which is what this family of implementations actually
satisfies and what makes the obligations closed by arithmetic alone.

* VC1 MERGE-COMM is already over arbitrary states in the paper, so it is
  reproduced verbatim.
* VC2 MERGE-INIT, VC3 LOCAL-REDISTRIBUTE and VC5 REDISTRIBUTE have the same
  equations with `can(E)` replaced by an arbitrary state and `e(m)` by an
  arbitrary state.
* VC4 CAUSAL-DELTA is **not** an obligation here. For an implementation whose
  events all commute the metatheory derives it, from `commuting_peel` below
  together with `all_commute`. An implementation outside that family must
  supply VC4 directly.
-/

namespace LeanProofs.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation

variable {type : MRDTType} (D : Impl type)

/-- `Laws(D_type, Spec)`, the conditions of Section 4 that constrain `rc`.

SPEC-NON-COMM is omitted from this bundle: it relates the implementation to
`Spec` and so belongs with the conformance obligations below. -/
structure Laws : Prop where
  /-- RC-NON-COMM: `rc` relates exactly the pairs that do not commute. The
  direction stated here is the one the linearization argument consumes. -/
  rc_non_comm : ∀ e₁ e₂ : D.Event,
    ¬ D.Commutes e₁ e₂ → D.RcBefore e₁ e₂ ∨ D.RcBefore e₂ e₁
  /-- NO-RC-CHAIN: no chain of two `rc` edges. -/
  no_rc_chain : ∀ e₁ e₂ e₃ : D.Event,
    ¬ (D.RcBefore e₁ e₂ ∧ D.RcBefore e₂ e₃)
  /-- COND-COMM: once an absorber removes an `rc` edge, both orders agree. -/
  cond_comm : ∀ (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event),
    D.Distinct e e' → D.Distinct e e'' → D.Distinct e' e'' →
    D.RcBefore e e' →
    (D.RcBefore e' e'' ∨ D.RcBefore e'' e') →
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e''

/-- The *canonical join laws*, VC1 to VC5, in their arbitrary-state form.
See the header for the two respects in which this differs from the paper. -/
structure CanonicalJoinLaws : Prop where
  /-- **VC1** MERGE-COMM, verbatim:
  `merge(l,a,b) = merge(l,b,a)`. -/
  vc1_merge_comm : ∀ l a b : D.Sigma, D.merge l a b = D.merge l b a
  /-- **VC2** MERGE-INIT, with `can(E)` generalised to any state:
  `merge(sigma0, sigma0, s) = s`. -/
  vc2_merge_init : ∀ s : D.Sigma, D.merge D.sigma0 D.sigma0 s = s
  /-- **VC3** LOCAL-REDISTRIBUTE, with `e(m)` generalised to any state `c`:
  `merge(l, merge(m,x,c), y) = merge(m, merge(l,x,y), c)`. -/
  vc3_local_redistribute : ∀ l m x c y : D.Sigma,
    D.merge l (D.merge m x c) y = D.merge m (D.merge l x y) c
  /-- **VC5** REDISTRIBUTE, with `e(m)` generalised to any state `c`:
  `merge(merge(m,x0,c), merge(m,x1,c), merge(m,x2,c)) = merge(m, merge(x0,x1,x2), c)`. -/
  vc5_redistribute : ∀ m x₀ x₁ x₂ c : D.Sigma,
    D.merge (D.merge m x₀ c) (D.merge m x₁ c) (D.merge m x₂ c)
      = D.merge m (D.merge x₀ x₁ x₂) c
  /-- Auxiliary, **not** a paper VC. An event that commutes with both
  replayed branches can be pulled outside the merge. The metatheory turns
  this into **VC4** CAUSAL-DELTA when every pair of events commutes. -/
  commuting_peel : ∀ (a : D.Sigma) (e : D.Event) (pi₀ pi₂ : List D.Event),
    (∀ x ∈ pi₀, D.Commutes e x) → (∀ x ∈ pi₂, D.Commutes e x) →
    D.merge (D.applyList D.sigma0 pi₀) (D.do_ a e) (D.applyList D.sigma0 pi₂)
      = D.do_ (D.merge (D.applyList D.sigma0 pi₀) a (D.applyList D.sigma0 pi₂)) e

/-- The complete obligation bundle for implementations whose events all
commute. `rc` is then `Either` everywhere, so `Laws` is discharged by the
metatheory rather than by the implementation.

An implementation with a nonempty `rc` supplies `Laws` and VC4 itself; the
fields of `CanonicalJoinLaws` above are shared with it. -/
structure Obligations : Prop where
  /-- Every pair of events commutes: `forall e1 e2. e1 <-> e2`. -/
  all_commute : ∀ e₁ e₂ : D.Event, D.Commutes e₁ e₂
  /-- `rc` is empty, as RC-NON-COMM then requires. -/
  rc_either : ∀ e₁ e₂ : D.Event, D.RcEither e₁ e₂
  /-- VC1, VC2, VC3, VC5 and the auxiliary peel law. -/
  joinLaws : CanonicalJoinLaws D

/-- Conformance to `Spec`: the remaining half of Definition 4, which the
canonical join laws alone do not establish.

`refines` is the simulation of Section 6; `observes` is the condition that
`ops(pi) . (q => b)` is in `Spec` with `b` the implementation's own answer. -/
structure Conformance (Spec : SequentialSpec D.toMRDTSig)
    (Rel : D.Sigma → Spec.State → Prop) : Prop where
  legal : ∀ pi : List D.Event, Spec.Legal pi
  refines : ∀ pi : List D.Event, Rel (D.applyList D.sigma0 pi) (Spec.run pi)
  observes : ∀ (pi : List D.Event) (q : type.QType),
    D.query (D.applyList D.sigma0 pi) q = Spec.query (Spec.run pi) q

end LeanProofs.Interface
