import LeanProofs.Interface.Implementation
import Artifact.MRDTs.Framework.Certificates
import Artifact.MRDTs.Paper1.RestrictedReplay

/-!
# `Laws(D_type)`, common to both routes

`Laws(D_type, Spec)` of Section 4 collects RC-NON-COMM, NO-RC-CHAIN,
COND-COMM and SPEC-NON-COMM. Every one of them is stated over operations,
`o1 --rc--> o2`, exactly as the displayed definitions are.

Every row proves `Laws`, by one of two routes.

* A **VC route** row discharges the canonical join laws of
  `Interface/VCRoute.lean`, and the metatheory hands it `Laws` for free.
* A **direct route** row proves `Laws` itself and supplies the join lemma,
  as `Interface/DirectRoute.lean` asks.

SPEC-NON-COMM is not a field below. It mentions `Spec`, which the laws of
this file do not, and no proof downstream consumes it.
-/
namespace LeanProofs.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1

variable {type : MRDTType} (D : Impl type)

/-- `rc` as the framework's operation policy. Definition 4 and the laws of
Section 4 are both indexed by it. -/
def policy : OperationPolicy type.OType where
  before o₁ o₂ := D.RcBefore o₁ o₂

/-- `Laws(D_type)`, the three conditions of Section 4 that constrain `rc`.

SPEC-NON-COMM is omitted from this bundle: it relates the implementation to
`Spec` and so belongs with the sequential premise in `Soundness`. -/
structure Laws : Prop where
  /-- **RC-NON-COMM**: `rc` relates exactly the pairs that do not commute.

  The paper writes this with a conjunct `o1 ≠ o2` on the left, which is
  **omitted here**: this development follows the framework's uniform adapter
  `RestrictedLaws` rather than its event-guarded contract
  `GuardedReplay.Laws`. All certified rows satisfy the stronger form. -/
  rc_non_comm : ∀ e₁ e₂ : D.Event,
    ¬ D.Commutes e₁ e₂ ↔ D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁
  /-- **NO-RC-CHAIN**: no chain of two `rc` edges. -/
  no_rc_chain : ∀ o₁ o₂ o₃ : type.OType,
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃)
  /-- **COND-COMM**: once an absorber removes an `rc` edge, both orders
  agree. `e''` is the absorber and `pi` the events applied between. -/
  cond_comm : ∀ (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event),
    D.EventRcBefore e e' → ¬ D.Commutes e' e'' →
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e''

/-- `Laws` is the framework's `RestrictedLaws` at `policy`, field for field. -/
theorem Laws.toRestricted {D : Impl type} (h : Laws D) :
    RestrictedLaws D.toMRDTSig.toUpdateSig (policy D) :=
  ⟨h.rc_non_comm, h.no_rc_chain, h.cond_comm⟩

end LeanProofs.Interface
