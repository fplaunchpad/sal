import LeanProofs.Interface.Implementation
import Artifact.MRDTs.Framework.Certificates
import Artifact.MRDTs.Paper1.RestrictedReplay
import Artifact.MRDTs.Paper1.GuardedReplay

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
  /-- **RC-NON-COMM**: `rc` relates exactly the pairs that do not commute,
  **over concurrent events only**.

  The paper writes the law with a conjunct `o1 ≠ o2` on the left, and in
  `lo^C_E` consults `rc` only when neither event sees the other. Two events
  issued by one replica are always causally ordered, so `rc` never has to
  order them. The event form of that exemption is the two hypotheses below:
  distinct timestamps, and different replicas. -/
  rc_non_comm : ∀ e₁ e₂ : D.Event,
    D.time e₁ ≠ D.time e₂ → D.rep e₁ ≠ D.rep e₂ →
    (¬ D.Commutes e₁ e₂ ↔ D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁)
  /-- **NO-RC-CHAIN**: no chain of two `rc` edges. -/
  no_rc_chain : ∀ o₁ o₂ o₃ : type.OType,
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃)
  /-- **COND-COMM**: once an absorber removes an `rc` edge, both orders
  agree. `e''` is the absorber and `pi` the events applied between. -/
  cond_comm : ∀ (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event),
    D.EventRcBefore e e' → ¬ D.Commutes e' e'' →
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e''

/-- **Non-commutation is a function of the payloads alone.**

`Laws.rc_non_comm` is guarded, as the paper's is, so on its own it says
nothing about a same-replica pair. The vendored `Soundness` chain runs on
`loOn` at a lifted operation policy and does need those pairs covered. This
predicate is what closes the gap, and it is exactly what a row whose
non-commutation is internal to one operation cannot supply.

The efficient OR-set is that row: two `add x` events from one replica
differ only in their timestamps and do not commute, while two from
different replicas do. It is certified outside `Interface/` for this
reason. -/
def PayloadDetermined (D : Impl type) : Prop :=
  ∀ e₁ e₂ f₁ f₂ : D.Event, e₁.op = f₁.op → e₂.op = f₂.op →
    (D.Commutes e₁ e₂ ↔ D.Commutes f₁ f₂)

/-- The guarded law plus payload determinacy give the framework's uniform
`RestrictedLaws`. Fresh timestamps on distinct replicas witness the guard,
and `PayloadDetermined` transports the result back. -/
theorem Laws.toRestricted {D : Impl type} (h : Laws D) (hp : PayloadDetermined D) :
    RestrictedLaws D.toMRDTSig.toUpdateSig (policy D) := by
  refine ⟨?_, h.no_rc_chain, h.cond_comm⟩
  intro a b
  have key := h.rc_non_comm ((0, 0, a.op) : D.Event) ((1, 1, b.op) : D.Event)
    (by simp [Impl.time, Op.time]) (by simp [Impl.rep, Op.rep])
  have hc := hp ((0, 0, a.op) : D.Event) ((1, 1, b.op) : D.Event) a b rfl rfl
  simpa [Impl.EventRcBefore, hc] using key

/-! ## The paper's guarded form

Section 4 writes RC-NON-COMM with a conjunct `o1 /= o2` on the left, so it
says nothing about a pair of events carrying the same operation. The event
form of that exemption is `a.rep /= b.rep`: two events from one replica are
always causally ordered, so `rc` never has to order them, and `lo^C_E`
consults `rc` only for concurrent pairs.

`GuardedLaws` below is that version. `Laws` implies it, never the converse,
and the gap is exactly the rows whose non-commutation is internal to one
operation.

It is not yet what `Soundness/` consumes. The chain there runs through
`loOn` at a lifted operation policy, and under the guard `paperOrder` and
`loOn` genuinely differ at a `vis`-ordered same-replica pair: `paperOrder`
orders them by visibility alone, `loOn` wants an `rc` edge. Closing that
needs the artifact's concrete pipeline, which this development does not
vendor. -/

/-- **The paper's RC-NON-COMM, with its `o1 /= o2` conjunct**, in the event
form the framework uses: exactness is required only of events with distinct
timestamps issued by different replicas. -/
abbrev GuardedLaws (D : Impl type) : Prop :=
  Artifact.MRDTs.Paper1.GuardedReplay.Laws D.toMRDTSig.toUpdateSig (policy D)

/-- The uniform contract implies the guarded one. The converse fails, which
is why `EfficientORSet/` cannot use `Interface/` at all. -/
theorem Laws.toGuarded {D : Impl type} (h : Laws D) (hp : PayloadDetermined D) :
    GuardedLaws D :=
  Artifact.MRDTs.Paper1.GuardedReplay.ofUniform (h.toRestricted hp)

end LeanProofs.Interface
