import LeanProofs.Interface.Implementation
import Artifact.MRDTs.Framework.Certificates
import Artifact.MRDTs.Paper1.RestrictedReplay
import Artifact.MRDTs.Paper1.GuardedReplay

/-!
# `Laws(D_type)`, common to every row

`Laws(D_type, Spec)` of Section 4 collects RC-NON-COMM, NO-RC-CHAIN,
COND-COMM and SPEC-NON-COMM. Every one of them is stated over operations,
`o1 --rc--> o2`, exactly as the displayed definitions are.

Every row proves `Laws` itself. The metatheory does not manufacture it: a
row with an empty `rc` closes each condition in a line or two, and a row
with a nonempty `rc` has real work to do.

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

/-- The replay order the argument runs at: `rc`, lifted from operations to
the events that carry them. `lo^C_E` is built from this together with `vis`. -/
noncomputable abbrev rcOrder (D : Impl type) : EventOrder D.toMRDTSig.toUpdateSig :=
  (policy D).lift

/-- `Laws(D_type)`, the three conditions of Section 4 that constrain `rc`.

SPEC-NON-COMM is omitted from this bundle: it relates the implementation to
`Spec` and so belongs with the sequential premise in `Soundness`. -/
structure Laws : Prop where
  /-- **RC-NON-COMM**: `rc` relates exactly the pairs that do not commute,
  **over concurrent events only**.

  `o1 /= o2` sits inside the equivalence, on its left, exactly where the
  paper puts it. It is not a side condition: read right to left the law has
  to produce it, and NO-RC-CHAIN does, since an `rc` edge from an operation
  to itself would be a chain of two such edges.

  The two hypotheses in front are the other exemption. `lo^C_E` consults `rc`
  only when neither event sees the other, and two events issued by one
  replica are always causally ordered, so `rc` never has to order them. In
  event form that reads: distinct timestamps, different replicas. -/
  rc_non_comm : ∀ e₁ e₂ : D.Event,
    D.time e₁ ≠ D.time e₂ → D.rep e₁ ≠ D.rep e₂ →
    ((¬ D.Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔ D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁)
  /-- **NO-RC-CHAIN**: no chain of two `rc` edges. -/
  no_rc_chain : ∀ o₁ o₂ o₃ : type.OType,
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃)
  /-- **COND-COMM**, with `e` and `e'` concurrent: once an absorber removes
  an `rc` edge, both orders agree. `e''` is the absorber and `pi` the events
  applied between.

  The first two hypotheses are the event-level reading of concurrency, as in
  RC-NON-COMM above. The absorber clause is reached only where `lo^C_E` may
  transpose `e` and `e'`. Two events of one replica are always ordered by
  `vis`, and one event is never transposed with itself, so the pair this law
  is asked about always carries distinct timestamps and distinct issuers. -/
  cond_comm : ∀ (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event),
    D.time e ≠ D.time e' → D.rep e ≠ D.rep e' →
    D.EventRcBefore e e' → ¬ D.Commutes e' e'' →
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e''

/-- **The paper's RC-NON-COMM, from the plain equivalence plus NO-RC-CHAIN.**

A row proves `not (e1 <-> e2) <-> rc`, with or without the concurrency
guards. The paper's form carries `o1 /= o2` as a second conjunct on the left,
so read right to left it has to produce that conjunct. NO-RC-CHAIN produces
it: an `rc` edge from an operation to itself is a chain of two `rc` edges. -/
theorem rcNonComm_of_exact {D : Impl type}
    (hchain : ∀ o₁ o₂ o₃ : type.OType, ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃))
    (h : ∀ e₁ e₂ : D.Event, D.time e₁ ≠ D.time e₂ → D.rep e₁ ≠ D.rep e₂ →
      (¬ D.Commutes e₁ e₂ ↔ D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁)) :
    ∀ e₁ e₂ : D.Event, D.time e₁ ≠ D.time e₂ → D.rep e₁ ≠ D.rep e₂ →
      ((¬ D.Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
        D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁) := by
  intro e₁ e₂ ht hrep
  refine ⟨fun hn => (h e₁ e₂ ht hrep).mp hn.1,
    fun hr => ⟨(h e₁ e₂ ht hrep).mpr hr, fun hop => ?_⟩⟩
  have hr' : D.RcBefore e₁.op e₂.op ∨ D.RcBefore e₂.op e₁.op := hr
  have hself : D.RcBefore e₂.op e₂.op := by
    rcases hr' with hb | hb
    · rw [hop] at hb; exact hb
    · rw [hop] at hb; exact hb
  exact hchain e₂.op e₂.op e₂.op ⟨hself, hself⟩

/-- **RC-NON-COMM without the concurrency guard.**

`Laws.rc_non_comm` is the paper's statement and asks nothing of a pair that
carries one operation, or that one replica issued. The vendored
`RestrictedLaws` asks about every pair, so it cannot be built from `Laws`
alone. Every row here proves the exact equivalence at an arbitrary pair, and
supplies it under this name alongside `Laws`. -/
abbrev UniformRcNonComm (D : Impl type) : Prop :=
  ∀ e₁ e₂ : D.Event,
    ¬ D.Commutes e₁ e₂ ↔ D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁

/-- **COND-COMM without the concurrency guard.**

`Laws.cond_comm` is the paper's statement and says nothing about a pair of
events issued by one replica. The vendored `RestrictedLaws` that `Soundness/`
consumes does ask about such a pair, so it cannot be built from `Laws` alone.
Every row here proves the equation at an arbitrary pair, and supplies it
under this name alongside `Laws`. -/
abbrev UniformCondComm (D : Impl type) : Prop :=
  ∀ (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event),
    D.EventRcBefore e e' → ¬ D.Commutes e' e'' →
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e''

/-- The framework's uniform `RestrictedLaws`, from the two unguarded laws
plus NO-RC-CHAIN.

`Laws` alone does not give this. Its RC-NON-COMM and COND-COMM each exempt
the pairs the paper exempts, and `RestrictedLaws` asks about those pairs too.
So both unguarded laws are taken as hypotheses, and a row that cannot supply
them cannot be certified through `Soundness/` at all. The efficient OR-set is
such a row. -/
theorem Laws.toRestricted {D : Impl type} (h : Laws D)
    (hru : UniformRcNonComm D) (hcc : UniformCondComm D) :
    RestrictedLaws D.toMRDTSig.toUpdateSig (policy D) :=
  ⟨fun a b => hru a b, h.no_rc_chain, hcc⟩
