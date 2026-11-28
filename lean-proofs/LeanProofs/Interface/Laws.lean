import LeanProofs_no_spec_non_comm.Interface.Implementation
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
namespace LeanProofs.NoSpecNonComm.Interface

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
them cannot be certified through this adapter at all. A row whose RC-NON-COMM
holds only at concurrent events is such a row, and it goes through
`GuardedReplay.Laws` instead. -/
theorem Laws.toRestricted {D : Impl type} (h : Laws D)
    (hru : UniformRcNonComm D) (hcc : UniformCondComm D) :
    RestrictedLaws D.toMRDTSig.toUpdateSig (policy D) :=
  ⟨fun a b => hru a b, h.no_rc_chain, hcc⟩

/-! ## The same two laws, as the guarded contract wants them

`RestrictedLaws` above is one of the framework's two adapters. The other is
`GuardedReplay.Laws`, which `Interface/VCRoute.lean` runs on and which
keeps the paper's concurrency guards on RC-NON-COMM. It is still not
`Laws(D_type)`: it drops the `o1 /= o2` conjunct, and its COND-COMM drops
the replica guard too. The readings below are what closes those two gaps,
and they live here rather than in `VCRoute.lean` so that every statement
of RC-NON-COMM and COND-COMM in this development is in one file. -/

/-- **RC-NON-COMM over concurrent events, without the `o1 /= o2` conjunct.**

`Laws.rc_non_comm` is the paper's statement and carries that conjunct on its
left. Dropping it costs nothing: read right to left NO-RC-CHAIN produces it,
which is what `rcNonComm_of_exact` does. Dropping the two **hypotheses**
would cost a great deal, and this abbreviation keeps them: unlike
`UniformRcNonComm` it asks nothing of a pair one replica issued. -/
abbrev ConcurrentRcNonComm (D : Impl type) : Prop :=
  ∀ e₁ e₂ : D.Event, D.time e₁ ≠ D.time e₂ → D.rep e₁ ≠ D.rep e₂ →
    (¬ D.Commutes e₁ e₂ ↔ D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁)

/-- The unguarded reading implies the guarded one. -/
theorem UniformRcNonComm.toConcurrent {D : Impl type} (h : UniformRcNonComm D) :
    ConcurrentRcNonComm D := fun e₁ e₂ _ _ => h e₁ e₂

/-- **What `Laws(D_type)` does not say.**

RC-NON-COMM carries `o1 /= o2` on its left, so it is silent about a pair of
concurrent events carrying **one** operation. That silence cannot be left
open. Nothing would order such a pair: `lo^C_E`'s causal disjunct needs a
`vis` edge, which concurrent events do not have, and its `rc` disjunct would
need `o --rc--> o`, which NO-RC-CHAIN refutes. The two replays would then
fold to different states and `can^C(E)` would not be a function of `E`.

So this is the one fact the paper's laws leave out, stated on its own rather
than folded back into RC-NON-COMM. The framework splits the contract the
same way, in `SplitPolicy.guarded_iff_repaired`. -/
abbrev EqualOpCommutes (D : Impl type) : Prop :=
  ∀ e₁ e₂ : D.Event, D.time e₁ ≠ D.time e₂ → D.rep e₁ ≠ D.rep e₂ →
    e₁.op = e₂.op → D.Commutes e₁ e₂

/-- A row that proves the exact equivalence at concurrent events has it
already: an `rc` edge from an operation to itself is a chain of two. -/
theorem EqualOpCommutes.of_concurrent {D : Impl type}
    (hchain : ∀ o₁ o₂ o₃ : type.OType, ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃))
    (h : ConcurrentRcNonComm D) : EqualOpCommutes D := by
  intro e₁ e₂ ht hr hop
  by_contra hn
  have hdiag : D.RcBefore e₂.op e₂.op := by
    rcases (h e₁ e₂ ht hr).mp hn with hb | hb
    · have hb' : D.RcBefore e₁.op e₂.op := hb
      rwa [hop] at hb'
    · have hb' : D.RcBefore e₂.op e₁.op := hb
      rwa [hop] at hb'
  exact hchain e₂.op e₂.op e₂.op ⟨hdiag, hdiag⟩

/-- **What `Laws(D_type)` does not say about COND-COMM.**

COND-COMM carries two guards, distinct timestamps and **different
replicas**. The guarded contract keeps the first and drops the second, so
the case left open is a pair of events one replica issued at different
times. `lo^C_E` never transposes such a pair, since one replica's events are
causally ordered, but the contract is stated without a context and cannot
see that, so a row supplies the case. -/
abbrev SameReplicaCondComm (D : Impl type) : Prop :=
  ∀ (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event),
    D.time e ≠ D.time e' → D.rep e = D.rep e' →
    D.EventRcBefore e e' → ¬ D.Commutes e' e'' →
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e''

/-- A row that proves COND-COMM with no guard at all has the case already. -/
theorem UniformCondComm.toSameReplica {D : Impl type} (h : UniformCondComm D) :
    SameReplicaCondComm D :=
  fun sigma e e' e'' pi _ _ hrc hnc => h sigma e e' e'' pi hrc hnc

/-- **The framework's guarded contract**, from `Laws(D_type)` and the two
cases it leaves open.

This is the contract `Soundness/` runs on along this route. Unlike
`RestrictedLaws`, every one of its three conditions carries the paper's own
exemptions, so a row is never asked about a pair that `lo^C_E` cannot
transpose. Each condition is proved by splitting on the guard the paper's law carries.
For RC-NON-COMM the `o1 /= o2` half is `Laws.rc_non_comm` and the `o1 = o2`
half is `EqualOpCommutes`, with NO-RC-CHAIN closing the right-hand side. For
COND-COMM the different-replica half is `Laws.cond_comm` and the
same-replica half is `SameReplicaCondComm`.

Every pair either law is consulted about therefore carries distinct
timestamps, and RC-NON-COMM is consulted only about pairs from different
replicas, which is what makes this contract and not `RestrictedLaws` the one
every row here runs on. -/
theorem guardedLaws {D : Impl type} (h : Laws D) (hself : EqualOpCommutes D)
    (hsame : SameReplicaCondComm D) :
    GuardedReplay.Laws D.toMRDTSig.toUpdateSig (policy D) where
  noncomm_exact a b hd hrep := by
    by_cases hop : a.op = b.op
    · refine ⟨fun hn => absurd (hself a b hd hrep hop) hn, ?_⟩
      rintro (hb | hb) <;> rw [hop] at hb <;>
        exact (h.no_rc_chain b.op b.op b.op ⟨hb, hb⟩).elim
    · exact ⟨fun hn => (h.rc_non_comm a b hd hrep).mp ⟨hn, hop⟩,
        fun hb => ((h.rc_non_comm a b hd hrep).mpr hb).1⟩
  no_chain a b c _ _ := h.no_rc_chain a.op b.op c.op
  conditional_commutation s a b c between hd _ _ hab hbc := by
    by_cases hrep : D.rep a = D.rep b
    · exact hsame s a b c between hd hrep hab hbc
    · exact h.cond_comm s a b c between hd hrep hab hbc

