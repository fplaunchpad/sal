import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Framework.Sigma_LoOn3

/-!
# The arbitration refactor

The **arbitration abstraction** of the RA-linearizability definitional audit, which
also **bounds** the thesis: it locates the one place in the adequacy chain that
consumes the `rc` *form* rather than merely its acyclicity consequence.

## The thesis and its bound

The thesis: RA-linearizability's invariant content is "a version's state is the
fold of some enumeration extending an **acyclic arbitration** that extends `vis`
on non-commuting pairs, up to the fold quotient", and the `rc` mechanism
(directionality, `no_rc_chain`, the absorber) is merely a device for discharging
that arbitration's *acyclicity*.

The adequacy chain splits its consumption of `loOn`/`rc` into two independent
sub-obligations.

* **Existence** (`isCanonicalState_exists_u` ← `loOnNe_acyclic_u` ←
  `no_rc_chain` + the absorber): a witness enumeration *exists*. This is
  **acyclicity-only**, as the thesis claims. `AcyclicArbitration.acyclic` below is
  its abstract form; `loOn` discharges it via `loOnNe_acyclic_u`.
* **Convergence** (`isCanonicalState_unique_u` ← `convergence_on_u` ←
  `applySeq_bubble_to_front_loOn_u` ← `applySeq_swap_via_cond_comm_lift_u` ←
  `cond_comm_lift`, VC3, with the `rc` value supplied by
  `rc_non_comm_directional.mp`, VC1, at `Sigma_LoOn3.lean:474`): *all* witness
  enumerations fold to the same state, so `op(v)` is well-defined as that fold.
  This consumes the `rc` **form**: `cond_comm_lift` is a *swap keyed to*
  `rc e e' = Fst_then_snd` (the ORSet discharge, `ORSet.lean:311-336`, uses that
  premise to narrow the pair to `(rem x, add x)` and pick the erasable member),
  which acyclicity alone does **not** supply.

So the thesis is **BOUNDED at the convergence site**: the rc mechanism discharges
*both* obligations, and acyclicity accounts only for the first. The full invariant
content is:

> a version's state is, up to `eqObs`, the fold of some enumeration extending an
> acyclic arbitration that (i) extends `vis` on non-commuting pairs **and**
> (ii) is *convergent*, all respecting enumerations fold equally.

Clause (ii), `ArbConvergence` below, is the second half. It is *stronger than
acyclicity* (`acyclicity_insufficient_for_convergence`) and *weaker than the full
rc form* (its content is the rc-free "an absorbed non-commuting-concurrent pair is
fold-swap-invariant"; the absorbed member is identified by `vis`-overwrite, not by
`rc`). `rc + cond_comm_lift` is *one* construction discharging both (i) and (ii);
LWW's `max`-payload discharges (ii) trivially (all writes commute) and takes a
*finer* (i), the timestamp total order, that `rc` cannot express (see
`MRDT_Instances/LWWRegister/LWWRegister.lean`, `lww_isRALinearizable3Arb_ts`).

## Contents (kernel-clean, axioms ⊆ {propext, Classical.choice, Quot.sound})

* `AcyclicArbitration`, `IsRALinearizable3Arb`: the abstraction (a,b).
* `loOnArbitration`: `loOn` **is** an `AcyclicArbitration` (c): its acyclicity is
  `loOnNe_acyclic_u` (= the absorber + `no_rc_chain` halves), its extends-`vis` is
  `loOn_of_vis_noncomm`.
* `isRALinearizable3Arb_loOn_of_goodConfig3`,
  `isRALinearizable3_of_isRALinearizable3Arb_loOn`: the adequacy **factoring** (d):
  `GoodConfig3 ⇒ IsRALinearizable3` re-derives *through* the abstraction, via the
  existing pieces, with no re-run of the reachability induction.
* `ArbConvergence`, `loOn_arbConvergence`: the convergence obligation and the fact
  that `loOn` discharges it *via `convergence_on_u`, i.e. the rc-keyed
  `cond_comm_lift`*. This is the B-site made explicit.
* `acyclicity_insufficient_for_convergence`: the bounded-thesis pin, an acyclic
  arbitration whose two respecting enumerations fold to different states, so
  clause (ii) is independent of clause (i).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

variable {D : ConditionedMRDTSig}

/-! ## §1. The arbitration abstraction (a,b) -/

/-- The **distinct-restricted** step relation of an arbitration on an event set,
mirroring `loOnNe`: an `arb`-edge between distinct events, both in `E`. -/
def arbNe (E : Set (Op D.AppOp))
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop)
    (a b : Op D.AppOp) : Prop :=
  a ≠ b ∧ a ∈ E ∧ b ∈ E ∧ arb E a b

/-- **(a) An acyclic arbitration** on a configuration `C`: a set-relative
relation `arb E` that (i) extends `vis` on non-commuting pairs and (ii) is
acyclic on every configuration event set. This is the invariant-content relation:
the rc arm, `no_rc_chain`, and the absorber are one *device* for producing such an
`arb`, not part of its specification. -/
structure AcyclicArbitration (C : Configuration D) where
  /-- The arbitration relation, ranging over the version's own event set. -/
  arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop
  /-- (i) Every visible non-commuting pair is ordered by `vis`. -/
  extends_vis : ∀ (E : Set (Op D.AppOp)) {a b : Op D.AppOp},
    a ∈ E → b ∈ E → C.vis a b → ¬ D.toCRDTSig.commutes a b → arb E a b
  /-- (ii) The arbitration is acyclic on every event set of `C`. -/
  acyclic : ∀ (E : Set (Op D.AppOp)), (∀ a ∈ E, a ∈ C.events) →
    ∀ a : Op D.AppOp, ¬ Relation.TransGen (arbNe E arb) a a

/-- **(b) RA-linearizability against an arbitration.** Every stored version's
state is the fold of *some* enumeration of its event set that respects `arb`.
With `arb := loOn (core C)` this is exactly `GoodConfig3.canonical`;
`IsRALinearizable3` is its `lo`-coarsening (Def-lin). -/
def IsRALinearizable3Arb (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (arb E) ∧
      applySeq D.toCRDTSig D.init π = s

/-! ## §2. `loOn` is an acyclic arbitration (c): the rc-instance

The absorber and `no_rc_chain` are exactly what discharge `loOn`'s acyclicity
obligation (`loOnNe_acyclic_u`); its extends-`vis` is the definitional vis arm
(`loOn_of_vis_noncomm`). Note `arbNe E (loOn (core C)) = loOnNe (core C) E`
definitionally, so the machinery's acyclicity lemma applies unchanged. -/

/-- **(c)** `loOn` (on the replica-keyed core) instantiates the abstraction.
Requires the update-layer VCs and the two `vis` facts that hold at every
reachable configuration (supplied by `GoodConfig3`). -/
def loOnArbitration (C : Configuration D) (hU : UpdateVCs D.toCRDTSig)
    (h_tr : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a) :
    AcyclicArbitration C where
  arb := fun E => loOn (Configuration.core C) E
  extends_vis := by intro _E _a _b _ha _hb hv hnc; exact loOn_of_vis_noncomm hv hnc
  acyclic := fun _E h_in a => loOnNe_acyclic_u hU h_tr h_ir h_in a

/-! ## §3. The adequacy factoring (d)

The adequacy `isRALinearizable3_of_good : GoodConfig3 C →
IsRALinearizable3 C` re-derives *through* the abstraction as the composite of two
one-liners: `GoodConfig3` gives `IsRALinearizable3Arb (loOn (core C))` (the
`canonical` field unfolds to the arb-witness), and the loOn-form transports down
to the `lo`-form Def-lin. No re-run of the `join_lemma3_of_cd_feasible`
induction: the abstraction sits *between* `GoodConfig3` and `IsRALinearizable3`. -/

/-- **(d, in)** The canonical invariant is arb-RA-linearizability at `arb :=
loOn`. `IsCanonicalState (core C) E s` unfolds definitionally to the arb-witness. -/
theorem isRALinearizable3Arb_loOn_of_goodConfig3 {C : Configuration D}
    (h : GoodConfig3 C) :
    IsRALinearizable3Arb C (fun E => loOn (Configuration.core C) E) :=
  fun v s E hv => h.canonical v s E hv

/-- **(d, out)** Arb-RA-linearizability at `loOn` transports down to the
`lo`-form Def-lin: a `loOn(E)`-respecting witness is a `lo`-respecting
witness (`respects_lo_of_respects_loOn`). -/
theorem isRALinearizable3_of_isRALinearizable3Arb_loOn {C : Configuration D}
    (h : IsRALinearizable3Arb C (fun E => loOn (Configuration.core C) E)) :
    IsRALinearizable3 C := by
  intro v s E hv
  obtain ⟨π, hp, hr, hs⟩ := h v s E hv
  exact ⟨π, hp, respects_lo_of_respects_loOn hr, hs⟩

/-- **(d)** The adequacy, factored through the abstraction: the same
`GoodConfig3 ⇒ IsRALinearizable3` implication, composed as
`(out) ∘ (loOn-instance) ∘ (in)`. -/
theorem isRALinearizable3_of_good_via_arb {C : Configuration D}
    (h : GoodConfig3 C) : IsRALinearizable3 C :=
  isRALinearizable3_of_isRALinearizable3Arb_loOn
    (isRALinearizable3Arb_loOn_of_goodConfig3 h)

/-! ## §4. The convergence obligation and the B-site (the bound)

`AcyclicArbitration` is *not* enough to make `op(v)` well-defined: two respecting
enumerations could fold to different states. Well-definedness is the separate
**convergence** obligation. For `loOn` it is discharged by `convergence_on_u`,
which routes through `applySeq_swap_via_cond_comm_lift_u` and hence consumes
`cond_comm_lift` (VC3), a swap *keyed to* `rc e e' = Fst_then_snd`. This is the
single place the adequacy chain consumes the rc *form* rather than mere
acyclicity, and it is why the thesis is bounded. -/

/-- **The convergence obligation** for an arbitration: on every configuration
event set, all `arb`-respecting enumerations fold to the same state (from any
start). This is what makes the canonical state, hence `op(v)`, well-defined.
It is *not* implied by `AcyclicArbitration` (see
`acyclicity_insufficient_for_convergence`). -/
def ArbConvergence (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : Prop :=
  ∀ (E : Set (Op D.AppOp)) (s₀ : D.State) (π₁ π₂ : List (Op D.AppOp)),
    (∀ a ∈ E, a ∈ C.events) →
    listPermOf π₁ E → listPermOf π₂ E →
    respects π₁ (arb E) → respects π₂ (arb E) →
    applySeq D.toCRDTSig s₀ π₁ = applySeq D.toCRDTSig s₀ π₂

/-- **The B-site, made explicit.** `loOn`'s convergence obligation is exactly
`convergence_on_u`, and `convergence_on_u` consumes `cond_comm_lift` (VC3,
rc-keyed) through `applySeq_swap_via_cond_comm_lift_u`, with the rc value obtained
from `rc_non_comm_directional.mp` (VC1). So this discharge is *not*
acyclicity-only: it consumes the rc form. -/
theorem loOn_arbConvergence {C : Configuration D} (hU : UpdateVCs D.toCRDTSig) :
    ArbConvergence C (fun E => loOn (Configuration.core C) E) :=
  fun _E s₀ _π₁ _π₂ h_in hp₁ hp₂ hr₁ hr₂ =>
    convergence_on_u hU s₀ h_in hp₁ hp₂ hr₁ hr₂

/-- **Acyclicity is insufficient for convergence** (the bounded-thesis pin). The
discrete (empty) arbitration is vacuously acyclic and, on a datatype whose
concurrent pair does not `vis`-relate, vacuously extends-`vis`-on-noncomm, yet
two enumerations respecting it fold to *different* states whenever `update` is
order-sensitive on that pair. Witnessed on the overwrite fold `fun _ e => e`:
`[a, b]` folds to `b`, `[b, a]` folds to `a`. Hence `ArbConvergence` is a genuine
obligation *beyond* `AcyclicArbitration`; `loOn` supplies it only through the
rc-keyed `cond_comm_lift`. -/
theorem acyclicity_insufficient_for_convergence {S : Type} {a b : S} (hab : a ≠ b) :
    ∃ (upd : S → S → S) (s₀ : S) (π₁ π₂ : List S),
      π₁.Perm π₂ ∧ List.foldl upd s₀ π₁ ≠ List.foldl upd s₀ π₂ := by
  refine ⟨fun _ e => e, a, [a, b], [b, a], List.Perm.swap b a [], ?_⟩
  simp only [List.foldl_cons, List.foldl_nil]
  exact Ne.symm hab

#print axioms loOnArbitration
#print axioms isRALinearizable3Arb_loOn_of_goodConfig3
#print axioms isRALinearizable3_of_isRALinearizable3Arb_loOn
#print axioms isRALinearizable3_of_good_via_arb
#print axioms loOn_arbConvergence
#print axioms acyclicity_insufficient_for_convergence

end Sal.ConditionedMRDTs
