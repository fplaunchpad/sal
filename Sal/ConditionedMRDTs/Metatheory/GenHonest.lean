import Sal.ConditionedMRDTs.Metatheory.HonestReach

/-!
# The generic honesty shape

Every conditioned instance's honesty contract so far has the same shape: a
predicate `P` holds of each event at the fold of (any enumeration of) its
causal past. `GenHonest D P` mechanizes that shape once, over the ternary
configuration.

This is the **client-checkable** form of the contract: `P e s` is a check the
*issuer* of `e` runs against its own state — which, at issue time, is exactly
the fold of `e`'s causal past. The bounded counter's `BCHonest` (a `dec`
needs slack: `BCHonest_iff_genHonest`) and the mergeable queue's
`qHonest_of_applicable` hypothesis (a `deq t` names the observed head:
`qHonest_of_genHonest`) are both instances with `P` the datatype's
`applicable` guard (`AppHonest`). Instances bridge `GenHonest` to whatever
witness-form their join actually consumes — the queue's `QHonest` (an
existential enqueue witness per dequeue), the counter's `BCHonest` verbatim.
The tombstone-free RGA's `HonestDelivery` (born accuracy + applicable
delivery) is the same fold-of-causal-past shape, stated per step of the
delivery relation rather than per configuration; it is deliberately left on
its own formulation.

**Caveat on the ∀-enumeration form**: quantifying `P` over ALL enumerations
of the causal past is only appropriate when `P` is fold-order-insensitive
(all-comm datatypes like the bounded counter, or measure-valued guards).
For order-sensitive datatypes the ∀-form can be unsatisfiable in honest
executions (the queue's head check: two surviving enqueues in a past
materialize different heads under different orders) — such instances want
the existential causal-fold form, taken directly by their bridges
(`qHonest_of_applicable`) and to be provided generically as `HonestApp`
with the safety metatheorem (see
`Development/GENERIC_SAFETY_PENPAPER.md` §3).

`CausalPastEnumerable` isolates the side condition the bridges need: every
event's causal past admits a `listPermOf`-enumeration. This holds in
reachable configurations, whose event sets are finite, but the repo has no
generic finiteness result for reachable configurations' event sets yet (only
the RGA carries a per-instance one), so it is kept as an explicit hypothesis.

The composite metatheorem `ra_linearizable3_of_genHonest_reach` instantiates
`HonestReach` at `H := GenHonest D P`: if every `GenHonest`-configuration
admits the Join at its core, every `GenHonest`-honestly reachable
configuration is per-version RA-linearizable.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- **The generic honesty shape**: `P` holds of every event at the fold of
(any enumeration of) its causal past. -/
def GenHonest (D : ConditionedMRDTSig) (P : Op D.AppOp → D.State → Prop)
    (C : Configuration D) : Prop :=
  ∀ e ∈ C.events, ∀ π : List (Op D.AppOp),
    listPermOf π {e' ∈ C.events | C.vis e' e} →
    P e (applySeq D.toCRDTSig D.init π)

/-- Every event's causal past admits an enumeration. Holds in reachable
configurations, where event sets are finite; kept as an explicit hypothesis
because the repo has no generic finiteness result for reachable
configurations' event sets. -/
def CausalPastEnumerable (D : ConditionedMRDTSig) (C : Configuration D) : Prop :=
  ∀ e ∈ C.events, ∃ π : List (Op D.AppOp),
    listPermOf π {e' ∈ C.events | C.vis e' e}

/-- The canonical instance of the shape: the datatype's own generation-time
`applicable` guard holds of every event at the fold of its causal past. -/
def AppHonest (D : ConditionedMRDTSig) : Configuration D → Prop :=
  GenHonest D D.applicable

variable {D : ConditionedMRDTSig}

/-- `GenHonest` is monotone in the predicate. -/
theorem GenHonest.mono {P P' : Op D.AppOp → D.State → Prop}
    (h : ∀ e s, P e s → P' e s) {C : Configuration D}
    (hGen : GenHonest D P C) : GenHonest D P' C :=
  fun e he π hπ => h e _ (hGen e he π hπ)

/-- **The conditioned metatheorem, generic-honesty form**: per-version
RA-linearizability at every `GenHonest`-honestly reachable configuration,
given the Join at every `GenHonest`-configuration. -/
theorem ra_linearizable3_of_genHonest_reach {hInit : D.Inv D.init}
    (P : Op D.AppOp → D.State → Prop)
    (hJoinAt : ∀ C', GenHonest D P C' → JoinLemma3At D (Configuration.core C'))
    {C : Configuration D} (hReach : HonestReach D (GenHonest D P) hInit C) :
    IsRALinearizable3 C :=
  ra_linearizable3_of_honest_reach hJoinAt hReach

#print axioms ra_linearizable3_of_genHonest_reach

end Sal.ConditionedMRDTs
