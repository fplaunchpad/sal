# The RA-linearizability definition: a four-strike audit and the absorber dichotomy

Task #114 phase 3. Companion harness:
`whiteboard/litmus/absorber_dichotomy_check.py` (stdlib only, PASS+FAIL, exit 0).
This note reads the RA-linearizability *definition* the way the VC-minimality
sweep (`whiteboard/vc-minimality-note.md`) read the verification conditions:
as a published statement carrying proof-technique artifacts around an invariant
core. The sweep found the eight VCs to be a four-law core plus a shell. This
note finds the definition's linearization order to be an arbitration-acyclicity
requirement plus a fold quotient, with four clauses that are sufficient devices
for that content rather than parts of it. One clause, the absorber, is
interrogated in full and decided by machine.

## 1. The published definition, stated natively

Fix a conditioned MRDT with update `do`, ternary merge `mergeL`, and conflict
resolver `rc`. For an event set `E` the linearization order `loOn(E)` puts
`e1` before `e2` when

    (vis e1 e2 and not comm e1 e2)                                  [vis arm]
    or (e1 || e2 and rc e1 e2 = Fst                                 [rc arm]
        and not exists e3 in E. vis e2 e3 and not comm e2 e3).      [absorber]

A visible non-commuting pair is ordered by visibility; a concurrent pair whose
conflict `rc` resolves is ordered by `rc`, unless `e2` is *absorbed*: some later
non-commuting visible successor `e3` in `E` cancels the rc-edge. A list `pi`
*witnesses* a version holding state `s` on event set `E` when `pi` enumerates
`E`, `pi` extends `loOn(E)` (never reverses an edge), and `pi` folds from
`init` to `s` (read up to the datatype's `eqObs` in the general signature). A
configuration is RA-linearizable when every stored version admits a witness.
(`def:lo`, `def:ralin` of `Sal/ConditionedMRDTs/sal-mrdts.tex`; `loOn`,
`IsRALinearizable3` in `Sal/CRDTs/Metatheory/Merge_Linearization_Set.lean`.)

## 2. Four strikes on the definition

Each strike names a clause that the published definition states as primitive but
that turns out to be a reachability-relative device or a proof-technique
artifact around a smaller invariant. The first three are recorded elsewhere; the
fourth is this note's result.

**Strike 1: the witness-extension clause is dropped, forced by the defeater.**
The paper's binary specification asks a merged version's witness to *extend*
witnesses of its two sides. `sec:defeater` (the add-wins skeleton, mechanized in
`Refutations/InterLca2op_Defeater_Arbiter.lean`) exhibits a fully LCA-legal
configuration where the tempting merged witness `[A_p, R_p, A_q, R_q]` restricts
on a side to a list that folds to the wrong side state. Witnesses do not extend
along the DAG, so the corrected `def:ralin` asks only that each version admit
*some* witness, independently. Extension is gone from the definition; the merge
layer is rebuilt on canonical states and a Join Lemma that never traffics in
witness lists.

**Strike 2: rc-directionality and chain-freedom are reachability-relative.**
The VC-minimality sweep found `rc_non_comm_directional` (VC1) redundant for
adequacy (its reverse direction never affects a fold; its forward direction is
enforced by CDVC3 on reachable concurrent pairs) and `no_rc_chain` (VC2)
sufficient but not necessary, weakenable to "loOn acyclic on reachable sets"
(the LWW register chains its rc along a total order and stays acyclic and
RA-linearizable). Both clauses over-specify: their true content is that `loOn`
order non-commuting reachable pairs and stay acyclic on reachable sets.

**Strike 3: the all-states quantification is a conditioning completion.**
VC3 (`cond_comm_lift`), VC4 (`mergeL_comm`), and the nonempty half of VC5
(`feasible_init`) quantify over the whole state universe, but adequacy only ever
evaluates them on canonical states of weakly-closed reachable sets. Each has an
RA-linearizable violator whose failure lives at an unreachable state (the VC3
and VC4 sentinels, the poisoned corner below the induction floor). Restricting
to reachable states is exactly what conditioning supplies; the unconditional
forms are the completion, not the content.

**Strike 4: the absorber (this probe).** The absorber clause removes edges. This
note asks whether removing it changes the RA-linearizability verdict, and if so
whether the change is observable or a fold quotient. The answer is decided
below.

## 3. The absorber dichotomy

**The edge-direction fact.** RA-linearizability asks each version's operational
state `op(v)` (fixed by the DAG dynamics: `do` on Apply, `mergeL` on Merge, and
*order-independent*) to be a fold of some `loOn`-respecting enumeration of its
event set. Write `plain` for the order that *drops* the absorber clause, keeping
every rc-resolved concurrent edge. Plain has a superset of loOn's edges, so its
respecting permutations are a subset, so

    folds_plain(E)  subseteq  folds_absorber(E)   for every E,

and therefore, for the fixed `op(v)`,

    op(v) in folds_plain(E)  implies  op(v) in folds_absorber(E),

that is, RA-lin under plain implies RA-lin under the absorber order. The
absorber order is the *weaker* (easier) property. The only possible separator is
a datatype RA-linearizable under the absorber order but not under plain; such a
separator makes the absorber load-bearing.

**Verdict: H-loadbearing, via acyclicity.** The separator exists, and it is the
canonical ORSet (add-wins set, all eight VCs green, mechanized RA-linearizable
under `loOn`). The mechanism is not a fold disagreement: it is order
*acyclicity*. Dropping the absorber makes the linearization order *cyclic* on
mundane reachable ORSet histories, so plain-RA-lin admits no witness at all.

**The minimal separator (hand-derived, deterministic in the harness).** Two
replicas each add then remove the same element `x`, then merge at the empty root
LCA. Events `a = add x`, `ra = rem x` on replica 0; `b = add x`, `rb = rem x` on
replica 1. In the merged version's event set `{a, ra, b, rb}` the plain order is

    a  -> ra   (vis: an add before its own later remove, non-commuting)
    ra -> b    (rc:  remove before a concurrent add, add-wins)
    b  -> rb   (vis)
    rb -> a    (rc:  add-wins again)

a cycle `a -> ra -> b -> rb -> a`, which no list extends. Plain-RA-lin has no
witness. The absorber removes both rc edges (each add is absorbed by its own
following remove), leaving the two vis chains `a -> ra` and `b -> rb`; every
interleaving folds to the empty live set, which is the operational merge state.
So the absorber order admits a witness and plain does not.

**Why no_rc_chain does not cover this.** The cycle alternates rc and vis edges;
its two rc edges (`ra -> b`, `rb -> a`) are not consecutive, so it is not an
rc-chain and VC2 does not forbid it. Acyclicity of the plain order is *not*
supplied by no_rc_chain. The absorber is the clause that supplies it, precisely
when `rc` opposes the visibility direction: add-wins orders a remove before a
concurrent add, while visibility orders an add before its own later remove, and
the two directions close a cycle. Overwrite datatypes never trigger this: the
directed LWW register, whose rc is the timestamp order and therefore agrees with
visibility, has no plain cycle and no separator (harness, directed candidate).

**Two routes, and only one is certified.** A separator version can arise two
ways: the *cyclic route* (plain order cyclic, no witness) and the *fold-value
route* (plain order acyclic but `op` is no plain fold, reproducible only by an
absorbed enumeration). The exhaustive two-state two-kind synthesis space (1408
tabulated specs, `space_s2x2` reused from `vc_synthesis_search.py`) yields, at
the configuration level, **9 separators, all via the cyclic route, zero via
fold-value**. Fold-value separator *versions* do occur, but only inside datatypes
that are already non-RA-linearizable under the absorber order (they violate VC3,
VC6, or VC8: the visible-swap datatypes the cond_comm_lift law exists to
exclude), so they never lift to a certified configuration-level dichotomy. Among
datatypes the metatheory certifies, the only separation is acyclicity.

**Observable versus internal.** The task's observable/internal split was framed
for a fold-value separator (do the two orders' witnesses fold to states that
differ under the query, or are they eqObs-equal?). The certified separation is
neither: plain-RA-lin is *vacuous* on the cyclic route (a cyclic relation has no
extending witness list at all), so there is no plain fold to compare against
`op`. This is strictly stronger than an observable disagreement, and it is not
eqObs-absorbable: coarsening the observation cannot rescue an order that has no
linear extension. The fold-value route, where the observable/internal question
would apply, is exactly the route that never survives to a certified separator;
for a flat datatype (query = identity) such a version is observable, and
coarsening eqObs to identify `op` with a plain fold would make it internal, but
either way it is confined to VC-violating specs.

**The antitonicity strike (demonstrated).** `loOn` is antitone in the event set
(`loOn_mono`): growing the set only adds absorbers, hence removes edges. Take
`E = {a, ra, b}` and `E' = E + {rb}` on the events above. In `E` the add `b` has
no later non-commuting successor, so the rc edge `ra -> b` is present; in `E'`
its own remove `rb` absorbs it, and `ra -> b` disappears. The harness prints the
two edge sets and the vanishing edge. This is the structural root of Strike 1:
a witness of the smaller version `E`, which must place `ra` before `b`, is not
forced by and can be violated under the larger version `E'`, because the edge it
respected is gone. Witness orders are not monotone in the store, which is why
the corrected definition cannot ask witnesses to extend, and why the
whole-configuration absorber scope (`Sal.Emulation.lo`) is unsound inside a
version: an event gains absorbers from other branches and silently loses an
order edge its own state depends on. The set-relative scope (`loOn(E)` ranging
over the version's own `E`) is the minimal fix; the absorber clause itself,
this note now shows, is load-bearing on top of that scope.

## 4. The invariant content, and a cleaner definition (conjecture)

The four strikes point at one reading. What RA-linearizability *invariantly*
asserts is:

> a version's state is, up to `eqObs`, the fold of some enumeration of its event
> set that extends an **acyclic arbitration** which orders every visible
> non-commuting pair by visibility.

Everything else in the published order is a *device* for producing such an
arbitration or a *completion* of it:

* rc-directionality and the rc arm are one way to arbitrate concurrent
  non-commuting pairs; the invariant needs only that non-commuting reachable
  pairs be arbitrated acyclically (Strike 2).
* no_rc_chain and the absorber together keep that arbitration acyclic; the
  absorber is the necessary half whenever rc opposes visibility (Strike 4, this
  note), no_rc_chain the half for consecutive rc edges.
* the all-states VC content is the conditioning completion of the reachable-set
  requirement (Strike 3).
* witness extension is not part of it at all (Strike 1).

**Conjecture (the arbitration refactor, phase 3b, not done here).** There is a
predicate `IsRALinearizable3Arb`, parameterized by an arbitration relation `arb`
required only to extend `vis`-on-non-commuting and to be acyclic on reachable
event sets, such that:

1. the published `IsRALinearizable3` (loOn form) is the instance `arb := loOn`,
   and loOn *is* such an arbitration on reachable configurations (the absorber
   and no_rc_chain are what discharge its acyclicity obligation);
2. the LWW register instantiates `arb` natively by its timestamp total order,
   with no absorber clause and no rc arm, and is RA-linearizable by the same
   predicate; and
3. rc-form arbitration transports into the refactor as one sufficient
   construction of `arb`, so the four demoted clauses (rc-directionality,
   no_rc_chain, chain-freedom, absorber) reappear as lemmas discharging
   acyclicity for that construction, not as parts of the specification.

The falsifiable next step is to state `IsRALinearizable3Arb` in Lean, prove the
loOn form is the rc-instance (transport in), and re-derive adequacy against `arb`
rather than `loOn`. The refactor fails if adequacy needs a property of `loOn`
beyond acyclic-arbitration-extending-vis-on-noncomm plus the fold quotient (for
example, if the Join Lemma consumes the rc form itself, not just its acyclicity
consequence). That is the phase-3b experiment.

## 5. What is anchored and what is conjectural

Anchored (machine-checked in the harness, PASS+FAIL, hand-derived expectations):
the edge-direction monotonicity; ORSet as a configuration-level separator
(deterministic minimal DAG plus random corroboration on single-element
histories); MVR, change-wins, and AWSetF3 as non-separators (MVR RA-lin under
both orders; change-wins and AWSetF3 non-RA under both, so they agree); the LWW
non-separator; the exhaustive S2x2 result that every certified separator is
cyclic and none is fold-value; the vanishing edge `ra -> b`. The four anchors
reproduce their known verdicts under both orders, so the null results are
meaningful.

Conjectural: the arbitration refactor of Section 4, named as phase 3b. The
published loOn-form definition remains the anchor. The thesis is that its four
audited clauses are presentation artifacts of that published definition, that
arbitration-acyclicity plus the fold quotient is its invariant content, and that
the four-law VC core (VC5-at-empty, VC6, VC7, VC8, with the update layer's
acyclicity and convergence content) is that content's proof theory.
