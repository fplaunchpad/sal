# Paper1 formalism and manuscript reconciliation

Concrete state equality suffices for all 20 positive production entries and
the additional exact paper OR-set. Fourteen use the guarded global-law route;
MVR, Core, and RichCore use the raw-order certified route; Embedded RGA, Sided
Embedded RGA, and native Peritext use the invariant-scoped certified route.
Semantic `abs` remains optional infrastructure; independent specification
refinement and metadata premises remain necessary.

Embedded RGA, Sided Embedded RGA, and native Peritext additionally have complete
certificates under the revised invariant-scoped criterion. Their concrete
commutation domains consist of sorted lists with certified insertion provenance. This changes the quantification in
the witness order, not the implementation, issuer, query, or independent
sequential language. The original 17-positive raw-order classification is
retained separately, including its Embedded RGA counterexample.

The retained raw-order campaign also establishes five obstructions with unchanged
implementations, public queries, specifications, and issuers. Queue cannot fit
the payload-only/no-chain policy class even at a represented certified root.
Embedded RGA, sided RGA, native Peritext, and Fugue have certified executions
that fail the retained full-event raw-order history criterion for every payload
policy. Restricting the algebraic laws alone does not fix this: the commutation
test inside the witness order still quantifies over arbitrary raw states.
The earlier 14-positive/eight-exclusion classification remains the result for
the globally quantified law contract; the new certified results are separate.

This note records manuscript recommendations and their evidence. Development
tasks remain exclusively in `../PRIORITIZED_REMAINING_WORK.md`. The current
manuscript is `../../sal_paper/main.tex`; only its included sections count as
active paper content.

## Two uses of abstraction

Semantic `abs` identifies implementation states for commutation, canonicality,
and merge reasoning. It is an optional generalization of concrete equality.
It preserves future update/query behaviour, not merely immediate answers.

Specification abstraction `α` relates implementation states to the independent
sequential specification. For OR-set it forgets tags and retains element
membership. Keep this even if the implementation metatheory uses concrete
equality. Removing semantic `abs` does not remove the sequential refinement
obligation.

## Changes to the manuscript

### State event guards explicitly

In `proof_strategy.tex`, replace ambiguous operation-level commutation
exactness with the event law

\[
t_a\ne t_b\land r_a\ne r_b\implies
\bigl(\neg(a\leftrightarrow b)\iff
rc(op(a),op(b))\lor rc(op(b),op(a))\bigr).
\]

The user supplies `rc` on application operation payloads only. Lift it to
events by projection. The payload-level no-chain restriction can remain:
timestamp-guarded event no-chain implies it by choosing fresh timestamps.

`GuardedReplay.Laws` states the corrected guards. `NeemScope.guarded_noncomm_exact`
proves the efficient OR-set's raw exactness for different replicas.
`GuardedPolicyControls` exhibits supported same-replica adds which fail to
commute despite having no add/add policy edge.

### Specify conditional commutation independently

State conditional commutation over three timestamp-distinct events, using
actual noncommutation between the second event and its absorber. The direct
guarded convergence proof needs this premise. Neem's manuscript's payload
conditional-commutation assumption supplies it. Neem's F* interface instead
uses policy conflict at that position; guarded exactness alone cannot equate
these premises for same-replica events.

Stop describing the conditions in `ralin.tex` as simply unchanged from Neem.
For the fourteen global-law positives, the displayed set-relative order
can stay: it uses actual noncommutation for causal edges and absorbers. Do not
replace these tests with policy conflict. To cover Embedded RGA, use the explicit
invariant domain described below in both clauses. The universal domain recovers
the original order (`InvariantOrder.order_universal`).

### Resolve specification visibility

The abstract in `main.tex` promises preservation of visibility for operations
that the specification distinguishes. The criterion in `ralin.tex` currently
requires only the implementation order and history admission.

Make the stronger criterion explicit. Define specification commutation through
observable history behaviour and require the witness to preserve visibility
between specification-conflicting updates. The Lean definition
`HistorySpec.Commutes` tests adjacent swaps in every prefix/suffix context,
including future updates and queries.

Implementation commutation implying specification commutation is a sufficient
bridge obligation, separate from history admission. It need not be mandatory
for every datatype: RGA uses an execution-scoped witness argument. Changing the
specification criterion does not remove the implementation commutation needed
for replay convergence.

### Correct the broken-remove argument

The no-op-remove implementation in `seq_spec.tex` satisfies the literal
criterion currently written. After an add and a no-op removal return `true`,
the witness `[remove, add]` explains the result.

It fails the universal sequential-simulation premise. It also fails the
stronger specification-visibility criterion, which retains add-before-remove.
These are distinct claims: failure of a sufficient proof obligation is not
failure of the criterion. `CriterionCounterexample` mechanizes this distinction.

### Parameterize sequential labels

Replace the categorical claim in `ralin.tex` and the abstract that a
specification never receives timestamps or replica IDs with an explicit
mapping `label(t,r,o)`. OR-set can project to `o`; RGA retains the supplied
identifiers. This preserves the ordinary-set specification without forcing
operation-only labels on every datatype.

The agreed RGA alphabet contains timestamp, replica ID, and operation. Its
current sequential semantics ignores the replica input but retains it in the
alphabet. The specification remains independent of the implementation.

### Describe issuance evidence and bridge scope

The lifting theorem in `seq_spec.tex` assumes correct sequential behaviour for
every event list. That is a useful sufficient route for OR-set, but is too
strong for specifications with issuance constraints.

Describe the alternative used for RGA: execution and issuance facts yield an
admitted, order-respecting sequential history, and replay uniqueness relates
its result to the stored state. Include the relevant freshness, identifier
origin, and anchor conditions. Qualify the theorem by the execution discipline
actually checked.

Reconcile `opsem.tex` with Lean's fresh child-snapshot fork and timestamp
assumptions, or state a correspondence. Lean retains causal timestamp
monotonicity and checks freshness against both the event registry and stored
versions. These facts should not silently enter a theorem whose semantics
states only uniqueness.

`rga.tex` currently contains a heading and is not included by `main.tex`. Add
an actual account if RGA supports the submission's claims.

### State the reconstruction premises of the merge proof

The five equations do not apply to arbitrary independently selected raw states.
Their premises identify represented histories, support, conflict/metadata
closure, freshness, and the chosen maximal event. The replay side supplies
finite representatives, uniqueness, and a peel/reconstruction witness.
`GuardedRawJoin.lean` defines `AbstractMRDT.Raw.MergeVCs`; its generic
`representationJoin_of_vcs` derives Join by strict finite-history induction.
Smaller-history representation premises come from that induction, not from an
assumed global merge theorem.

For efficient OR-set, the causal add equation requires every old tag killed in
the remainder to be covered by the reconstruction past. The local add equation
requires killed tags shared with the other branch to be covered by the merge
base. `GuardedEqualityVC` gives concrete PASS+FAIL examples showing why freshness
alone and an incoherent base fail. `GuardedRawORSetVC` derives the necessary
coverage from the represented histories. Preserve these premises in the paper;
changing equality alone does not make arbitrary replay representatives safe to
merge.

## Checked status and the equality decision

Both OR-sets now have closed guarded certificates with concrete equality. The
identity model retains every implementation tag; the final certificates do not
assume a nontrivial observational quotient or query completeness.

| Result | Checked declarations |
|---|---|
| Full guarded raw update laws, including actual noncommuting absorbers | `ORSet.Guarded.laws`, `EfficientORSet.Guarded.laws` |
| Five raw merge equations | `ORSet.GuardedRawVC.mergeVCs`, `EfficientORSet.GuardedRawVC.mergeVCs` |
| Generic VC-derived Join | `AbstractMRDT.Raw.join_at_sizes`, `representationJoin_of_vcs` |
| Concrete Join instances | `ORSet.GuardedRawVC.representationJoin`, `EfficientORSet.GuardedRawVC.representationJoin` |
| Exact-set ordinary and virtual execution correctness | `ORSet.RawExecution.executions`, `executionsV` |
| Efficient-set ordinary and virtual execution correctness | `EfficientORSet.RawCertificate.executions`, `executionsV` |
| Every stored state equals a semantic-order replay | Both certificate namespaces' `storedCanonical` |
| Same-history stored states are equal, including tags | Both certificate namespaces' `convergence` |

The execution conclusions use the independent ordinary-set history language,
retain full event inputs, and preserve specification-conflict visibility. The
specification is free to ignore the supplied metadata. Stored canonicality is
derived through execution induction, including every recursive virtual-base
merge; it is not an outstanding premise of either concrete certificate.

The ledger recursively requires the new raw VC induction and each datatype's
raw equation bundle. It rejects both previous direct Join routes and the
observational Join induction in these execution proofs. Standard-axiom audits
and the no-unproved-declarations check accompany the dependency checks.
The full registry `scripts/check-paper1.sh` gate passes with 3,477 build jobs;
`git diff --check` also passes.

Some replay-construction helpers still reuse proved observational lemmas,
notably the efficient set's joint-maximal peel construction. These are discharged
internal lemmas, not assumptions imposed on certificate users. Therefore the
result supports concrete equality as the core interface, but does not establish
that the proof implementation is independent of all observational machinery.
Retain that infrastructure rather than delete useful proved lemmas before the
remaining ports are complete.

## Complete registry classification

`GuardedCoverage.packages_eq_production` checks all 22 production packages,
including their original signatures and issuers. `counts` proves **14 positive
entries and eight global-contract exclusions**. Every positive carries a checked
identity-equality witness and ordinary/virtual execution correctness.
`ProvedResult.storedCanonical` exposes exact raw replay equality for every
stored version. The exact paper OR-set is a fifteenth positive datatype outside
that registry.

| Production entries | Result under the corrected contract |
|---|---|
| Grow-only-set, add-store, finite-add-store, counter, increment-only-counter, pn-counter, flat-grow-only-set, flat-grow-only-map | Concrete-equality certificates, independent total specifications |
| Bounded counter, plain RGA, TreeMove, AegisSheet | Concrete-equality certificates with original issuance-sensitive histories |
| Efficient OR-set | Concrete-equality certificate through the new five-VC raw Join induction |
| LWW register | Concrete-equality certificate with empty payload policy and chronological overwrite history |
| Queue | Guarded cross-replica enqueue conflicts force a payload self-edge forbidden by no-chain |
| MVR | Guarded pairs with the same payloads have different commutation verdicts |
| Embedded RGA, sided embedded RGA, Peritext embedded RGA, sided Peritext core and rich core | Observable conflict triangles contradict no-chain, even with distinct timestamps and replicas |
| Registered FugueMax | A guarded same-payload conflict forces a forbidden policy self-edge |

### Correct the LWW exclusion

Do not say that the LWW implementation cannot satisfy the restricted criterion.
Its previous timestamp-order policy violates no-chain, but an empty payload
policy works for its commuting max effectors. `LWW.GuardedPort` proves the full
VC-to-execution chain with the unchanged implementation and ordinary overwrite
specification. A chronological witness respects all causal visibility and
explains the timestamp maximum. This is another use of the scoped history
bridge; global implementation/specification commutation compatibility is not
necessary.

### State the scope of the remaining exclusions

`GuardedQueueMVR` and `GuardedRGAObstructions` prove impossibility for every
sound model under the current globally quantified `Guarded.Laws`. These are
not counterexamples to the existing production execution certificates.

In particular, all six RGA witnesses are rejected by their original issuers at
every origin. The embedded witnesses use an anchor of 3 with timestamps 1–3,
violating the required clock inequality. Registered FugueMax's witness carries
an empty coordinate chain, whereas prepared insertions always have nonempty
chains. `never_issuable` theorems and positive/negative issuer controls make
this boundary explicit.

If the paper intends to cover these implementations, the laws must be
reconsidered for eligible issued events and represented states, with a new
metatheory showing those eligibility conditions survive replay swaps and merge
reconstruction. The present exclusions do not prove that such an extension is
impossible. Merely changing equality to observational equivalence cannot fix
the current global contract: the witnesses are distinguishable by public reads.

Keep `α` for independent specification refinement; semantic `abs` is optional
for the supported core interface. Some internal replay lemmas still use the
observational development. New proof automation remains deferred.


### Certified-scope campaign: checked results

The campaign now restricts replay equations to represented prefix states and
eligible events. `CertifiedReplay` proves preservation under legal adjacent
swaps and updates, then exact equality of causally admissible enumerations
respecting the original semantic paper order. Requiring the replay to preserve
visibility is additional sufficient evidence; it does not remove or replace
the RA witness's specification-conflict visibility requirement.

The diamond interface is a replay theorem, separate from the restricted
policy contract in `CertifiedPolicy`. In particular, it does not itself assert policy exactness or
no-chain. Any paper theorem using this interface must identify which eligible
pairs need exactness and justify that scope. MVR now has a checked
concurrency-only exactness lemma: every overwrite target has a visible birth,
so concurrent certified writes commute by concrete equality. This differs
from globally quantifying exactness over every pair with different replicas.
Its original sequential legality and full-event labels are retained by
`CertifiedMVRHistory.replay_history`.

Embedded and sided RGA have checked scoped replay laws using original honest
event and coordinate evidence. All six variants now have raw VC-derived ordinary and recursive virtual
canonicality. `CertifiedHistoryBridge` transports an independently admitted
merge-free history through concrete represented-state uniqueness. Its public
result is explicitly the witness clauses; it does not silently manufacture
the missing scoped policy or merge obligations.

Queue's obstruction now has certified-scope evidence. The original issuer
admits a fork followed by concurrent `(1,0,enqueue(7))` and
`(2,1,enqueue(7))`. At their represented empty common root, both replay orders
are legal and expose heads `(1,7)` and `(2,7)` respectively. Payload-only
exactness forces a self-edge on `enqueue(7)`. The no-chain instance `(a,b,a)`
has both required timestamp inequalities and rejects that edge.
`CertifiedQueueMVR.Queue.certified_control` and `no_local_payload_policy`
check this argument. `no_scoped_policy` additionally refutes the actual
`CertifiedReplay.PolicyLaws` interface for every scope containing this history
and its represented empty root. This is an obstruction to the restricted sufficient
policy class, not a counterexample to Queue's independent execution-correctness
result. Issuance restriction alone cannot remove it.

The next checked increment closes MVR end to end. `CertifiedMVRVC` discharges
the five raw equations over execution-certified history representations;
`AbstractMRDT.Raw.join_at_sizes` derives Join. `CertifiedMVRExecution` preserves
that representation through ordinary stores and recursive virtual bases.
`CertifiedMVRCertificate` combines these results with the unchanged independent
specification, exact stored replay, scoped restricted laws, and explicit
specification-visible history witnesses. Recursive audits require the new VC,
Join, virtual, and history dependencies and reject the old direct MVR route.

`CertifiedPolicy` now makes the scoped policy class explicit: concurrent
eligible pairs are compared at represented prefixes where both are ready,
and the original pairwise timestamp-guarded no-chain condition is retained.
This is a stated change from globally quantified exactness. Readiness does
not assert original `CanIssue` at the reordered state: issuance is certified
at the original mint. `CertifiedMVRControls.mint_not_reissuance` proves that
both concurrent writes can be originally issuable, both replay orders legal,
yet regeneration of the second write after the first violates the issuer.

All six embedded RGA signatures now have original-issuer scoped replay laws,
including raw auxiliary-store and birth-set equality, and five raw merge VCs
connected to ordinary and recursive virtual execution canonicality. Core and
RichCore also have final RA certificates against their original independent
specifications. Their original issuer excludes native text deletion and uses a
separate deletion store. Chronological replay therefore respects all visibility
and explains their public queries. This restriction is derived from original
issuance, not added to make the proof pass. RichCore reuses the new Core
operational VC proof and proves its own query bridge.

Typed coverage preserves all 22 original packages: 14 retained guarded
positives, three scoped positives, four certified raw-order obstructions, and
one certified Queue policy obstruction. Exact paper OR-set is an additional
positive. All eight originally excluded entries now have either a complete
certified-scope positive result or an obstruction in an actual certified scope.

### Certified counterexample: which states define commutation in the order?

`paperOrder` still tests noncommutation on all raw implementation states.
Restricting the algebraic VCs to represented states does not change that test.
The difference now yields original-issuer certified counterexamples for
embedded RGA, sided RGA, and native Peritext, for every payload policy.

Insert A, fork, delete A and insert root B on the left, insert C after the
still-live A on the right, then merge. The original implementation returns
[B,C]. Global raw commutation requires delete-A before insert-B: although these
operations commute on represented states, they differ on an unsorted scratch
list. The independent specification requires increasing insertion IDs. Together
with deletion legality, this leaves A, delete-A, B, C, which cannot explain
[B,C]. The legal history A, B, C, delete-A does explain the result but violates
the required raw-order edge.

`CertifiedRGARawOrderObstruction`, `CertifiedSidedRawOrderObstruction`, and
`CertifiedPeritextRawOrderObstruction` construct the actual certified executions
and exclude all 24 event permutations in the unchanged independent languages.
Each has an admitted-history positive control and raw-order negative control.
The rejection does not use specification-conflict visibility; the full-event
raw-order witness is already impossible. This claim uses the agreed full-event
alphabet; a payload-projected manuscript language needs a separate alphabet
bridge. The malformed scratch list is not an execution state: it enters through the criterion's universal commutation test.

Thus restricting proof laws alone is insufficient for these implementations.
Retaining the raw criterion requires documenting these exclusions. Using
commutation over an appropriate represented-state domain in the witness order
is a separate formalism change. It is now defined and proved for Embedded RGA,
as described below; the original raw criterion is retained unchanged.

Fugue has a separate, smaller certified obstruction. Start at the empty state,
insert seed 1, delete it, then prepare replacement 3 at position zero. The
original preparation uses retained births and chooses `.ins 1 .L`, with the
appropriate original chain and bounds. The implementation returns [3]. Global
raw commutation imposes deletion-before-replacement, but the original list
specification forbids insertion naming an already deleted anchor. All six
permutations respecting that edge are illegal, irrespective of the answer.
`CertifiedFugueRawOrderObstruction` checks original preparation, issuance at
each step, full certified reachability, and the exclusion. The original
specification admits [seed, replacement, delete] with query [3]; its failure is
again the raw-order requirement. No fork or merge is needed in this example.

### Why Embedded RGA passes on main

Compared against local `main` at `223d4976b28d7df249c6c9d91475557ff9f1d196`,
`EmbedRGA.lean`, `ProductionRGA.lean`, `Metatheory/Correctness.lean`, and
`Join/SetRelativeReplay.lean` are unchanged. This preserves the implementation,
issuer, independent sequential specification, and original proof contract.

Main's `loOn` retains a causal edge when the supplied replay policy relates the
two events in either direction. `eRcOrder` relates an insertion only to deletion
of the identifier it allocates. `embedSemanticCommutes` is an explicit
operation-independence predicate implementing this classification; it is not
quantified concrete update commutation. `embedRc_noncomm` proves exactness for
that predicate. Main already contains a counterexample showing that this
classification differs from raw update commutation on unsorted lists.

The paper order instead retains a causal edge whenever the updates do not
commute on all raw states. For the certified four-update example, main omits
`delete(A) → insert(B)` and accepts `[A,B,C,delete(A)]`. The paper order includes
that edge. Insertion-ID legality then forces `[A,delete(A),B,C]`; C's absent
anchor makes that replay return only B. This difference is independent of the
payload policy, because the edge comes from the causal clause.

`CertifiedRGAOrderComparison.contracts_differ` proves both verdicts for exactly
the same certified configuration and independent specification. Additional
controls prove the explaining history respects main's order, main omits the
separating edge, and the paper order includes it for every payload policy.
All comparison roots use standard axioms. The sufficient adapter
`paperOrder_iff_loOn` requires exactness against actual raw commutation; the
syntactic `embedRc_noncomm` theorem does not supply that premise.

The newly required specification visibility is not used to reject the history;
the raw-order requirement alone suffices. Nor is the difference caused by
operation-only labels, changed queries, changed issuance, virtual merges, or
per-query witness selection. Main also permits an event-level replay policy,
whereas the paper interface asks for a payload policy, but no choice of the
latter removes the separating causal edge.

### Earlier main: raw replay and public histories used different orders

The September 8 commit `223d497` changed both the generic replay-law bundle and
the order. Its parent `50e48e2` (September 3) still had guarded equivalence of
raw noncommutation and directed conflict, with distinct timestamps and different
replicas, plus guarded no-chain. Its internal `loOn` used raw noncommutation in
the causal and absorber clauses, just as the paper order does. The analysis of
latest main above must not be attributed to this earlier snapshot.

Earlier main's public `IsSpecLinearizable` instead used a separately supplied
`InteractionSpec`. Embedded RGA supplied `embedInteraction`, constructed from
`embedSemanticCommutes`, and derived replay adequacy directly from `e_join_at`;
it did not instantiate the guarded `ReplayLaws` bundle.

In that snapshot's `embedSequentialCorrectness`, the proof obtains an internal
raw-order-respecting replay `ops`, then replaces it with the insertion-first
`EmbedWitness.canonical ops`. It proves the two implementation folds equal,
but only proves that the new history respects the public `interactionLoOn`.
It does not retain raw-order respect for the newly chosen sequential witness.

The concrete separation is checked in `CertifiedRGAOrderComparison`:
`earlier_internal_replay_control` shows that [A,delete-A,B,C] respects the
empty-policy raw order and reconstructs the implementation's [B,C], while its
independent sequential read is [B]. `earlier_public_history_control` shows that
[A,B,C,delete-A] respects the earlier public semantic order and is admitted with
[B,C], but fails the raw paper order. These controls reproduce the relevant
old order clauses in the current environment; they do not import an old build.

Thus earlier main also did not establish one history simultaneously respecting
raw commutation order and explaining the independent sequential result. The
paper criterion imposes that combined requirement. This explains its failure
even relative to the version before September 8's policy refactor.

### Why Neem's equality proof does not settle this issue

The local Neem RGA uses a pair of birth and tombstone sets
(`code/mrdts/Replicated-Growable-Array/App_mrdt.fst`). Updates add to the
appropriate set and merges take unions. Its interface tests commutation over
all concrete states using application equality. This differs from Sal's
embedded live-list representation, whose operations assume sorted coordinates
in reachable states. Neem's success with equality does not prove that arbitrary
raw live lists satisfy the same equations.

The active Sal manuscript describes commutation on any state in `ralin.tex`
and globally quantified replay equations in `proof_strategy.tex`. A paper that
claims the certified extension must explicitly state the event/state scope of
its equations, the preservation obligations through replay and virtual merges,
and the chosen scope of commutation in the witness order. Semantic abstraction
remains optional infrastructure; every positive certificate above uses concrete
equality. Merely replacing equality by query equivalence does not resolve the
choice of states over which commutation is quantified.

### Checked change: commutation on an invariant domain

For Embedded RGA, the revised criterion is now proved end to end in
`CertifiedRGAInvariantCertificate`. It uses concrete equality throughout.
`CertifiedRGAInvariant.Valid Γ C s` means that `s` is sorted and every live
record equals an insertion record minted in the certified context `C`.
It overapproximates reachable states: arbitrary supported subsets are allowed,
and an event may already have been applied. The domain does not mention a
desired witness, query answer, or simultaneous readiness of the tested pair.

`InvariantOrder.Commutes D Inv a b` means that applying `a;b` and `b;a` produces
equal concrete states for every state satisfying `Inv`. Both the causal clause
and the absorber clause of `InvariantOrder.order` use this definition.
The application policy still receives only operation payloads. Event eligibility
and issuance evidence remain separate from that interface. Taking `Inv` to be
true recovers the original full-event criterion (`versions_universal`).

The proof establishes the following obligations:

- Initialization, every already-issued update, arbitrary reordering/repetition
  of eligible updates, and three-way merge preserve validity. These are stronger
  than preservation only at fresh causally ready prefixes.
- On eligible pairs, invariant commutation is exactly the existing
  `embedSemanticCommutes` classification. An insertion and deletion of its own
  identifier remain noncommuting, witnessed by the valid empty state.
- Generic replay convergence and event-set restriction retain the same fixed
  state domain. The implementation replay is causally legal; its representation
  is obtained from the new raw VCs, generic Join induction, and certified
  ordinary/recursive-virtual execution theorem.
- A single explicit insertion-first history respects the revised order and
  specification-conflict visibility, folds to the exact stored implementation
  state, and is admitted by the unchanged independent specification with the
  actual query result. This history may reorder commuting causal updates;
  it is proved separately from full-causal implementation replay convergence.
- Actual synthesized recursive virtual merge bases satisfy the invariant
  (`virtual_base_valid`), in addition to stored versions.

The four-event control now passes: `[A,B,C,delete-A]` explains `[B,C]`, the
spurious `delete-A → insert-B` edge is absent, and `A → delete-A` remains.
`CertifiedRGAInvariantControls.certified_execution_comparison` proves opposite
verdicts for the revised and retained raw criteria on exactly the same certified
execution. The malformed scratch carrier is excluded by the explicit invariant.

The manuscript change belongs in `ralin.tex`: introduce a declared valid-state
domain and replace both universal raw-state commutation tests with commutation
over that domain. In `proof_strategy.tex`, state the event/state premises and
preservation obligations explicitly, including all replay and merge states used
by the derivation. For this context-indexed domain, restricting a version's event
set must not silently redefine the commutation domain. Keep the independent
specification-visibility and history-admission obligations.

This first invariant-scoped port was Embedded RGA. The subsequent Sided and
native Peritext ports and the distinct Fugue result are described below. Queue's
certified policy obstruction remains separate.
It also does not claim that invariant closure alone proves the merge VCs or
the sequential-history bridge. Semantic `abs` remains optional; this result
needs no observational quotient. The manuscript itself has not been edited.

### Remaining invariant ports: two positives and a stronger Fugue obstruction

`CertifiedSidedInvariantCertificate` and `CertifiedPeritextInvariantCertificate`
prove the same full target as Embedded RGA: invariant closure, scoped replay
laws, new VC-derived stored canonicality, independent history admission with
specification visibility, ordinary and recursive-virtual finite executions,
and validity of actual virtual merge bases. Sided's invariant uses its native
coordinate order and insertion provenance. Native Peritext specializes the
generic Embedded result at its original `Element` payload; its character and
format-boundary operations, public query, renderer, and specification are
unchanged. Each original four-event counterexample passes the revised criterion
and still fails the retained raw criterion. PASS+FAIL controls check the original
query results; native Peritext also checks its rendered output.

FugueMax's implementation proof also succeeds. `CertifiedFugueInvariant` uses
sorted live records with certified insertion provenance, and a birth set
containing only supported insertion records. It proves closure under arbitrary
eligible updates and merges, exact commutation classification, and stored and
recursive-virtual-base validity. `CertifiedFugueInvariantReplay` supplies the
new scoped replay laws and exact canonical replays through the existing new
VC-to-Join route. No observational quotient is needed.

However, Fugue's full independent-history criterion still fails, for a reason
that is independent of implementation commutation. The original certified trace
is:

1. Insert seed 1.
2. Delete seed 1.
3. Prepare and insert replacement 3. The original issuer consults retained
   births and produces an insertion to the left of seed 1, although seed 1 is
   no longer live.

The implementation returns `[3]`. The unchanged ordinary-list specification
requires an insertion's non-root anchor to be allocated and not yet deleted.
Consequently `[seed, replacement, delete]` is admitted with `[3]`, while
`[seed, delete, replacement]` is illegal. This is a contextual specification
noncommutation witness for the deletion and replacement. They are causally
ordered in the original execution, so specification visibility retains
`delete → replacement`. Every permutation respecting that edge is illegal.

`CertifiedFugueInvariantObstruction.no_spec_visible_history` excludes every
answer. `certified_failure` proves failure for every state invariant and every
operation policy; it does not use the raw scratch-state counterexample.
`valid_execution_counterexample` additionally proves that all four concrete
states of the original trace lie in the independently justified closed domain.
`implementation_spec_separation` establishes both sides of the distinction:
the effectors commute on every valid implementation state, while the independent
history language distinguishes their order.

This is an issuer/specification incompatibility under the stronger criterion.
Changing `abs` or restricting implementation commutation cannot resolve it.
To include Fugue under that criterion, a later design decision must reconcile
its deleted-birth anchor preparation with the public specification, or reconsider
the specification-visibility requirement. This campaign changes none of them.
The manuscript should not claim that valid-state commutation alone admits all
RGA variants. Record this limitation alongside the explicit specification-
visibility definition in `ralin.tex` and the RGA case study.

The resulting coverage is 20 positive production packages across the retained
and invariant-scoped routes, plus exact paper OR-set. Fugue's history obstruction
and Queue's policy obstruction are the two remaining production cases. The old
`CertifiedCoverage` registry intentionally retains its 17-positive raw-order
classification, allowing both criteria to be compared without rewriting results.

### Validation of the certified campaign

Both `scripts/check-paper1.sh` and `scripts/check-mrdt-refactor.sh` pass on the
completed classification and all three invariant-scoped RGA ports, including
the stronger Fugue obstruction (3543 and 3571 Lean jobs respectively). The latter checks 22 exact public contracts, 13 gate
tests, 187 runtime tests, and 569 benchmark records. Recursive theorem audits
require the new VC-to-Join and virtual-execution dependencies and reject the
legacy direct correctness routes. All audited new final roots use only Lean's
standard axioms. The invariant certificates additionally audit their new
commutation, history, scope-restriction, and generic convergence dependencies.
The Fugue specification-only rejection excludes dependencies on the earlier
raw-order rejection and its scratch-state conflict. Independent cross-reviews
and root source/gate verification cover the new ports and counterexample.
Original datatype definitions and sequential specifications
were preserved; helper proofs expose existing evidence separately from old
Join theorems. The manuscript itself has not been edited.

### Presentation of the direct proof route

Keep the paper's main development centered on sufficient VCs, execution and
issuance evidence, and the explicit history criterion. The mechanization can
factor the execution theorem through a semantic merge premise and establish
that premise directly or from VCs. This modularity does not require a separate
direct-route presentation in the paper. A short mechanization remark is optional.

The case-study coverage claim must distinguish these routes: an example proved
only through a direct merge argument cannot count as satisfying the advertised
VCs. Datatype-specific independent-history proofs are a separate issue: even
when the merge premise follows from VCs, the specification bridge still needs
justification. The new anchored queue work is intended to use the checked
VC-to-Join route for representation and a FIFO scheduling proof for that bridge.

### Anchored-enqueue queue: separate design and FIFO bridge

This variant leaves the existing Queue and its policy obstruction unchanged.
Its enqueue records the issuer's current tail identity and immutable coordinate;
dequeue records the current head identity. An empty queue uses the root anchor.
Concurrent enqueues sharing a tail are ordered deterministically, with the larger
fresh timestamp first. The implementation reuses the compact Embedded RGA
live-list kernel but restricts original issuance to tail insertion and head
deletion. Its public query returns the tagged head, as the existing Queue does.

The independent sequential specification is a list of identity/value pairs.
Enqueue appends and ignores its recorded anchor and coordinate. An identity can
be born only once in a history. Dequeue removes the named head, or is a no-op if
that identity was born and has already been removed. Removing a live non-head
or a never-born identity is illegal. These rules are stated independently of
the implementation's sorted-insertion operation.

No separate full birth set or tombstone set is stored. Surviving records retain
their immutable coordinates, which carry anchor-position information after
deletion. This result should not be described as elimination of all historical
metadata or as a bounded-space result: the coordinates can grow. Head-only
deletion is essential to the FIFO argument. In particular, an observed tail
can also be a deletable head only in a singleton queue.

The central scheduling lemma is derived from actual issuance: if enqueue A is
visible to enqueue B, any deletion of B has a deletion of A in its causal past.
Consequently the removed births form a downward-closed set among causal
enqueues. A sequential witness processes deletions in timestamp order, placing
each removed birth immediately before its first deletion. Duplicate deletions
then act on absent identities. It appends all surviving births in their final
coordinate order. The surviving suffix comes from stored-record provenance,
not an assumed explaining history. An unrelated enqueue and dequeue commute
in the independent history language, including its legality checks, permitting
the reordering used by this schedule.

The representation proof uses concrete equality and the checked new merge VCs.
The FIFO bridge is a separate argument; an Embedded RGA sequence-specification
certificate does not establish this queue specification. Likewise the internal
full-value-list query alone does not establish the public tagged-head result:
the witness reconstructs the exact tagged list before projecting its head.

Independent finite search found no counterexample in 40,000 generated histories
with at most nine updates and checked 441,459 stored snapshots. It included
ordinary merges, noninitial merge ancestors, honest dequeues and postmerge
updates. It skipped 708 multiple-base cases and is not evidence of recursive
virtual-merge coverage. The durable script and output are
`scripts/research/anchored-queue-search.py` and
`docs/anchored-queue-search-results.json`.

The assembled Lean roots `AnchoredQueue.History.correct`, `correctV`,
`executions`, and `executionsV` prove the criterion for the actual public
signature, including arbitrary recursive virtual-base executions. Their only
execution premise is the certified reachability or trace relation. They derive
the schedule and exact surviving suffix, with no additional witness assumption.
All roots use standard Lean axioms only. This universal theorem supplies the
recursive virtual-merge coverage that the finite search lacks. The public
certified trace supplies a separate nonvacuity control; its virtual control is
an ordinary trace embedded in the virtual relation, not a multiple-base example.

For the manuscript, describe this as an additional queue design rather than
claiming the original Queue's policy obstruction disappeared. Its case study
should state the tail/head issuance contract, the independent FIFO language,
and the retained coordinate information. The substantive bridge lemma is that
removing a causally later enqueue implies its earlier causal enqueue has already
been removed. The original 22-package registry and its 20 positive entries are
unchanged; this is a separate Lean variant with no JavaScript implementation.

Final validation passes both gates: 3559 paper1 Lean jobs and 3587 production
Lean jobs, with 22 exact public contracts, 13 certificate-gate tests, 187 runtime
tests and 569 benchmark records. The ledger checks standard axioms and recursively
requires the new merge VCs, constructed FIFO schedule, live-birth extraction,
causal-removal lemma, public-language commutation and virtual-base transport.
Sol 6.1 implementation and independent review were followed by root source
review and gate verification. The manuscript has not been edited.
