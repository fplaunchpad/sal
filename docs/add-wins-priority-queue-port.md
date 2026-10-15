# Priority queue reconciliation: published source and same-record repair

## Certified same-record repair — 15 October 2026

`Instances.PriorityQueueSameRecord` intentionally changes Algorithm 2's priority
selection: both the innate priority and acquired increments come from the same
latest surviving Add record. Preparation guards, observed insertion snapshots,
per-record increment attachments, observed removals and union merge remain
unchanged. Thus a new Add after removal does not inherit the old record's
increments. This is a certified intentional semantics change, not a source-faithful replacement
or a claim that the published algorithm has a convergence defect.

The independent sequential model in `Paper1.PriorityQueueSameRecordSpec` is an
ordinary finite priority map. Add is a total overwrite; Inc adds to a present
priority and is a no-op on absence; Remove clears and is a no-op on absence.
Absent get-priority and empty get-maximum return `none`. Abstract cells store
only `Option Int`, with finite live support. They contain
no birth IDs, observation snapshots, magnitude counters or history sums. The
published Add-absent and Inc/Remove-present guards apply at issuance, not at each
prefix of an explaining sequential history. This choice is explicit: requiring
Add-absent at every sequential prefix excludes concurrent successful Adds.

The repaired query uses actual finite live birth support. Maximum ties choose
the greatest element ID, and `rmvMax` observes the local maximum, issues the
existing Remove of that identity, and returns the observed pair. It is not a
globally atomic extraction operation. Raw states are totalized by querying only
known live births; a forged birth-ID collision chooses the greatest innate
value. The certified stored-version domain transfers whole causally closed
versions, rather than permitting the source op-based network's transient early
Inc placeholders as issuer states. Globally unique operation timestamps and
causal timestamp monotonicity are supplied by the current Sal configuration.

Current kernel-checked coverage:

- `PriorityQueueSameRecordVC.fiveVC`, `representationJoin`, `joinAt`, and
  `canonicalVersions` derive replay/convergence for ordinary and recursive
  virtual-base executions through the shared five-VC induction.
- `priority_selected_record` identifies an actual live, latest-timestamp birth
  and that same birth's acquired attachments. `getMax_sound`,
  `getMax_none_iff`, and `priority_none_iff` certify the query interface.
- `priority_remove` and `elements_remove` prove exact local removal of the
  selected identity and preservation of other elements.
  `PriorityQueueSameRecordSpec.rmvMax_refines` certifies the returned pair and
  resulting ordinary map for the derived local client operation.
- `cross_key_commutes` proves contextual commutation of distinct element
  updates in the full ordinary history language, including maximum queries.
- `PriorityQueueSameRecordProvenance.birthComplete_versions` rules out unborn
  increment attachments at every allocated ordinary/recursive version.
  `honest_increment_birth`, `honest_remove_birth`,
  `attached_increment_visible`, `surviving_birth_successor`,
  `absent_birth_has_remover`, and `absent_no_add_after_maximal_remove` establish
  actual issuance provenance and both ordering cases. No hidden stronger
  preparation guard is used.
- Seven hand-derived PASS+FAIL SPOT blocks distinguish reset **2** from **7**,
  repaired unique-winner **11** from source **12**, attachments to an unselected
  Add, independent MCW ties, computed maximum ties and winner changes, and
  observed removal followed by reinsertion.

`PriorityQueueSameRecordHistory.historyAdequacy` is now kernel-checked.
`present_replay` and `absent_replay` construct each element's causal ordinary
history; `acquired_fold` matches identified attachments to ordinary signed
addition under the supported execution's distinct timestamps.
`assemble_key_histories` composes those histories into **one** word matching
**every** query of the full finite map. `PriorityQueueSameRecordCertificate`
exports `certified`, `certifiedV`, `executions`, `executionsV`, and `convergence`
for exact source preparation and the current ordinary/recursive stored-version
execution model. These are independent-history SpecificationRA results, beyond
state convergence. The old measured implementation is preserved until the
parent integrates the explicitly renamed replacement; its old certificates are
not used to claim this result.

`PriorityQueueSameRecordAudit` checks every public ordinary/recursive endpoint's
transitive dependence on the **named** `fiveVC`, shared `Raw.join_at_sizes`,
`historyAdequacy`, both replay cases, honest birth provenance, `acquired_fold`
and all-key composition. The targeted audit build passes with standard logical
axioms only. The max client's `prepared_remove_issued` theorem also proves its
emitted event satisfies the actual source Remove guard; event freshness remains
the ordinary execution premise.

The constructive proof strategy is per element. For a present element, place
all superseded updates before its selected surviving Add, then exactly the Incs
attached to that Add. Honest preparation makes the latter portion upward closed
under same-element visibility: a later Add fails the absence guard, while a
later Remove would destroy the surviving record. For an absent element, choose
a visibility-maximal Remove, put all Adds before it, and leave any following
Incs as ordinary absent no-ops. Distinct-element updates commute in the
independent language, so their explaining orders can compose while preserving
specification-conflicting visibility. These ordering, aggregation and composition steps, and the final scoped
history certificate, are now checked theorems.

Parent-side exhaustive dynamic programming searched causal serializations for
**29,880** reachable one-element versions from **2,000** seeds, at most eight
events and three replicas, with actual issuance guards and random merges. Every
repaired answer was admitted; source **12** was rejected by the four-event
control, and repaired **11** was admitted. This is bounded evidence, not a
universal theorem. The ordinary updates in that experiment are the explicit
total operations described above.

Preserving *all* cross-element causal edges is a stronger, false goal even for
plain add-wins existence. Two branches from empty can do
`Add(x,10); Add(y,200); Remove(y)` and
`Add(y,20); Add(x,100); Remove(x)`. Their merged survivors are the first x and
first y. A resetting ordinary replay preserving both full causal chains would
require the cycle `Remove(x) < first Add(x) < Remove(y) < first Add(y) < Remove(x)`.
Those crossed element edges commute in the ordinary specification, so this
boundary does not obstruct the actual specification-conflict criterion.

## Published source result

The source-faithful investigation has a checked negative result. Algorithm 2's
Most-Change-Win query does not admit the intended ordinary priority-queue
explanation when the sequential history preserves the source causal Add-to-Inc
edges. With Add-absent imposed at every sequential prefix, concurrent successful
Adds already have no legal serialization, even without any order constraint.
That strict sequential guard is our specification choice, not an implication of
the source issuance guard. Neither result refutes the paper's stated strong
eventual consistency theorem.

The previous measured flattened variant is preserved below. Its existing
certificates have not been reused to claim correctness of the source model or
same-record repair. Catalogue, measurement and manuscript changes belong to the
parent's separate scope decision.

## Reality oracle and encoded source semantics

The primary authority is Zhang et al., *Conflict-free Replicated Priority Queue:
Design, Verification and Evaluation*, Internetware 2023, Sections 2.1–3.3 and
Algorithms 1/2, in `_references/3609437.3609452 (1).pdf`. The archived Sal audit
records the former simplification; it does not define the published behavior.

`Instances.PublishedAddWinsPriorityQueue` is an executable state-based
translation using integer-valued source inputs. Birth payloads, increment
attachments and observed-removal tags are retained. Each increment attachment
names its observed Add timestamp and an effect ID. The ID deduplicates merged
copies of the same effect, corresponding to the source's exactly-once delivery
assumption. An element-wide acquired sum is never used.

The record projection computes, for each Add identity, its immutable innate
value, acquired sum and sum of increment magnitudes. Inc and Remove preparation
snapshot exactly the currently live Add identities. Add preparation requires
absence; Inc and Remove require presence. Remove disables the observed records
and their priority contributions. Consequently
`Add(7,10); Inc(7,5); Remove(7); Add(7,2)` reads **2**, not **7**.

The query independently selects the latest live Add's innate value and a live
record with greatest accumulated magnitude for the acquired value. Maximum and
its derived observed-removal client use the admitted priority answers. The
source's unqualified choices are retained as relations represented by finite
sets of possible answers. These sets are diagnostic query evidence; the paper's
API itself returns individual integers and element/priority pairs.

## Kernel-checked obstruction

Two isolated replicas perform this honest trace:

| Replica A | Replica B |
|---|---|
| `Add(7,0)` with tag 1 | `Add(7,10)` with tag 2 |
| `Inc(7,+2)`, observing only tag 1 | `Inc(7,+1)`, observing only tag 2 |

Both Add guards see absence. Each Inc guard sees presence and snapshots exactly
its own Add. The effect timestamps are globally distinct. After merging, the
source records are `(tag 1, innate 0, acquired 2, count 2)` and
`(tag 2, innate 10, acquired 1, count 1)`. Thus the source has a unique latest
innate winner and a unique Most-Change-Win winner and reads **12**. Summing both
increments would give **13**, which the source rejects in this trace.

`Paper1.PublishedPriorityQueueObstruction` supplies two independent ordinary
machines. The exact machine stores only element priorities and enforces Add
absent, Inc/Remove present, and get-priority present. The relaxed comparison
machine permits resetting Add on an existing element. Neither stores Add IDs,
observation sets, magnitude counts or merge state.

`relaxed_no_causal_serialization` kernel-enumerates all 24 permutations. Every
permutation preserving both source Add-to-Inc edges returns **2, 3, 11 or 13**,
never **12**. `ordinary_no_serialization` rejects every permutation under the
exact ordinary guards, with no causal hypothesis. `strict_two_adds_obstruction`
minimizes this guard issue to the two successful concurrent Adds.
`ordinary_positive_control` proves the exact history language admits an honest
single-branch Add/Inc trace and rejects its nearby wrong answer. These are
specific refutations, not an always-rejecting specification.

The relaxed result depends on preserving those causal edges. Prepared metadata
effects commute, so an implementation-only empty-policy criterion can omit
such edges. `relaxed_add_inc_conflict` proves that the ordinary specification
regards Add and Inc as contextually conflicting despite concrete effect
commutation. The relaxed counterexample therefore refutes causal ordinary
linearization and the specification-conflict-visibility candidate; it is not
silently promoted to a refutation of a weaker order criterion. The exact guarded
ordinary-language obstruction is independent of this distinction.

## Independent source review — 15 October 2026

The parent inspected the original Algorithm 2 on printed page 305, Sections
3.3 and 5.1.3, and the staged source model and counterexample. Lines 7–9 select
the latest innate value and the greatest-change acquired value independently;
line 28 accumulates both signed increments and their absolute magnitudes.
Thus the two-record example really returns 10 + 2 = 12 under the published
rule, with no tie or null-placeholder ambiguity. Independent enumeration of
the six causal serializations again produced only 2, 3, 11 and 13. The parent
reran both new SPOT targets together; the build passed (3,429 jobs).

Scope matters: the Add-absent condition occurs in **prepare** (line 12).
Carrying it into every sequential prefix is a choice of sequential contract,
not a consequence of issuance alone. The strict two-Add obstruction must be
reported with that qualification. The resetting-Add comparison removes this
particular guard issue, but still requires preserving the two Add-to-Inc edges.
Neither result is a contradiction of the source paper: Section 5.1.3 specifies
strong eventual consistency, not ordinary sequential priority-queue conformance.
No literal mutable-record refinement or production integration is asserted.

## Published underspecification retained explicitly

- Algorithm 2 does not resolve Most-Change-Win count ties. Honest `+1` and `-1`
  increments on separate concurrent Add records can yield equal magnitude
  counts but different acquired values. With latest innate 10, the paper permits
  **9** or **11**. The source model preserves both choices.
- An Inc delivered before its Add creates a null-innate placeholder. Lookup
  includes the placeholder, but the paper does not define null arithmetic for
  get-priority. `unresolvedInnate` records that gap. Matching Add delivery fills
  the innate value while preserving the acquired value and magnitude count.
- Algorithm 2 annotates increment amounts as real numbers while declaring
  get-priority integer-valued. The current executable oracle explicitly uses
  integer inputs. The refutation uses integers and hence is unaffected by a
  later decision to support the larger numeric domain.
- Add timestamps are required to be unique and totally ordered; causal
  monotonicity is not stated. Exactly-once eventual message delivery is stated
  in Section 5.1.2. Add-Win does not require causal delivery, which is why early
  placeholders are explicitly handled.

## Evidence and remaining work

`lake build Sal.MRDTs.Instances.PublishedAddWinsPriorityQueueSPOT` checks the
source model, obstruction theorems and ten PASS+FAIL conformance controls.
The controls cover reset on re-add, absent-operation rejection, observed tags,
early placeholders and later filling, MCW ties, actual maximum and derived
maximum removal. Audited declarations use only `propext`, `Classical.choice`
and `Quot.sound`.

The attachment representation has executable preparation/effect behavior and
commuting effects. A complete refinement proof to literal Algorithm 2's mutable
record store and a full five-VC convergence certificate are not yet claimed.
There is no ordinary/recursive ordinary-PQ RA certificate for this published
model. The checked obstruction prevents supplying the intended independent
history bridge by merely changing proof automation or weakening the read.
A useful next research question is which innate/acquired selection policies and
sequential operation contracts admit such an explanation, while preserving the
source observation semantics.

---

## Preserved earlier flattened Sal variant

The production port answers a precise question: can the existing Sal priority
queue, including its noncommuting same-element Add/Remove pair, historical
signed increments, four observable queries and derived maximum removal, satisfy
the current five-equation merge framework and an independent sequential
priority specification? The answer is yes. No additional
state-dependent issuance guard is required.

This ports the Sal implementation on `archive/conditioned-mrdts-2026-08-21`,
not the complete Internetware 2023 priority-queue algorithm. The archived audit
`docs/aw-crpq-vs-paper.md` records the difference: the paper tracks increment
observation and change counts per Add record and uses Most-Change-Win; Sal
flattens increments into one retained set and sums all matching amounts.
This port preserves that flattening, including increments issued while an
element is absent and increments retained across removal and re-addition.

## Concrete behavior

The state is a finite set of `(element, timestamp, innate)` Add records and a
finite set of `(element, timestamp, signedAmount)` increment records. Coordinates
are reordered from the archive, without changing their interpretation.

- `add element innate` inserts an Add record.
- `inc element signedAmount` inserts an increment record.
- `remove element` filters all Add records for that element. It preserves all
  increment records.
- Add records merge with `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)`.
- Increment records merge by union. The archived survivor merge is equal to
  union when ancestor increments occur in both branches; `increments_mono`
  establishes these inclusions for canonical ancestor histories and
  `historical_increment_merge` proves the equality. The union extension on
  arbitrary incoherent states has no effect on honest execution semantics.
- `getPri` returns `none` when the element is absent. Otherwise it returns the
  innate priority of the live Add with greatest timestamp plus the sum of every
  retained matching increment amount.
- `empty` reports whether there are no live elements; `lookup` reports element
  membership; `getMax` returns `Option (Nat × Int)` with the highest signed
  priority and greatest element ID among tied priorities. Empty queues return
  `none`. `getMax_sound` proves that a selected pair is live and dominates every
  live priority; `getMax_none_iff` proves that selection returns `none` exactly
  when there are no live elements.

The public full-query signature is `Instances.AddWinsPriorityQueue.FullD` on the
archived natural-number element IDs. Its `FullQuery`/`Answer` alphabet includes
all four queries. The older generic per-element `D α` is the internal
operational proof carrier, not a second queue implementation.

Equal Add timestamps are broken by innate payload on arbitrary raw states.
Honest execution gives globally unique event timestamps, so this tie extension
is unreachable. An increment's repeated delivery is idempotent. Signed amounts
may make a priority negative.

## Independent sequential model

`AddWinsPriorityQueueFullSpec` extends the independent compressed cells with
finite live-element support. Each cell has only the largest live
`(timestamp, innate)` candidate and a set of increment identifiers and amounts.
It has no ancestor, merge operation, or set of live Add records. Add inserts
the element into support and takes the maximum candidate; Remove erases the
element and clears the candidate; Inc adds its identifier and amount without
changing support. Remove leaves increments intact. Maximum selection examines
only this finite support, so arbitrary function-valued cells do not require an
infinite search or an invented default candidate.

The identifiers allow the model to describe repeated raw delivery. Under the
framework's fresh-timestamp execution discipline they describe ordinary addition
of each signed increment once. The projection from concrete Add records to one
winner is a proper compression, and its update and observation equations prove
the full-query `historySound`. `compatible` proves preservation of contextual specification
commutation on every abstract state, rather than relying on projection
surjectivity or a selected trace.

## Theorem coverage and execution conditions

`AddWinsPriorityQueueVC.fiveVC` proves commutativity, initial-state identity,
causal replay, local redistribution and shared replay directly. Its premises
use canonical Add survival, complete increment membership and globally unique
event timestamps. These proofs invoke no representation Join. The common finite
event-set induction then supplies `representationJoin`.

`AddWinsPriorityQueueFullCertificate` transports the five equations through
the existing generic query-only lift; the update signature is definitionally
unchanged. It supplies `certified` and `certifiedV` for every
allocated version, including stored ancestors and recursive virtual merge bases.
`executions` and `executionsV` also explain execution traces with reads.
Issuance is `CanIssue := True`; honest minting, global timestamp freshness,
causally closed supported histories and valid merge-base evidence come from the
certified transition systems. Arbitrary fabricated ancestor states are outside
these endpoint theorems.

The read-side theorems cover observed removal, retained acquired priority,
priority changes under fresh signed increments, concurrent Add survival, maximum
soundness and completeness. The original twelve PASS+FAIL SPOT blocks cover
these priority behaviors; eleven full-interface blocks additionally cover empty
and membership reads, actual maximum selection, deterministic ties, negative
priorities, changing maxima, and the derived removal client. Independent-model
history tests reject stale maximum and reset-on-remove answers.

## Derived maximum-removal client

`prepareRmvMax` observes the current maximum pair, retains it as the client
result, and emits the existing `remove selectedElement` operation with supplied
timestamp and replica. Empty queues emit no event. `rmvMax` describes the local
application and returned pair. `rmvMax_refines` proves that both the returned
pair and projected resulting state agree with the independent sequential
client; `prepared_remove_effect` proves that the selected element is locally
absent afterward and historical increments remain intact.

The issued operation removes its selected identity on replay. It does not
recompute the maximum in the replay state. This implements a local derived
operation, not atomic global extraction across replicas: two replicas can
observe and return the same maximum pair concurrently. A PASS+FAIL trace pins
that behavior. The full RA endpoints certify the four query forms and issued
ordinary updates; they make no global atomic-pop guarantee.

Every audited endpoint depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The port adds no axioms or unproved production theorems.
