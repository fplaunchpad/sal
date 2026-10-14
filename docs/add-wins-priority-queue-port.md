# The flattened add-wins priority queue

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
