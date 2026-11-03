# ra-pbt

Property-based testing of replicated data types against a sequential
specification. Plain ES modules for Node, no dependencies.

## Two layers

**End-to-end layer** (`src/schedule.js`, `src/checks.js`, `src/witness.js`,
`src/generate.js`, `src/shrink.js`, `src/campaign.js`, `src/regressions.js`).
A real implementation runs behind an adapter. Seeded schedules of edits,
deliveries, single-record sends and opened replicas are executed; after every
step the acting replica's view is checked for causal-history conformance:
some linear extension of all causal dependencies among its integrated records, folded
through the specification, yields that view. The search is exact over
down-closed sets of at most 20 events. Convergence, local meaning,
determinism of opened versus created replicas and conservation are checked
alongside. Failing schedules are shrunk greedily and can be kept as
regressions.

The legacy API key `raLinearizability` names this end-to-end check. Its
result and failures carry criterion metadata with
`paperRaVerdict: 'not-checked'`. It is not a general checker for the paper's `lo_E`: it keeps
all causal edges, including commuting ones, and adds no directed implementation
`rc` edges between concurrent events. The two orders can be incomparable.
A found witness is a sufficient paper witness only when it also respects
the required implementation order and the event/specification interfaces
correspond. A missing causal-history witness alone does not refute paper RA.

For example, concurrent branches `add x; remove y` and `add y; remove x`
of the correct add-wins OR-set merge to `{x,y}`. The paper order admits
both removes followed by both adds. The full-causal-history search rejects
that result: preserving both branches' order forces at least one removal
after the corresponding addition. Conversely, the search may accept a
concurrent order forbidden by an implementation's directed `rc` policy.

Partly integrated records skip the witness check (`witnessSkipsPartial`).
When a fully integrated record lacks a dependency in the receiver's
integrated set, that edge is dropped and counted in `causalGaps`; the
remaining slice is checked, even though it is not a causally closed version
of the paper model. Bound skips are counted in `witnessSkips`. These skips
and gaps must accompany any reported coverage or verdict.

The packaged Yjs, Automerge, Loro and production-Notion visual specifications
use full observation-preserving search. An earlier optimisation constrained
target identity order even though their queries ignore identities; repeated
characters exposed a false rejection. Historical negative campaign counts
must be rechecked with the corrected search. Full relational enumeration can
be expensive; report skips, truncation and undecided confirmation separately.

**Law layer** (`src/laws.js`). The five verification conditions of the paper
(VC1 to VC5) and its conditions on the conflict relation `rc`, checked as
properties over randomly generated configurations of a state-based datatype
with a three-way merge, with shrunk counterexamples. Instances for the Sal
runtime live in `instances/sal-runtime/`.

Law results include `status` (`pass`, `fail`, `inconclusive`, `vacuous`, or
`not-applicable`) and `pass`, which is true only for `status: 'pass'`.
`runs` counts checked pass/fail candidates; `inconclusive` counts unresolved
candidates separately, with the first example in `inconclusiveExamples`.
A result containing any unresolved candidate has status `inconclusive`
unless a concrete failure was found. Consumers must use `status` or `pass`,
not an empty `failures` array, to report checked passes. Passing sampled
checks does not prove a universal law.

The commutation laws search a finite state pool. Not finding a witness of
non-commutation is inconclusive, even when the pool exhausts all distinct-event
sequences of a small configuration. An optional trusted
`datatype.semanticCommutes(a, b)` oracle may return `true` or `false` to
certify semantic commutation or non-commutation on the datatype's whole state
domain, or `undefined` to leave the pair unresolved. This is separate from
`instance.commutes`, which declares the policy used to construct the order
and supplies no semantic certificate. The specification witness search is
also inconclusive when it exhausts `maxSpecPrefixes` (default 50000) without
finding a witness; a completed search may establish that no witness exists.
`maxSize` bounds generation steps, including synchronization steps.

## Specifications (`src/spec.js`)

A specification is a plain object:

| Member | Meaning |
| --- | --- |
| `init()` | the initial state |
| `apply(state, op)` | the next state, or null when a precondition fails |
| `applyAll?(state, op)` | every next state of a relational specification; without it the specification is deterministic |
| `applyDirected?(state, op, target)` | the next states consistent with a target view; must keep some witness whenever `applyAll` has one |
| `directs?(target)` | whether `applyDirected` narrows the search for this target |
| `view(state)` | the observable value |
| `serialise(state)` | canonical string of a state |
| `viewKey(view)` | canonical string of a view; views are equal exactly when their keys are |
| `normalise?(view)` | the view as shown in reports |
| `localEdit?(view, request)` | the meaning of a request on the issuer's own view (the localMeaning check) |
| `rc?(op1, op2)` | optional specification-conflict annotation; unused by witness search, neither filtering dependencies nor providing directed implementation rc |
| `equivalent?(a, b)` | equivalence of states; defaults to equal serialisations |

`normaliseSpec(spec)` fills the defaults. States are immutable values.

## Adapters (`src/adapter.js`)

An adapter is a plain object over the implementation's replicas, validated
and completed by `checkAdapter(adapter)`:

| Member | Meaning |
| --- | --- |
| `createReplica(id, { opened })` | a fresh replica; an opened one receives a state through `loadInto` first |
| `loadInto?(replica, source)` | gives an opened replica `source`'s whole state (enables `open` steps and the determinism check) |
| `issue(replica, request)` | issues a request; returns a record `{ replica, kind, request, update, deps?, specOps }`, where `specOps` are the specification operations the request denotes, with the identities the implementation assigned; throws a RangeError for a rejected request |
| `deliver(replica, record)` | applies one record; returns `{ pending, emitted }` where `emitted` are cleanup records (`kind: 'cleanup'`, no specOps) the replica issued on its own |
| `sync(to, from)` | brings `to` up to date with `from`; returns `{ emitted }` |
| `view(replica)` | the value in the specification's view format, with identities when the directed search needs them |
| `displayed?(replica)` | the value as displayed (convergence, local meaning, determinism); defaults to `view` |
| `stateVector(replica)` | a JSON summary of what the replica holds |
| `integrated?(replica, records)` | which received records are fully integrated: a Set of keys or `{ integrated, partial }`; the default reads `record.dot = [origin, counter]` against the state vector |
| `hasPending(replica)` | received state not yet integrated |
| `validRequest(replica, request)` | false, or a thrown RangeError, for an out-of-range request |
| `inserted?`, `deleted?`, `present?` | element accounting for the conservation check |
| `fingerprint?`, `snapshot?`, `traceRecord?`, `crossCheck?`, `requestOf?` | extra comparison, report and consistency hooks |

Checks whose hooks are absent are skipped and counted in `stats.skipped`.

## Writing an instance

An instance is `{ spec, adapter, nextRequest, reduceRequest?, generateOptions? }`:

- `nextRequest(rnd, view, options)` returns a request for a replica displaying
  `view`, or null; `rnd` offers `next()`, `int(lo, hi)` and `pick(xs)`.
- `reduceRequest(request)` returns smaller requests for the shrinker, each a
  request or `{ request, reduction, to }`.
- `generateOptions(options)` applies instance defaults to generation options.

Then:

```js
import { execute, generate, runCampaign, findWitness } from 'ra-pbt';

const schedule = generate(instance, 42, { replicas: 3, steps: 12, partialDelivery: true });
const trace = execute(instance, schedule);            // trace.checks.raLinearizability.pass
const { summary, failing, shrunk } = runCampaign(instance, { seed: 1, trials: 200 });
```

Schedule steps are `{ type: 'edit', replica, ...request }`, `{ type: 'deliver',
from, to }`, `{ type: 'send', from, to, op }` and `{ type: 'open', replica,
from }`; records are keyed `r<replica>#<n>`. `test/gset.js` is a small complete
instance: a grow-only set with an in-process adapter, and a
wrong variant whose merge forgets an element, which the tests show failing
causal-history conformance.

## Instances

- `instances/yjs/`: Y.Text from the pinned `yjs@13.6.31` against the strong
  list specification with formatting marks (`spec.js`; `oracle.js` binds the
  witness search to it and is independent of Yjs), the replica adapter
  (`adapter.js`), request generation and reduction (`requests.js`) and a
  mechanism classifier for failures (`classify.js`). `verify-sources.js`
  checks the installed release against `sources.json`. Install with
  `npm install --ignore-scripts` in that directory.
- `instances/sal-runtime/`: law-layer instances for the Sal runtime datatypes,
  and end-to-end instances (`endtoend.js`) running the runtime's OR-set and
  RGA as replicas.

## Commands

```
npm test                                        # node --test test/*.test.js
node instances/yjs/verify-sources.js            # pinned Yjs release
node instances/yjs/classify.js <search.json> [out.json]
```

The Yjs experiments that drive the instance (search, replay, regressions,
measured facts) are in `experiments/yjs-oracle/`.
