# ra-pbt

Property-based testing of replicated data types against a sequential
specification. Plain ES modules for Node, no dependencies.

## Two layers

**End-to-end layer** (`src/schedule.js`, `src/checks.js`, `src/witness.js`,
`src/generate.js`, `src/shrink.js`, `src/campaign.js`, `src/regressions.js`).
A real implementation runs behind an adapter. Seeded schedules of edits,
deliveries, single-record sends and opened replicas are executed; after every
step the acting replica's view is checked for RA-linearizability: some linear
extension of the causal order on the records it has integrated, folded
through the specification, yields that view. The search is exact over
down-closed sets of at most 20 events. Convergence, local meaning,
determinism of opened versus created replicas and conservation are checked
alongside. Failing schedules are shrunk greedily and can be kept as
regressions.

**Law layer** (`src/laws.js`). The five verification conditions of the paper
(VC1 to VC5) and its conditions on the conflict relation `rc`, checked as
properties over randomly generated configurations of a state-based datatype
with a three-way merge, with shrunk counterexamples. Instances for the Sal
runtime live in `instances/sal-runtime/`.

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
| `rc?(op1, op2)` | operations that do not commute in the specification |
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
RA-linearizability.

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
