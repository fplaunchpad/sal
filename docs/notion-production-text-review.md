# Review of the extracted production Notion TEXT experiments

Reviewed on 2026-10-29. The question is which bounded results and concrete
counterexamples survive execution of the pinned production routines, rather
than a reconstruction of their behavior. The source report is
`docs/notion-production-text.md` and the corresponding experiment and instance
directories in the `sal-yjs` source tree, reviewed at commit
`5b12b7ac21ced869c6ae731fa39063c5f2dac9bf`. The imported main-tree specification
has the correction described below. Historical campaign JSON was not rewritten.

The short reproductions survive. The headline claim of production
RA-linearizability does not follow: the checker tests causal-history
conformance, the extracted client uses a fixture clock path, and the original
witness optimisation could reject observations that the specification admits.

## Evidence and trust boundary

The authority for an implementation observation is the pinned downloaded
asset plus its extracted module body. The export's handwritten wrapper,
record fixtures, bundler shim, transport, specification and search are
additional executable assumptions. Neither an intact hash nor an executable
regression proves correspondence to every live editor path.

Level-2 source verification passed using an available external export and
asset cache: all six export digests, all 63 asset lengths and digests, and
all 4,335 extracted module slices matched. The asset total was 9,006,862
bytes. The complete pins are in
[`sources.json`](../ra-pbt/instances/notion-production-text/sources.json).
For example, the checked `client.mjs` digest was
`564729b916d7344ef4024d20311e38f6e9620d65705c36c70b26cd3d72660892`.
The export remains outside the repository and unchanged. The extraction
suite passed all 19 tests against that cache, including the modified-source
negative control and original-module execution controls.

The checked production functions include builders, text integration,
annotation sets, rich-text reading and the record handler. Application
bootstrap, optimistic editor stores, server acceptance and actual transport
were not executed. “Extracted production editing routines under fixture
records” is supported; “the complete shipped client” is broader than the evidence.

## Claim ledger

| Candidate claim | Evidence status | Surviving claim and falsifier |
|---|---|---|
| T1: plain text satisfies the gap/left list rules | Measured historical passes; small cases validated after correction | These generated fixture histories had witnesses. A completed corrected search finding no witness would refute the selected causal-history specification on that history. No universal list theorem follows. |
| T2: bold is RA-linearizable under the anchored reading | Overclaim; bounded causal-history evidence survives | The supplied small histories have witnesses under a dynamic anchor-coverage reading. Paper RA additionally needs an implementation policy and a correspondence argument. |
| T3: positional local meaning | Refuted for insertion by NT-1 | Typing after a bold character inherits bold. The added inheritance rule explains the checked local cases; it is not a proof for all requests. |
| T4: created/opened determinism | Measured, fixture-scoped | Forks from the same source state/history agreed. This does not establish equivalence of arbitrary states with the same display, or of the live editor clock/store path. |
| T5: convergence and conservation | Measured, transport-scoped | No reported failure under the adapter's causal, once-per-record delivery. P-1/P-4 expose different results when that adapter buffering is removed. |
| NT-2: two-sided refinement | Validated counterexample | Distinct-character `c; f-before-c` concurrent with `x` yields `fxc`, outside the two-sided rule's `{xfc,fcx}`; gap and left admit it. |
| NT-3: interval formatting reading | Validated counterexample | Concurrent bold of `a` and insertion of plain `h` after it yields `a*h*` in both session orders. The interval reading excludes it; anchored coverage admits it. |
| P-1: an early deletion is lost | Validated conditional behavior | Applying an absent-character deletion once, then its insertion, leaves the character visible. Redelivering the identical deletion repairs it. |
| P-4: partial backfill suppresses the rest of an insertion run | Validated conditional counterexample | The pinned handler produces `hxj` versus `hxjw`; the unsplit control produces `hxw` on both. Deployment reachability is unestablished. |

Here “validated” means the concrete script and its control were rerun, not
that a universal property was machine-checked. NT-2 and NT-3 refute chosen
specification readings; they do not by themselves establish an editor defect.

## Witness order and observation correction

The end-to-end search orders every supplied causal dependency among
integrated records. It does not compute the paper's implementation-policy
`lo_E`, does not insert directed concurrent `rc` edges, and does not check
the datatype's globally quantified laws. Extra causal edges can exclude a
paper-permitted witness; absent implementation-policy edges can admit an
order the paper forbids. A causal-history rejection is therefore not an
unconditional paper-RA counterexample. Partly integrated records and
out-of-bound histories are skipped; missing external dependencies are
dropped and counted. The stored TEXT summaries report zero such skips and
gaps for the buffered campaigns.

The new TEXT specification was computationally independent of the exported
library: its only import was the positional request specification. Its
anchored reading was nevertheless chosen using a source reading and a
pilot. Comparing that reading's passes with another library's failures
under interval formatting does not establish superiority under a common
specification. A shared independently stated observation and formatting
contract is needed for that comparison.

A concrete search-contract error was reproduced. `viewKey` observes only
characters and bold, but `applyDirected` restricted insertions to the
target's identity order. Two causally ordered head insertions of `x` have
the single sequential placement `B,A`. A target carrying identities `A,B`
still observes `xx`. The old directed search returned `found:false`; the
same specification without that pruning returned `found:true`. Thus the
optimisation could turn an admitted observation into a reported failure.

The main-tree TEXT specification now uses full `applyAll` search. The query
was not strengthened to expose identities. Its new PASS+FAIL regression
accepts `xx`, rejects a target with an unexplained bold character, and
demonstrates that the former pruning mutant loses the valid witness.
All 15 specification blocks and all 24 production TEXT regressions pass.

The same mismatch was independently reproduced in the Yjs gap, Loro gap,
and Automerge character/layout-directed specifications. Their main-tree
packaged specifications now also use the full visual-observation search,
with per-adapter repeated-character positive and attribute-negative tests.
Automerge retains an unpruned compatibility hook; its confirmation helper
now budgets full `applyAll` applications and retains `undecided` on
exhaustion. A zero-budget / sufficient-budget / completed-rejection
regression checks all three outcomes.

All historical random **negative witness counts and classification counts**
affected by the old pruning are pre-review observations, pending corrected
reruns. The stored TEXT totals are internally consistent: 19 runs, 3,800
trials, 37,311 edits, 65,584 checked versions, zero reported anomalies, and
910 opened replicas. These arithmetic checks do not revalidate every old
negative verdict. Previously found witnesses remain positive evidence for
the weaker visual query, subject to the specification/search contracts.
The distinct-character NT-2/NT-3 cases, the direct shipped-code scripts, and
the corrected regression suites provide separate evidence from those counts.

## Clock-holder choice is a load-bearing fixture boundary

The pinned wrapper calls `RecordMap.getModel(...).getBlockTitleTextSliceTree`
(model module `500183`). That path constructs a numeric clock value holder
`508649.g`. The live `BlockStore` path (`970831`) instead deserializes with
`997076.W`, whose per-text-instance override persists reservations across
separately reconstructed trees. Both paths use original extracted code;
they are observably different.

The following independent seam test was executed with the unchanged export:
two `prepareInsert` calls without an intervening apply returned `s1:1` and
`s1:1` through the wrapper, but `s1:1` and `s1:2` through the original
deserializer with the live-store holder and the same insertion builder.
This is not evidence that the live client issues duplicate identities.
It establishes that this fixture is not a test of the live clock-reservation path.

```js
// Run as an ES module with NOTION_PRODUCTION_LIBRARY pointing to the pinned export.
import assert from 'node:assert/strict';
import { pathToFileURL } from 'node:url';
import { join } from 'node:path';
const { createClient } = await import(pathToFileURL(join(process.env.NOTION_PRODUCTION_LIBRARY, 'index.mjs')));
const block = { table: 'block', id: '00000000-0000-4000-8000-0000000000b1',
  spaceId: '00000000-0000-4000-8000-000000000100' };
const c = createClient('s1'); c.createBlock(block);
assert.equal(c.prepareInsert(block, 0, 'a')[0].args.id.join(':'), 's1:1');
assert.equal(c.prepareInsert(block, 0, 'b')[0].args.id.join(':'), 's1:1');
const decode = c.module('266858').r, Holder = c.module('997076').W;
const prepare = c.module('769718').H, serialized = c.value(block).crdt_data.title;
const tree = () => decode(serialized,
  ({ value, textInstanceId }) => new Holder(value, textInstanceId), 's1');
assert.equal(prepare(tree(), { index: 0, content: 'a' }).id.join(':'), 's1:1');
assert.equal(prepare(tree(), { index: 0, content: 'b' }).id.join(':'), 's1:2');
```

The TEXT adapter prepares and immediately applies each request. That is
consistent with the wrapper's documented calling convention and explains
why this difference need not invalidate its small replays. Reservation
without immediate application, stale snapshots, aborted transactions and
the live store's persistent clock state remain outside the tested claims.

## Out-of-order probe limits

P-1 and P-4 reproduce on the extracted handler without the sequential
specification or witness checker. Both also have passing causal-delivery
controls. They are evidence about these operation batches and this delivery
policy, not evidence that the deployed transport permits those schedules.
The quote “deliver each batch once, after its causal predecessors” is the
extraction wrapper's calling convention; this review did not establish a
vendor-documented transport guarantee.

P-1's standalone comment says redelivery is refused. A direct additional
probe disproved that sentence: deletion-before-insertion leaves `a`, then
redelivering the same deletion batch yields the empty text. “Permanent” must
be qualified by the probe policy, which records an accepted batch and never
redelivers it. P-4's observed partial-run suppression remains distinct.

The reported mechanism totals also need narrower wording. The global
`out-of-order.mjs` counters are incremented during primary trials,
classification re-executions, and shrinking/replays. `runSearch` does not
isolate those phases before snapshotting `summary.mechanisms`. In particular,
487 refusals and 298 backfills are not established as counts over only the
400 generated trials. Trial counts and per-trial failure summaries use
separate accounting. Fresh phase-isolated mechanism counts are needed before
quoting those columns as campaign rates.

## Commands and checked results

Set `NOTION_PRODUCTION_LIBRARY` and `NOTION_PRODUCTION_CACHE` to external
directories matching the pins; no download, installation or historical
campaign rewrite was needed for this review. Commands are from the repository root.

| Command | Checked result |
|---|---|
| `node ra-pbt/instances/notion-production-text/verify-sources.js` | Level 2 accepted: six export hashes, 63 assets, 4,335 module slices |
| `npm test --prefix experiments/notion-production-client` | 19/19 extraction and replay controls passed |
| `node experiments/notion-production-text/spec-tests.mjs` | Corrected specification: 15/15 blocks passed |
| `node experiments/notion-production-text/run.mjs --mode regressions` | Corrected search: 24/24 regressions passed; level-2 check before and after |
| `node experiments/notion-production-text/repro/run-all.mjs` | All seven standalone NT/P scripts matched their documented outcomes |
| `node experiments/yjs-oracle/spec-tests.mjs` and `node experiments/yjs-oracle/run.mjs --mode regressions` | 27 specification tests and 28 regressions passed; pinned Yjs 13.6.31 verified |
| `node experiments/automerge-oracle/spec-tests.mjs` and `node experiments/automerge-oracle/run.mjs --mode regressions` | 14 specification tests and 18 regressions passed; pinned Automerge 3.5.0 verified |
| `node experiments/loro-oracle/spec-tests.mjs` and `node experiments/loro-oracle/run.mjs --mode regressions` | 18 specification tests and 54 regressions passed; pinned Loro 1.17.1 verified |

A corrected small TEXT search was also run, without an output file:

```sh
node experiments/notion-production-text/run.mjs --mode search \
  --seed 31 --trials 10 --steps 8 --bold --local inherit --rule left --no-shrink
```

It checked 124 versions over 69 edits, with zero failures, witness skips,
causal gaps or anomalies. This is a fresh bounded check, not a rerun of the
3,800-trial campaign.

Full search can grow rapidly: the 20-event cap bounds event subsets, not
the number of relational states or character placements per subset.
`findWitness` itself has no general relational-state budget; Automerge's
confirmation helper has its separate application budget. `allFinalViews`
caps relational enumeration by default and marks truncated output. The old
12-event Yjs relational performance test relied on the removed optimisation;
its replacement uses four events. The independent 20-event deterministic
test remains. The small corrected suites were tractable; this review does
not establish the cost of corrected 12–16-request random campaigns.

## Research question opened by the evidence

The checked source suggests a compositional question: under what explicit
list, issuance and clock assumptions does dynamic coverage by stable
character-side anchors admit a common causal-history witness with the list?
The proposed identity order, deletion placement and annotation resolution
are candidate proof ingredients, not a theorem checked on 34,596 versions.
Falsifiers should include repeated characters, tombstone anchors, a shared
clock across preparation/rollback, overlapping add/remove annotations and
multi-character batches. A common specification across the four libraries,
followed by a formal composition argument, would answer a stronger question
than reporting clean campaigns under individually selected readings.

One-block, one-slice, ASCII, bold-only fixture histories remain the scope.
Non-expanding keys, after-side anchors, multi-instance text, undo, the
monotonic-insertion option, live editor state and transport reachability
remain unestablished. Publication should retain those boundaries and the
pre-review status of affected historical negative counts.
