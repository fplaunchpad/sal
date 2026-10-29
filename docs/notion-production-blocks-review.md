# Review of the extracted production block findings

Independent review on 2026-10-29 of the production-block experiment at
source revision `5b12b7a` and its main-tree integration. The six declared
minimal phenomena reproduce, with their controls. The label-addressing
rejection survives an independent use of the shipped editor clock path;
the N-002/N-003 full-exchange finding is supported. These are findings about
extracted handlers under specified fixture and delivery contracts, not
observations of live Notion or automatically six distinct product bugs.

## Evidence and clock fidelity

The production-block manifest verified **six export files and eight named
module digests**, covering an export of **4,335 modules from 63 pinned
assets**. Older exports with different wrappers/manifests were correctly
rejected; they were not substituted for the pinned export. No downloaded
module body was copied into this review or its controls.

Fresh checks:

| Check | Result |
| --- | --- |
| Production-block specification tests | 15/15 |
| Source production-block regression cases, imported without writing results | 35/35 |
| Six standalone minimal reproductions, each with a nearby control | 6/6; exit 0 means the phenomenon and control matched |
| Main production-client extraction/replay suite against the pinned cache | 19/19 |
| Independent main-tree review controls | 16/16 |

No random campaign was rerun. Campaign counts in the source note remain
historical measurements, not independently refreshed totals.

The clock distinction is real and load-bearing. The original main
`ProductionClient.tree` reads through the record model. The shipped editor
store, module 970831, instead calls parser 266858 with per-instance holders
`997076.W`. The source adapter reproduces that parser choice and swaps a
per-client override map into shared runtimes. Merely accepting that custom
adapter would leave a fidelity question.

[review-controls.mjs](../experiments/notion-production-blocks/review-controls.mjs)
therefore uses a separate VM per client and invokes the **verbatim
BlockStore getter**, with only the fixture session injected through module
727114 and fixture accessors exposing record values. It does not assign
`W.overrides` or substitute a parser. Native per-runtime holder maps remain
in use. Its sequential control gives `a | b | c` with the editor getter,
versus `ac | b | empty` with record-model clocks. Label rejection,
past-boundary rejection and concurrent move reproduce with this independent
clock path under both A/B session orders. N-002/N-003 do too.

This validates the clock choice on the decisive traces, not the complete
live editor cache, optimistic update path or session lifecycle.

## Label addressing and the five demo schedules

For label-divergence, A splits `abc` after `a`, B splits it after `ab`,
and A inserts X into its split-off block. After exchange, A displays
`a | Xb | c`; B displays `a | b | c` and rejects the insertion with
`Cannot backfill prev item that is not a text item`. The record's complete
declared causal past is present at B. Removing concurrent splitting makes
both display `a | Xb | c`. The source's third-receiver sequencing regression
also reproduces this rejection and passes its serialization control.

The mechanism has direct source support: module 458789 subdivides labels
using 663360 after splits; module 121141 selects slices within the
operation's label range. Applying the concurrent splits in opposite orders
produces different labels for the same identity-addressed slices.

N-002 and N-003 have the contracted **local** bold effect on the production
path. Their old demo formatting failures are not reproduced. On full
exchange, however, the receiving extracted handler rejects the bold with
`Unable to apply annotation operation due to start missing`:

| Schedule | Issuer after exchange | Receiver after exchange |
| --- | --- | --- |
| N-002 | `empty | [a][b]` | `empty | ab` |
| N-003 | `[a][b] | c` | `ab | c` |

Both session orders reproduce these outcomes using the native editor
getter. Retrying the same operation on a fresh copy of the final receiver
state rejects it again. Expected and actual **character identities are
equal**; only the bold record remains unintegrated. The generic conservation
check fails because it additionally requires no pending records and complete
integration, not because characters were lost or duplicated.

The earlier main replays end N-002/N-003 after checking the issuer's local
bold effect. They do not perform this final exchange. Their record-model
clock/fixture path also has different post-merge layouts: N-002 is `a | b`,
N-003 is `a | bc`, and each original replay selects its actual target's
entire **one-character** range. Extending that exact contract to full
exchange exposes a bold rejection for N-002, but **N-003 succeeds**, yielding
`[a] | bc` at both receivers. The two-character native-editor-clock fixture
still rejects N-003. Both delivery coverage and the clock/fixture path are
therefore load-bearing; they cannot be treated as interchangeable replays.

An earlier version of the added comparison controls incorrectly requested
two characters in these one-character targets. Root's independent rerun
exposed the local range errors. Those assertions and the claim that both
original-wrapper extensions reject were retracted; the corrected controls
preserve the original dynamic selection and assert N-002 rejection versus
N-003 success explicitly.
The source regressions also retain the local-effect/seed-text results for
N-001, N-004 and N-005.

## Six candidate classes and what each establishes

| Candidate | Fresh minimal observation | Interpretation boundary |
| --- | --- | --- |
| Label-divergence | Causally ready insertion/annotation rejected; serialization control succeeds | Handler applicability/progress failure; receiver has not integrated the same records as issuer |
| Past-boundary | Second split rejected after a concurrent merge; one-split control succeeds | Handler rejection, likewise not equal-integrated-record convergence evidence |
| Concurrent-move | Both receivers integrate all four records, have no pending records or causal gaps, but display `ab | empty | c` and `a | b | c`; serialized control agrees | Genuine same-record nonconvergence under the extracted peer-to-peer replay contract, in both session orders |
| Stale-merge | All three records integrate; both show `a | bc | empty`; one-merge control keeps the split | Rejected by the declared sequential specification even after removing every event-order edge |
| Removed-anchor | All four records integrate; one display is `ab | empty | cd | empty` | Rejected under the tested causal order; admitted when all event-order edges are removed |
| Order-mismatch | All three records integrate; one display is `empty | empty | Ya` | Rejected under the tested causal order; admitted when all event-order edges are removed |

For stale-merge the completely relaxed exact search admits only
`a | b | c`, and the admitted set is nonempty and untruncated. This is an
order-independent sequential-specification counterexample for those decoded
atomic command groups. Connecting it to a formal paper-RA statement still
requires establishing the operation/query/specification correspondence.
It specifically depends on the contract that merging an already tombstoned
source is a no-op; the extracted handler deliberately continues through a
`merge_from_deleted_block` path. The measurement establishes disagreement
with that contract, not which stale-merge policy the product intends.

Removed-anchor has a relaxed witness in event order
`r1#1, r1#0, r2#0, r2#1`; order-mismatch has one in order
`r1#1, r2#0, r1#0`. These relaxed witnesses do not show that the paper admits
the executions: a separate commutation and implementation-order analysis is
needed. They do show why absence of a full-causal-history witness alone
cannot support the note's unconditional RA claims. Swapping session order
also removes the stale-merge and order-mismatch witness failures in the
tested variants, which is useful identity-order sensitivity evidence.

## Corrections required before publishing claims

- Call the six names **candidate mechanisms/classes under the extracted
  harness**, rather than six established live-product defects or six
  independent root causes. The classifiers name already detected failures;
  they do not establish their specification or protocol meaning.
- Replace B2's generic RA verdict with causal-history conformance. The
  current main checker explicitly records `paperRaVerdict: 'not-checked'`.
  Preserve the stronger all-order result for stale-merge separately.
- Distinguish rejection from convergence of identical integrated histories.
  The adapter rolls back on an exception, blacklists the record and leaves
  it pending. That is a harness recovery policy. Raw handler rejection and
  retry failure are supported; permanent live-client divergence is not.
- State B4 as a composite integration/pending/character check when quoting
  its result. N-002/N-003 do not falsify character conservation alone.
- Remove the inference that every class would occur at a live sequencing
  server. The third extracted receiver demonstrates label rejection under
  one causal receive order. It does not establish the server's transaction
  acceptance, transformation, retry or snapshot semantics. Concurrent-move,
  like list-order, compares different replay orders; one authoritative order
  can choose a sequentially admitted outcome.
- Retain fixture boundaries prominently: block creation/removal and record
  transport are ours; own optimistic operations in module 946729 and the
  live client's receipt of server record values are not exercised. The
  removed-anchor and order-mismatch expectations additionally depend on the
  declared block-list/tombstone specification.
- Bound B3/B5 passes to the tested requests and forks. No full search or
  absence of unexplained failures was established by this review.

## Reproduce the review

From the repository root, with the pinned export and asset cache supplied:

```sh
node ra-pbt/instances/notion-production-blocks/verify-sources.js
node --test ra-pbt/instances/notion-production-blocks/spec.test.js
node --test experiments/notion-production-blocks/review-controls.mjs
npm test --prefix experiments/notion-production-client
```

The first and third commands use `NOTION_PRODUCTION_LIBRARY`; the last uses
`NOTION_PRODUCTION_CACHE`. The original 35 source regressions were invoked
through exported `cases(lib)` with verification before/after, rather than
their result-writing CLI. The six plain reproductions use the same library
environment variable. No source-tree, remote, paper or artifact changes
were made by this review; additions are this note and the independent
control script.
