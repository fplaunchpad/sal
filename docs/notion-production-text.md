# Extracted Notion text handlers: reviewed evidence

The question is what sequential specification explains the publicly shipped
one-block text routines for insertion, deletion and bold. The experiments
exercise extracted request builders and shared record handlers on fixture
records. They do not run Notion's server or full editor protocol.

## Bounded observations and specification choices

The recorded campaigns found no missing causal-history witness for the
selected anchored bold reading in 2,000 trials and 34,596 checked versions.
They found no convergence or conservation failure under the adapter's causal
delivery in 3,800 trials. These are finite observations, not proofs of the
implementation or the paper's RA criterion. Its implementation-dependent
order is not an input to the generic schedule checker.

Three named cases distinguish specifications rather than establish bugs:

| Case | Observation | Interpretation |
| --- | --- | --- |
| NT-1 | Typing after a bold character can inherit bold. | The initial positional contract omitted inheritance. Its `inherit` variant admits this result. |
| NT-2 | Three insertions produce a list excluded by the tested two-sided placement rule. | The gap and one-sided rules admit it; this refutes that stronger specification choice. |
| NT-3 | A concurrent insertion into an annotation's end gap becomes bold. | The anchored reading admits it; the fixed-character interval reading rejects it. |

The five Yjs formatting shapes re-expressed on these routines have admitted
results under the selected anchored reading. This does not establish that
every possible formatting trace is admitted. Only one-block ASCII text and
bold are exercised; links, other annotation keys, grapheme boundaries, undo
and cross-block formatting are outside these campaigns.

## Review corrections

The original target-directed optimisation constrained the order of character
identities while `viewKey` compared only characters and bold. Two equal
characters provided a false rejection. The reviewed specification now uses
observation-preserving search, with an independent regression pinning the
case. The same correction was needed in the Yjs, Automerge and Loro adapters.
Historical campaign outputs were preserved, not relabelled as fresh results;
negative search verdicts require rechecking with the corrected implementation.
A stored successful witness remains separate bounded evidence.

There is also a clock-interface distinction. The pinned fixture wrapper uses
the record-model getter with per-tree clock holders. The live editor's record
store uses persistent per-text-instance holders. Two preparations without
application can reuse an identifier through the fixture getter while the
editor holders allocate distinct ones. This is an adapter-boundary finding,
not evidence that production Notion reuses identifiers. The reviewed block
controls exercise the original editor getter explicitly.

See the [independent text review](notion-production-text-review.md) and
[protocol review](notion-production-protocol-review.md) for the precise source
and control evidence.

## Delivery probes outside the adapter contract

| Probe | Observation | Qualification |
| --- | --- | --- |
| P-1 | Delivering a deletion before its insertion leaves the later character visible. | Causal delivery avoids it; re-delivering the deletion clears it. Loss of the deletion persists only under the probe's once-per-accepted-batch policy. |
| P-2 | An annotation delivered before its anchor is rejected. | Re-delivery after the anchor succeeds. |
| P-3 | A later insertion can backfill its missing predecessors. | The documented control converges after the withheld operations arrive. |
| P-4 | A partial backfill followed by the original insertion run can leave a suffix absent. | This is an extracted out-of-order-handler result, not evidence that the production transport exposes that schedule. |

None of these probes establishes a live-service defect. The actual client
has optimistic local application, versioned record receipt and rollback/refetch
behaviour that the fixture does not execute.

## Reproduce

Follow the [extraction instructions](../experiments/notion-production-client/README.md)
and keep the downloaded assets and generated library outside the repository:

```sh
export NOTION_PRODUCTION_LIBRARY=/path/to/exported/library
export NOTION_PRODUCTION_CACHE=/path/to/pinned/assets
node ra-pbt/instances/notion-production-text/verify-sources.js
node experiments/notion-production-text/spec-tests.mjs
node experiments/notion-production-text/run.mjs --mode regressions
node experiments/notion-production-text/repro/run-all.mjs
```

The verifier checks six exported-file hashes. With the asset cache supplied,
it also verifies all 63 asset digests and all 4,335 module bodies against their
recorded JavaScript string ranges. Third-party code is acquired separately.
The [reproduction table](../experiments/notion-production-text/repro/README.md)
links each minimal case and its control. The historical campaigns remain in
`experiments/notion-production-text/results/`; no universal correctness result
follows from their counts.
