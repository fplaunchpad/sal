# Extracted Notion block handlers: reviewed findings

The question is whether the publicly shipped editing handlers work as a
standalone peer-to-peer replicated implementation under causal delivery.
This experiment does not run Notion's server, optimistic transaction queue,
record-value receipt, rollback or refetch protocol. It therefore does not
establish failures in the live Notion application.

## Findings

The six recorded classes have different evidential status:

| Class | Measured result | What the result establishes |
| --- | --- | --- |
| Label divergence | Concurrent splits assign different slice labels; a later insertion or bold request is rejected at one receiver. | Acceptance failure under the fixture's causal peer delivery. The receiver has not integrated the rejected record, so this alone is not same-record non-convergence. |
| Past boundary | A concurrent merge marker changes where a subsequent split item integrates; one receiver rejects the split. | Another handler-acceptance failure. Recovery and server acceptance remain untested. |
| Concurrent move | Both replicas integrate the same four records without pending records or causal gaps, but display different block divisions. | Same-record non-convergence under the extracted peer-handler contract. |
| Stale merge | A late merge of an already removed block moves its text again. | The minimal observed display has no witness even when all event-order dependencies are removed, under the supplied decoded-request specification. |
| Removed anchor | Listing a new block after a removed block appends it at the end. | Rejected by the tested causal-history specification; an explanation exists after removing all order dependencies. This alone does not refute the paper's criterion. |
| Order mismatch | Page order and text division resolve the operations differently. | Also a tested causal-history failure with a relaxed-order witness, not an established paper-RA counterexample. |

These are six mechanisms or specification disagreements, not six confirmed
live-service bugs or necessarily six independent root causes. No character
loss follows from a conservation-check failure without examining its fields:
that checker also requires all records to integrate and none to remain pending.
In particular, the reviewed N-002 and N-003 schedules retain every character;
the rejected bold record is what leaves the check incomplete.

The [independent block review](notion-production-blocks-review.md) records
freshly reproduced controls and exact outcomes. The
[protocol review](notion-production-protocol-review.md) identifies the actual
optimistic, versioned-receipt and rollback/refetch paths. A sequencing server
would reproduce a fixture failure only if it accepted and interpreted those
exact commands against corresponding states; that premise has not been shown.

## Source and harness

The [extraction manifest](../experiments/notion-production-client/sources.json)
pins 63 public assets. The parser extracts 4,335 original module bodies;
they are downloaded and exported outside the repository, never redistributed
here. [The block pins](../ra-pbt/instances/notion-production-blocks/library.json)
identify all six exported files and the eight modules used in the analysis.

Requests use the shipped split/merge builders and shared record interpreter.
The harness supplies fixture records, block creation/removal, causal peer
transport and its policy for a rejected record. It rolls back a thrown batch
and leaves it pending; it does not implement the live client's recovery.
The generic history search respects full dependencies and has no
implementation-policy `lo_E` input. Its verdict is causal-history conformance.

Clock allocation matters. The record-model getter creates fresh holders for
each parsed block, while editor module `970831` uses `997076.W` holders shared
by text instance. The block adapter uses the latter. Independent controls
invoke the original editor getter in isolated runtimes, without replacing
its static clock map, and reproduce the six minimal mechanisms. They also
reproduce the rejected formatting records after the N-002/N-003 full exchange
in both replica-ID orders. This checks the clock seam, not the full UI protocol.

## Reproduce

From the repository root, first follow the
[extraction instructions](../experiments/notion-production-client/README.md).
The library and cache must be outside this repository:

```sh
export NOTION_PRODUCTION_LIBRARY=/path/to/exported/library
export NOTION_PRODUCTION_CACHE=/path/to/pinned/assets
node ra-pbt/instances/notion-production-blocks/verify-sources.js
node --test ra-pbt/instances/notion-production-blocks/spec.test.js
node experiments/notion-production-blocks/regressions.mjs
node experiments/notion-production-blocks/review-controls.mjs
```

The [six minimal reproductions](../experiments/notion-production-blocks/repro/README.md)
state their expected and observed displays and nearby controls. The independent
review controls also compare relaxed event orders. Original campaign summaries
in `experiments/notion-production-blocks/results/` are historical measurements,
not a fresh run of the reviewed tester or proofs of the stated properties.

## Relation to the five demo reports

The original production-client comparison checked the local request effects;
those checks passed. Extending its exact selection contract through the final
exchange exposes a rejected N-002 bold record, while its N-003 variant succeeds.
The editor-clock fixture separately reproduces rejection in both re-expressed
schedules. Thus the fixture and clock path are load-bearing; final exchange
alone does not explain both new observations. In all of these cases the local
selection is correct, unlike the public demo's immediate selection failures.
The reviewed N-001/N-004/N-005 schedules do not reproduce their demo failures.
Neither result settles behaviour in the live application.
