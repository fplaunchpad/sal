# Peritext benchmark workload contract

This contract separates comparable rich-text operations from Peritext-specific
semantics. Do not rank systems on a workload unless they implement the stated
observable.

## Observable

A render is an ordered list of characters. Each character carries a
name-sorted list of `(mark type, value)` pairs. Correctness gates compare the
complete render, not only the plain text.

The cross-system core uses marks whose endpoints remain live and uses fixed
inclusive intervals. It measures insertion, deletion, overlapping bold and
italic marks, link values, and explicit mark removal. Yjs, Automerge, or Loro
adapters may enter this comparison only after a directed fixture establishes
the same interval and removal behavior.

The Sal-specific extension measures Peritext behavior that common editor APIs
do not necessarily share:

- boundary gravity over later insertions;
- forward/backward dead-anchor rehoming;
- delete-induced re-spanning;
- overlapping comments encoded as distinct mark types;
- retention-root text GC and guarded mark-pair GC.

Label external cells `incomparable` when these observables differ. Do not
coerce native editor behavior into Peritext behavior inside an adapter.

## Deterministic workloads

1. `format-trace`: replay each real text trace and inject deterministic mark
   additions/removals at transaction boundaries.
2. `concurrent-rich`: two replicas concurrently insert/delete text and
   add/remove overlapping marks, then synchronize at fixed intervals.
3. `mark-churn`: repeatedly add and remove marks over a mostly stable document.
4. `marked-delete-churn`: delete text under live and removed marks to exercise
   retention roots and guarded pair dropping.
5. `offline-rich`: delay one replica while the other edits text and marks, then
   measure catch-up, acknowledgement, and history pruning.
6. `empty-rich`: delete all characters and remove all marks; after settlement
   and acknowledgement, require the fresh-empty datatype representation and one
   epoch-base commit.
7. `multi-epoch-rich`: repeat edit, settle, state GC, acknowledgement, and
   history pruning across several epochs.

Use fixed seeds and record every workload parameter in the raw result.

## Sal ablations

- `none`: no collector;
- `history`: commit-history GC only;
- `text-state`: retention-root text compaction with guarded pair drop disabled;
- `full-state`: text compaction plus guarded mark-pair GC;
- `both`: full state GC followed by acknowledged epoch-base pruning;
- `both-delayed`: the same protocol with pruning attempted before and after the
  delayed receipt.

State GC must run before history pruning because its certificate consumes causal
ancestry. Keep the premature-history-GC ordering only as a negative control.

## Metrics and gates

Record text/mark apply latency, sync latency and bytes, GC pauses, durable and
resident bytes, commit count, shadow records, deleted IDs, mark records,
coordinate symbols, save/load time, and late-bootstrap cost.

Every result must pass:

- intra-system replica convergence on the complete render;
- render equality before and after each state GC;
- render equality across all Sal GC ablations for the same trace and seed;
- snapshot round-trip equality;
- refusal before required evidence and successful pruning afterward;
- directed PASS/FAIL fixtures for gravity, rehoming, and mark removal.

The existing Python Peritext read model supplies independent expected values for
directed fixtures. Randomized ablation equality is differential validation, not
a proof of the read semantics.
