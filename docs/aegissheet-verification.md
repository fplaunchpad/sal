# AegisSheet verification enquiry

## Goal

Verify a compositional spreadsheet MRDT against the merge and undo outcomes in
Tables 3 and 4 of *AegisSheet: A Compositional CRDT for Collaborative
Spreadsheets*. Cover stable row and column identities, persistent cell
conflicts, nonduplicating moves, anchored ranges, and tombstone collection.

## Candidate claim

A grow-only set of causally annotated spreadsheet actions, queried by the
AegisSheet conflict policies, converges under union merge. A guarded sequential
trace refines an executable list-based spreadsheet reference. Every published
matrix outcome is a checked fixture. Tombstone collection requires either a
semantic cutoff marker or a protocol that rules out later revival.

## Falsifier

Any of the following results refutes the claim:

- a published matrix fixture evaluates to a different result;
- two merge orders produce different observations;
- a guarded linear trace disagrees with the reference interpreter;
- local tombstone collection followed by a permitted late merge changes a
  result without the claimed stable-cut premise.

## Formal oracle

`Sal/MRDTs/Instances/AegisSheet.lean` contains the executable model,
certificates, and matrix SPOTs. `AegisSheetGC.lean` contains the collection
counterexample, corrected semantic-marker collector, and state-GC
certificate. Lean kernel checking is the formal oracle.

## Reality oracle

Tables 3 and 4 and Figure 1 of the PaPoC 2026 AegisSheet paper define the
external fixtures. The Scala implementation in the Bismuth `ex2025tabular`
module is a separate implementation oracle. The audit in
`docs/aegissheet-scala-audit.md` refutes equivalence at Bismuth commit
`dd4c614`: move undo violates two Table 4 cells, range undo loses stable
endpoints, and a crossed range can make `listRanges()` throw.

## Evidence vocabulary

- Theorems and SPOTs accepted by Lean are **machine-checked**.
- Matrix fixtures copied from the paper and checked against the model are
  **validated on the named scenarios**.
- Scala equivalence is **refuted** at commit `dd4c614` by four executable
  regression tests.
- Performance and retained-state claims remain **unmeasured** until the runtime
  and benchmark harness include this datatype.

## Current result

The first formal increment is build-clean.

- `AegisSheet.lean` defines a union-merge MRDT over stable row, column, cell,
  and range identities. Its generation guard checks the exact issuer context,
  stable-ID applicability, before-images, overwritten cell versions, and local
  selective-undo provenance.
- The ordinary and virtual-LCA convergence certificates, safety certificate,
  and incremental-machine sequential refinement are machine-checked. The complete
  merge/undo tables are encoded as named policy entries.
  `AegisSheetSequential.lean` defines the production sequential reference
  machine that stores observed-remove tokens, position candidates, active cell
  versions, and active range versions without replaying the event log. Its
  representation relation is exact and universal: every chronological
  enumeration of a replicated event set must produce the same complete
  incremental state. Lean proves uniqueness from strict Lamport chronology.
  It also proves, by induction over every guarded minted history, that replay
  produces exactly the cache materialization of the replicated event set.
  The induction preserves metadata validity, timestamp uniqueness, and
  seen-frontier validity, and covers axis, cell, range, and semantic-purge
  steps. A second general theorem proves that the incremental cache observer
  equals the declarative MRDT observer on every guarded history. Its component
  lemmas cover observed-remove axis tokens, latest positions, ordinary cell
  overwrites combined with purge masks, and range values. The proof derives
  cell-axis and purge-entry provenance from the generation guard. The public
  certificate relation includes both exact materialization and this observation
  equality. The obsolete event-list certificate has been removed.
  Concrete SPOTs cover the nontrivial policies: update versus
  remove, persistent cell conflicts, selective undo, move versus remove/edit,
  two moves, two inserts, insert versus move/remove, and undo of insert, remove,
  and move. The Scala audit added the previously missing Table 4 move/insert
  and move/move undo SPOTs; the stable-ID model produces the published
  positions in both cases.
- Range SPOTs cover border deletion, interior deletion, crossing endpoints,
  removal, and recreation.
- `AegisSheetGC.lean` refutes naive local purging with a kernel-checked
  continuation: purge is invisible while a row is absent, but undoing its
  removal later distinguishes the full and filtered states. It then implements
  a replicated semantic purge marker and a payload collector. Each reclaimed
  cell version leaves a compact `timestamp -> coordinate` entry. Lean proves
  that collection retains every causal timestamp, preserves the complete
  query, and is idempotent. The packaged `StateGCCertificate` proves closure
  under guarded updates and compatible branch merges. Generic authored
  frontier evidence derives the marker's roster acknowledgements. Directed
  checks show that late axis restoration and stale payload re-delivery cannot
  revive old contents, while a fresh post-cutoff edit remains visible.
- The incremental machine physically removes the covered cell versions when
  it applies the marker. It retains the timestamp-coordinate entries because
  a cell edit is also an observed-remove keep token for its row and column.

## Remaining validation boundary

The public packaged sequential certificate targets the independent in-place
machine. Its guarded-history theorem proves both exact cache materialization
and equality with the declarative MRDT query, not only uniqueness of
chronological replay. This does not establish equivalence with Bismuth's Scala
implementation, which uses different list and undo machinery.

The semantic collector's full `StateGCCertificate` is complete. Merge closure
uses the execution invariant that a timestamp identifies the same event on
both branches; the framework now exposes this compatibility premise instead
of quantifying over impossible timestamp-colliding branches. The generic
distributed protocol proves when authored frontier evidence is complete, and
the AegisSheet bridge converts that evidence into the marker's roster
acknowledgements. Authenticating transport remains a runtime concern outside
the MRDT semantics.

The Scala artifact uses `ReplicatedUniqueList.filter` and undo closures rather
than this module's declarative query. The completed source and differential
audit found index-based undo and range-validation bugs; see
`docs/aegissheet-scala-audit.md`. Do not claim algorithm equivalence until those
regressions pass. The Scala `purgeTombstones` method exposes no cutoff or
frontier argument. Its artifact documentation explicitly treats purge as a
semantic removal, not silent GC; the tested concurrent-edit and later-undo
controls agree with that interpretation.
