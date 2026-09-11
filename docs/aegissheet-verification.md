# AegisSheet verification enquiry

## Goal

Verify a compositional spreadsheet MRDT against the merge and undo outcomes in
Tables 3 and 4 of *AegisSheet: A Compositional CRDT for Collaborative
Spreadsheets*. Cover stable row and column identities, persistent cell
conflicts, nonduplicating moves, anchored ranges, and tombstone collection.

## Sequential abstraction enquiry

- **Goal:** Determine whether AegisSheet refines a conventional sequential
  spreadsheet state, rather than only an incremental interpreter of its
  causally annotated events.
- **Candidate claim:** The visible `View`, plus explicit client-level selective
  undo information, determines every future legal observation. Causal tokens,
  timestamped active versions, historical position candidates, and replicated
  purge evidence can otherwise be quotiented away.
- **Falsifier:** Find two reachable legal histories with the same candidate
  abstract state and one admissible merged continuation whose observations
  differ. Minimize each witness and retain it as a checked SPOT.
- **Formal oracle:** Executable projections and continuation theorems in
  `AegisSheetSequential.lean`, followed by a refinement theorem for the
  strongest quotient that survives the SPOTs.
- **Reality oracle:** Tables 3 and 4 and Figure 1 of the AegisSheet paper define
  the client-visible outcomes. They do not by themselves validate hidden
  timestamp or purge state. The Scala implementation remains a refuted
  implementation oracle at commit `dd4c614`.

The audit must preserve either outcome. If a smaller client ADT survives, make
it the public `SequentialSpec`. If a same-view distinguishing continuation
refutes that ADT, state the necessary hidden semantic history explicitly and
do not describe the theorem as refinement to a conventional spreadsheet.

## Candidate claim

A grow-only set of causally annotated spreadsheet actions, queried by the
AegisSheet conflict policies, converges under union merge. Every certified
version has a causal-origin-legal serialization that refines an independent
incremental spreadsheet reference. Every published matrix outcome is a checked
fixture. Tombstone collection requires either a semantic cutoff marker or a
protocol that rules out later revival.

The public merged-history theorem defines an event as origin-legal when
some timestamp-earlier subset of the serialized prefix satisfies the
executable `applicable` predicate. The predicate itself checks that this subset
has exactly the causal timestamps encoded in `event.seen`. Lean proves that
every certified ordinary or virtual-merge-base version has a chronological
origin-legal enumeration, and that the incremental machine materializes and
observes that enumeration exactly.

## Falsifier

Any of the following results refutes the claim:

- a published matrix fixture evaluates to a different result;
- two merge orders produce different observations;
- a guarded linear trace disagrees with the reference interpreter;
- the two independently applicable empty-origin insertions fail the new
  merged-history legality predicate;
- an event whose encoded origin names an unavailable timestamp passes the new
  legality predicate;
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

The current formal result is build-clean.

- `AegisSheet.lean` defines a union-merge MRDT over stable row, column, cell,
  and range identities. Its generation guard checks the exact issuer context,
  stable-ID applicability, before-images, overwritten cell versions, and local
  selective-undo provenance. It also requires the issuer's Lamport timestamp
  to exceed every direct or compact causal timestamp in that context.
- The ordinary and virtual-merge-base convergence certificates, safety certificate,
  and incremental-machine sequential correctness theorem are machine-checked. The complete
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
  cell-axis and purge-entry provenance from the generation guard.
  For merged histories, `CausalOriginLegal` validates each operation against
  an honest causal-origin set contained in the serialization prefix instead of
  pretending that concurrent predecessors were visible at issuance. The
  timestamp-canonical witness theorem derives those origins from
  `MintHonest` and causal closure. The generation guard explicitly requires
  each Lamport timestamp to exceed every timestamp in its origin; freshness
  alone cannot establish chronological order. The resulting `VerifiedMRDT`
  proves exact event-set membership, interaction-order respect, sequential
  legality, state refinement, and query equality for ordinary and virtual-merge-base
  executions. The internal replay compatibility package remains, but is not
  the public result.
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

## Sequential abstraction result

The abstraction audit refutes the candidate conventional spreadsheet state.
`AegisSheetAbstraction.lean` contains three reachable pairs with identical
complete `View`s. Every operation is applicable at its encoded causal origin,
and Lean checks that each combined history satisfies `CausalOriginLegal`.

- A move to the row's current position changes no visible field but creates a
  fresh observed-remove keep token. The same concurrent removal deletes the
  row from the base state and preserves it in the moved state.
- Replacing a cell write by a fresh write of the same value leaves the visible
  cell unchanged. The same concurrent selective overwrite then produces
  `{1}` from the base state and `{0, 1}` from the reversioned state.
- Replacing a range version by a fresh version of the same anchored range also
  leaves the view unchanged. A concurrent selective range edit distinguishes
  the two states in the same way.

The capstone `no_view_only_step` proves that no deterministic transition
function over `View` can implement even the first pair and its common legal
continuation. `row_tokens_distinguish_future`,
`cell_versions_distinguish_future`, and
`range_versions_distinguish_future` identify the lower bound: exact
observed-remove tokens and exact active cell/range write identities are
semantic history. Passing selective-undo IDs with an operation does not remove
this need because the state must know which named versions remain active.

The remaining fields have a different role. `knownRows` and `knownColumns`
are finite-domain indexes for the function-valued Lean representation. A purge
marker's acknowledgements and covered-entry map justify and execute
collection, while its cutoff/coordinate mask has semantic effect. Obsolete
position candidates are a plausible quotient on chronological histories
because every later axis update has a greater Lamport timestamp, but this
audit does not package that quotient as a replacement state machine. The
checked result is a semantic lower bound, not a proof that the current record
is globally minimal. The public `clientSpec` is therefore described precisely
as a causally aware incremental spreadsheet machine, not as a conventional
single-user spreadsheet.

## Remaining validation boundary

The public packaged sequential certificate targets the independent causally
aware in-place machine. Its causal-origin merged-history theorem proves both exact cache
materialization and equality with the declarative MRDT query, not only
uniqueness of chronological replay. The positive control accepts two honest
concurrent empty-origin insertions; the negative control rejects an event that
cites an unavailable origin timestamp. This does not establish equivalence
with Bismuth's Scala implementation, which uses different list and undo
machinery.

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
