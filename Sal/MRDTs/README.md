# Verified MRDT framework

This directory contains the current paper artifact. The raw datatype signature
has no invariant or applicability fields. A datatype implementation supplies a
single origin `Issuance` relation, an independent `SequentialSpec`, convergence,
an `InteractionSpec`, sequential correctness, and representation through
`VerifiedMRDT`. `InteractionSpec` classifies pairs as independent or as
conflicts with an optional concurrent direction. Causal conflicts follow
visibility. Safety is an optional separate certificate. Convergence
certificates store only the widened theorem; the ordinary theorem is derived.
The raw-fold package is named `ReplayVerifiedMRDT`. It supports internal replay
proofs and datatypes with a checked negative classification; it is not the
public sequential-correctness result. The framework supplies the ordinary and
canonical virtual-LCA operational semantics and distributed commit-history GC.
Datatype-state GC is an optional representation certificate.

The executable `CRDTSig` contains only state transitions, merge, and query.
The old replay resolver is a proof-local `ReplayPolicy`, not a datatype field
or client arbitration API. `Instances/InteractionSPOT.lean` checks the key
controls: LWW admits a three-write timestamp chain, and concurrent add/remove
uses remove-before-add to explain add-wins.

## Minimal distributed-GC state

The paper-facing commit collector stores only a head and a retained commit set
at each replica:

```text
World = Replica → { head : Version, commits : Set Version }
```

The fixed roster and immutable commit metadata are protocol parameters. Each
operation commit carries an optional author; roots and merge commits are
unauthored. The collector derives per-author frontier evidence from retained
commit records and reachability. It does not store `self`, a copied roster, an
author set, or a per-author commit index in `Local`. The datatype-rich `core`
in `GC.Runtime` is ghost specification state used by the refinement theorem,
not a second physical copy of the runtime store.

`Instances/TreeMove.lean` formalizes the TPDS replicated tree-move algorithm
as a finite event-set MRDT with canonical timestamp replay. It proves merge
convergence, cycle-safe rendering, issuer checks, and the framework's
direct chronological mutable-tree refinement. The incremental undo/redo refinement and
stable-prefix/trash collection are packaged as a concrete `StateGCProtocol`.
The generic composition theorem combines that protocol directly with asynchronous
distributed commit-history GC.

`Instances/AegisSheet.lean` is an executable spreadsheet-intent model derived
from the PaPoC 2026 merge and undo matrices. It packages stable identities,
update-wins deletion conflicts, persistent cell conflicts, moves, selective
undo, and anchored ranges as a convergent union-merge MRDT. The companion
`AegisSheetSequential.lean` proves guarded refinement to an independent
incremental spreadsheet machine. Strict Lamport chronology gives each finite
event set one sequential enumeration, so the representation relation fixes the
machine's complete token, position, cell, range, and purge state rather than
echoing the event list. It also proves that, on every guarded minted history,
the incremental and declarative observers agree on rows, columns, latest
positions, cell values after purge masking, and range values; this equality is
part of the public sequential relation. The companion
`AegisSheetGC.lean` proves that naive local tombstone purging is not a silent
state GC under later revival. It implements a replicated semantic cutoff
marker whose compact timestamp-to-coordinate entries preserve causal context
and observed-remove axis tokens after cell payload collection. Its
`StateGCCertificate` proves query preservation, collection idempotence, and
closure under guarded updates and compatible branch merges. Generic authored
frontier evidence derives the marker's configured-roster acknowledgements.
This remains an internal `ReplayVerifiedMRDT`: two independent origins can
each pass issuance while neither ordering passes the old whole-prefix guard.
`concurrent_origins_not_guarded_chronological` checks that obstruction; a
public spreadsheet specification must describe each event's encoded origin
view instead of rechecking it against the merged serialization prefix.
Equivalence with the Bismuth Scala
implementation is refuted at commit `dd4c614`: the audit in
`docs/aegissheet-scala-audit.md` records move-undo, range-undo, and crossed-range
counterexamples.

The neutral transition-system and CRDT definitions used by the metatheory live
in `Framework/Base`; they are not the Shapiro op-based-to-state-based emulation
development.

Run the release gate with:

```sh
./scripts/check-mrdt-refactor.sh
```
