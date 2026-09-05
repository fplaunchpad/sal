# Verified MRDT framework

This directory contains the current paper artifact. The raw datatype signature
has no invariant or applicability fields. A datatype implementation supplies a
single origin `Issuance` relation, an independent `SequentialSpec`, convergence,
an `InteractionSpec`, sequential correctness, and representation through
`VerifiedMRDT`. `InteractionSpec` classifies pairs as independent or as
conflicts with an optional concurrent direction. Causal conflicts follow
visibility. Safety is an optional separate certificate. Convergence
certificates store only the widened theorem; the ordinary theorem is derived.
The raw-fold package is named `ReplayAdequateMRDT`. It supports internal replay
proofs and datatypes with a checked negative classification; it is not the
public sequential-correctness result. The framework supplies the ordinary and
canonical virtual-merge-base operational semantics and distributed commit-history GC.
Datatype-state GC is an optional representation certificate.

`PackagedMRDT` is the release boundary: it pairs one raw signature with a
`VerifiedMRDT` for that exact signature. `Metatheory/ProductionLedger.lean`
is the typed registry of released datatypes. Replay-only results,
counterexamples, and internal policy signatures live in
`Metatheory/NegativeLedger.lean`; they cannot be registered by name alone.

The proof-level `UpdateSig` is a merge-free projection of `MRDTSig`; it is not
an executable datatype interface or transition system. Historical binary
proofs request their merge operation separately through
`HistoricalBinaryMerge`. The old replay resolver is an
internal `ReplayPolicy`, not a datatype field or client arbitration API. The
certified Join route uses its unconstrained default.
`Instances/InteractionSPOT.lean` checks the key
controls: LWW admits a three-write timestamp chain, and concurrent add/remove
uses remove-before-add to explain add-wins.
`Instances/AegisSheetRetentionSPOT.lean` pins what a spreadsheet
representation must retain about removed rows and columns: range resolution
and update-wins revival both read a removed identifier's last position, eager
re-anchoring and remove-wins are refuted, and undoing an older cell write
revives a causally later removal.
`Instances/AegisSheetMaterialised.lean` and its companions (`Join`,
`Certificates`, `Equivalence`, `Update`, `Bridge`) re-encode the spreadsheet
as a materialised three-way MRDT: flat sets of keep tokens, cell versions, and
range versions with named removal, a last-writer-wins position register, and
plain deletion for purges. `canon` reads the materialised state off a
union-model event set. Proved: the Join restricted to honest replay contexts,
replay adequacy under issuance at the materialised state, observation
equivalence with the union model's view on purge-free histories, preservation
of `canon` by updates issued at any past of an honest history, and
`cross_model`: every version of a certified execution of the union model is
the materialised fold of an issue-ordered enumeration of its events, with equal
observations when purge-free; and `converse`: every version of a certified
execution of the port without purges and with honest undo is the canonical
state of an issue-ordered union-model history with the same observation.
`verified` packages the design with its own fold as sequential machine, and
`retirement` is its `StateGCCertificate`: the `known` entries of identifiers
without tokens are collected with no evidence and no cross-branch condition,
leaving live data and one register entry per identifier ever positioned. The
purge semantics (plain deletion of covered versions) is specified by `canon`
and validated by differential testing (`docs/aegissheet-materialised/`).
`Instances/LWWRegister.lean` packages the full LWW result: timestamped `max`
updates commute and make the proof-local replay order empty, while the public
interaction order has a timestamp-sorted witness refining to a total
overwrite register.

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
The old whole-prefix legality remains refuted: two independent origins can
each pass issuance while neither ordering passes that guard.
`concurrent_origins_not_guarded_chronological` checks the obstruction. The
public `VerifiedMRDT` instead uses causal-origin legality, which validates each
event against its encoded origin view rather than rechecking it against the
merged serialization prefix.
Equivalence with the Bismuth Scala
implementation is refuted at commit `dd4c614`: the audit in
`docs/aegissheet-scala-audit.md` records move-undo, range-undo, and crossed-range
counterexamples.

The neutral transition-system and replay definitions used by the metatheory live
in `Framework/Base`; they are not the Shapiro op-based-to-state-based emulation
development.

Run the release gate with:

```sh
./scripts/check-mrdt-refactor.sh
```
