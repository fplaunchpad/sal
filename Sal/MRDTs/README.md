# Verified MRDT framework

This directory contains the current paper artifact. The raw datatype signature
has no invariant or applicability fields. A datatype implementation supplies a
generation contract, convergence proof, sequential refinement, and safety
certificate through `VerifiedMRDT`. The framework supplies the ordinary and
canonical virtual-LCA operational semantics and distributed commit-history GC.
Datatype-state GC is an optional representation certificate.

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

The neutral transition-system and CRDT definitions used by the metatheory live
in `Framework/Base`; they are not the Shapiro op-based-to-state-based emulation
development.

Run the release gate with:

```sh
./scripts/check-mrdt-refactor.sh
```
