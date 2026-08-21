# Verified MRDT framework

This directory contains the current paper artifact. The raw datatype signature
has no invariant or applicability fields. A datatype implementation supplies a
generation contract, convergence proof, sequential refinement, and safety
certificate through `VerifiedMRDT`. The framework supplies the ordinary and
canonical virtual-LCA operational semantics and distributed commit-history GC.
Datatype-state GC is an optional representation certificate.

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
