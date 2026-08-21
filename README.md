# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual LCAs, and garbage collection.

The current framework is under [`Sal/MRDTs`](Sal/MRDTs). Its raw `MRDTSig`
contains only datatype operations. Client minting discipline is supplied by a
`GenerationContract`; observable invariants by a `SafetyCertificate`; intended
single-replica behavior by a `SequentialRefinement`. `VerifiedMRDT` combines
those certificates with ordinary and virtual-LCA convergence.

The framework supplies:

- ordinary and canonical virtual-LCA operational semantics;
- the convergence metatheory;
- distributed commit-history GC and its refinement theorem.

A datatype may separately supply state-GC representation and protocol
certificates. The runtime implementation lives in [`runtime`](runtime).

## Verification

```sh
./scripts/check-mrdt-refactor.sh
cd runtime && npm test
```

The historical conditioned framework and refuted MRDT experiments are retained
on the archive branch `archive/conditioned-mrdts-2026-08-21`, not on `main`.
