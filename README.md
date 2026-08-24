# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual LCAs, and garbage collection.

The current framework is under [`Sal/MRDTs`](Sal/MRDTs). Its raw `MRDTSig`
contains only datatype operations. Client minting discipline is supplied by a
single `Issuance.CanIssue` relation. An independent `SequentialSpec` supplies
the abstract state, legal histories, and queries. `ArbitrationSpec` states the
public semantic dependence policy without quantifying over malformed concrete
states. `VerifiedMRDT` combines these with widened convergence, representation,
and legalization. Ordinary
convergence is derived by embedding the ordinary trace in the widened
semantics. Safety and datatype-state GC are separate optional certificates.
Proof-local invariants and applicability predicates are not part of the public
API.

The framework supplies:

- ordinary and canonical virtual-LCA operational semantics;
- the convergence metatheory;
- distributed commit-history GC and its refinement theorem.

A datatype may separately supply state-GC representation and protocol
certificates. The runtime implementation lives in [`runtime`](runtime).

## Verification

```sh
./scripts/check-mrdt-refactor.sh
```

The historical conditioned framework and refuted MRDT experiments are retained
on the archive branch `archive/conditioned-mrdts-2026-08-21`, not on `main`.
