# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual LCAs, and garbage collection.

The current framework is under [`Sal/MRDTs`](Sal/MRDTs). Its raw `MRDTSig`
contains only datatype operations. Client minting discipline is supplied by a
single `Issuance.CanIssue` relation. An independent `SequentialSpec` supplies
the abstract state, legal histories, and queries. `InteractionSpec` states
whether two operations are independent or conflicting and, for a concurrent
conflict, which order the sequential explanation requires. `VerifiedMRDT`
combines these with widened convergence, a representation relation, and a
`SequentialCorrectnessCertificate`. Ordinary
convergence is derived by embedding the ordinary trace in the widened
semantics. Safety and datatype-state GC are separate optional certificates.
Proof-local invariants and applicability predicates are not part of the public
API.

The framework supplies:

- ordinary and canonical virtual-LCA operational semantics;
- the convergence metatheory;
- distributed commit-history GC and its refinement theorem.

`CRDTSig` contains no arbitration field. The historical resolver remains an
internal `ReplayPolicy`; the certified Join route uses its unconstrained
default. It is not the datatype's public interaction policy.

A datatype may separately supply state-GC representation and protocol
certificates. The runtime implementation lives in [`runtime`](runtime).

## Verification

```sh
./scripts/check-mrdt-refactor.sh
```

The historical conditioned framework and refuted MRDT experiments are retained
on the archive branch `archive/conditioned-mrdts-2026-08-21`, not on `main`.
