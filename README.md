# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual merge bases, and garbage collection.

The current framework is under [`Sal/MRDTs`](Sal/MRDTs). Its raw `MRDTSig`
contains only datatype operations. Client minting discipline is supplied by a
single `Issuance.CanIssue` relation. An independent `SequentialSpec` supplies
the abstract state, legal histories, and queries. A single `ReplayPolicy`,
stored as `VerifiedMRDT.rc`, supplies any design-specific direction between
concurrent events. The sole linearization order `loOn` is derived from that policy and
visibility: visibility is retained exactly for conflicting pairs, while
`Either` contributes no edge. `VerifiedMRDT` combines these with widened convergence, a representation relation, and a
`SequentialCorrectnessCertificate`. Ordinary
convergence is derived by embedding the ordinary trace in the widened
semantics. Safety and datatype-state GC are separate optional certificates.
Proof-local invariants and applicability predicates are not part of the public
API.

The framework supplies:

- ordinary and canonical virtual-merge-base operational semantics;
- the convergence metatheory;
- distributed commit-history GC and its refinement theorem.

`UpdateSig` is a merge-free proof-level algebra projected from `MRDTSig`, not
a second datatype interface. Historical binary proofs request their merge
operation separately through `HistoricalBinaryMerge`.

The verified LWW register shows why `rc` may be nontrivial even when updates
commute. Its timestamped state uses `max` for update and merge, while its sole
`rc` policy orders writes by timestamp. A sorted overwrite history supplies
the ordinary sequential-register explanation.

The verified multi-value register stores only live tagged values. A local
write replaces what it observed; ancestor-relative merge preserves concurrent
writes. `MVRLive.verified` proves the public contract for ordinary and virtual
executions, including causal maximality and ordinary sequential behavior.

`FugueMax.verified` certifies the exact FugueMax issuer and enriched state
against a plain-list specification. One witness establishes list correctness
and maximal non-interleaving for ordinary and virtual executions. Birth/origin
metadata is implementation-side; datatype-state collection remains staged.

A datatype may separately supply state-GC representation and protocol
certificates. RGA has a checked `(id,parent)`/live-set packing
certificate. It retains deleted identifiers internally to integrate operations
minted concurrently with deletion, while issuance permits a new insertion only
at a root or live anchor. Rich SidedPeritext, TreeMove, and
AegisSheet supply the other representation-changing collectors or protocols.
The runtime implementation lives in [`runtime`](runtime).

## Verification

```sh
./scripts/check-mrdt-refactor.sh
```

This CI gate checks every production package against the explicit selections in
[`public-contracts.json`](public-contracts.json): implementation, issuance,
`rc`, sequential specification (including legality and queries), and state
relation. Lean must connect them through the public certificate for ordinary
and virtual executions. Replay-only packages cannot pass. Registry coverage,
certificate axioms, runtime mappings, and negative controls are also checked.
See [the gate and its review boundary](docs/production-packaging.md).
Passing this gate is not human approval of a specification; the cross-datatype
semantic audit remains open.

The historical conditioned framework and refuted MRDT experiments are retained
on the archive branch `archive/conditioned-mrdts-2026-08-21`, not on `main`.
