# Sal

Sal is a Lean formalization and JavaScript implementation of mergeable
replicated datatypes (MRDTs), including RGA-based text, rich-text Peritext,
canonical virtual merge bases, and garbage collection.

On branch `paper1`, [`Sal/MRDTs/Paper1`](Sal/MRDTs/Paper1) mechanizes the
submission's prefix-closed history specifications and explicit per-query
RA-linearizability criterion. Its operation-level policy requires exact concrete
noncommutation and no length-two conflict chain. Soundness retains issuance and
execution evidence, with local sequential simulations or suitable-history
proofs supplying the bridge to specification acceptance. The exact paper
OR-set retains every addition tag and has an ancestor-aware Join proof.

The agreed sequential update interface retains the full
`(timestamp, replica, application operation)` input supplied to MRDT updates.
`Paper1.RGAEventSpec` implements it with an independent ordinary list and
allocation registry: insertion uses its supplied timestamp as the element ID,
and replica metadata has no effect on this datatype's list semantics. It proves
the literal and stronger specification-visible criteria for ordinary and
virtual certified RGA executions, including all stored versions. Sequential
witnesses preserve event inputs while permitting timestamp order to change.

The active manuscript criterion and the separate specification-visibility
criterion are separate definitions. The active criterion admits the no-op
removal mutation: every raw execution has a removals-first explanation, despite
the incorrect sequential behavior. The stronger candidate rejects the checked
reachable mutation. The earlier operation-only RGA investigation is retained
as a counterfactual to the agreed full-input interface. Its language uses independent,
globally fresh nondeterministic allocation because its update label omits the
inserted identifier. Certified RGA executions satisfy the literal criterion.
Both operation-only languages—globally fresh allocation with missing-anchor
no-ops, and strict live-anchor insertion—fail the stronger criterion on a
checked honestly certified eight-event execution from the empty initial
configuration. The proofs exclude every witness order and allocation choice,
including unbounded natural-number allocations. With explicit insertion identifiers in application
labels, independent strict and missing-anchor list languages satisfy the
stronger projected criterion on all ordinary and virtual certified executions.
The projection is explicit and genuinely changes the application alphabet; the
concrete datatype and issuer are unchanged. `Paper1.RGAComparison` checks both
negative and positive criteria on the same reachable read `[5,4,8,7]`.
These paper-facing results do not assert a migration of every
production package to the restricted policy.

The full-input migration is checked against the complete 22-entry production
registry in `Paper1.MigrationCoverage`: twelve entries have independent
history-language specifications and ordinary/virtual certified guarantees for
every allocated version, nine have proofs that the paper's operation-only
exact/noncommutation plus no-chain assumptions cannot hold on their unchanged
carriers, and LWW is explicitly excluded. The compatible entries are the three
add/set stores, three flat counters, two flat grow-only stores, bounded counter,
plain RGA, TreeMove, and AegisSheet. Coverage retains each original signature
and issuer and proves equality with the original registry, not just its names.
The exact paper OR-set is an additional checked instance outside that registry.
Including efficient OR-set's direct proof, thirteen of the original twenty-two
entries have the new specification-visible history criterion proved. Eight
retain their original production verification without that new proof; LWW
remains excluded from this migration.

`Paper1.EventBridge` exposes full-input simulations, independent fold-history
acceptance, mint-sensitive and execution-sensitive chosen-history premises,
Join/five-VC soundness, and finite-trace guarantees. TreeMove and AegisSheet use
`GuardedHistory` to retain their independent in-place machines and causal-origin
legality. BoundedCounter retains nonnegative account guards; its global
commutation-compatibility VC fails, while its honest causal witnesses prove
specification-visible correctness.

The nine exceptions are efficient OR-set, queue, compact MVR, and six embedded
RGA/editor registry entries. These are obstructions to all-state concrete replay
assumptions, not failures of the sequential specifications or the existing
production certificates. Efficient OR-set additionally has a direct full-input
ordinary-set history proof under its retained policy. `main` already proves
that its all-state replay laws are unavailable; `paper1` strengthens that result
to impossibility for any operation-only exact policy. The embedded RGA
obstructions use raw event pairs that need not satisfy honest issuance.

`Paper1.CommutationBridge` exposes a separate specification-compatibility VC:
concrete commutation must imply observable contextual commutation in the
independent history language. This is the contrapositive of the existing
specification-conflict coverage premise. It makes specification-conflict
visibility follow from the replay order, supports full event inputs, and
combines with the five merge VCs and history acceptance to prove the stronger
criterion. The exact OR-set satisfies it; the no-op-removal mutant fails it.
This is a sufficient route, not a requirement on every datatype: certified RGA
continues to use its issuance-based chosen-history proof. The VC does not
silently change the literal RA definition. `appendix_soundness.tex` is excluded
from the manuscript build and is not an included paper appendix.

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

The paper branch has an additional theorem and axiom gate:

```sh
./scripts/check-paper1.sh
```

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
