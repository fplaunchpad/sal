# TreeMove's incremental undo/redo implementation

The research question is whether the source algorithm's materialized tree and
undo log can replace Sal's finite-event replay carrier while retaining exact
state merge proofs and the existing independent tree specification. The new
implementation answers this for coherent source log states, without making
query equality stand in for a merge law.

## Source algorithm and state

The source is Kleppmann, Mulligan, Gomes and Beresford, *A highly-available move
operation for replicated trees*, Fig. 4 and Sections 3–4, in the local copy
`_references/kleppmann-et-al-tree-move-tpds-2021.pdf`.

`TreeMoveIncremental.lean` retains a descending list of `LogEntry` values and
the current tree. Each entry records the original event and the moved child's
parent and edge metadata before that event. The function-valued tree enforces
unique parents structurally. `sourceMove` uses the source's ancestor/self-move
cycle test. Rejected moves still receive a log entry.

`applyRaw` implements Fig. 4's recursive undo/insert/redo:

1. If the new event precedes the newest entry, restore that entry's old edge
   and recurse through the remaining log.
2. Apply the new event at its timestamp position.
3. Redo the removed entries, recomputing every old-parent field and every
   cycle decision against the changed tree.

On supported distinct timestamps the full-key comparison is exactly the source
timestamp comparison (`source_comparison`, `applyRaw_eq_sourceApply`). The
replica/payload tie extension only totalizes otherwise unsupported clock ties.
The source assumes duplicate suppression by the delivery protocol. `receive`
implements that suppression, which is also needed when two MRDT versions
share earlier operations.

The MRDT state exchange is a derived adapter for the source's operation-based
algorithm. `mergeRaw` delivers the other branch's log to the first branch through
`receive`. It does not replay either branch from the empty tree, and it ignores
the ancestor, as does the existing finite-event union semantics. The
query reads the maintained tree directly. Issuance checks event freshness
and reserved sentinels; it does not inspect tree visibility.

## Exact refinement and nonvacuity

`undo_push` proves actual restoration of the prior tree, including the case
where a move was rejected. `applyRaw_build` proves that late insertion updates
the entire normal-form state: both tree and all undo metadata.
`canonical_tree` identifies that tree with the existing cycle-rejecting replay
semantics. `candidate_safe_iff` proves the source ancestor test and the old
candidate-acyclicity test equivalent on safe trees.

The raw algorithm is exposed independently of a correctness subtype.
`Coherent` asserts that the stored undo log and tree are the normal form of
the events actually in that log. Its closure is proved from the algorithm:
`receive_coherent` and `mergeRaw_coherent`. `run_coherent` establishes coherence
for every receive trace from the empty state, with no caller-supplied replay
witness or requested answer. `State` restricts the MRDT carrier to those
coherent states; fabricated mismatched log/tree pairs are outside the laws.

`encode` and `decode` form an exact-state isomorphism with finite event sets.
Injectivity identifies full log/tree states, including rejected events and
old-parent metadata. The five kernel equations use that injectivity, not an
observational relation. `fiveVC` invokes `CommonVerification.verify`, and
`joinAt` invokes the shared finite event-set induction through
`automatedJoinAt`. No prior TreeMove Join theorem supplies these merge proofs.

## Independent history and endpoints

`sequentialSpec` in `TreeMoveIncrementalCertificate.lean` reuses the independent
in-place tree machine: a sequential move changes a child's parent unless this
would introduce a cycle; its query hides trash and its descendants. It does
not call the incremental update, merge, log insertion, or rendering function.
`SourceClientLegal` requires distinct events in timestamp-key order and a
causal origin satisfying the editor wrapper. `sourceClientLegal_iff` proves
that this is precisely `SequentialLegal` plus reserving root and trash as
children. There is no hidden visibility, destination-existence, replay witness,
or requested-answer premise in this legality predicate.

The wrapper `sourceApplicable` requires a fresh `(time, replica)` identifier at
the origin and forbids moving either distinguished sentinel. All other moves
are eligible: creating a fresh child, moving a visible or hidden child,
deleting by moving to trash, restoring a hidden parent, rescuing a descendant,
and moving to an absent or hidden destination. This allows the forests of
Section 4.1. Reserved sentinel children are an explicit application restriction;
the raw source algorithm has no such reservation. Certified executions supply
the stronger globally distinct scalar timestamps, so the raw comparison is
literally Figure 4's timestamp comparison on those executions. The key extension
still defines behavior on raw tied-clock inputs outside that source contract.

`history` reconstructs original causal origins and uses one timestamp-ordered
word for implementation replay, visibility order and independent sequential
admission. `verified : VerifiedMRDT D` packages the independent tree relation
and this sequential proof with the new merge proof. `certified`, `certifiedV`,
`executions` and `executionsV` cover all allocated versions and visited
configurations of ordinary and recursive-base certified executions. Their
execution hypotheses are the framework's honest minting, global timestamp
freshness, causal support/closure and valid merge-base evidence, together with
the wrapper above. There is no assumption that a requested observation is
correct. `materialized_safe` and `observable_safe` prove acyclicity.

The public replacement route is `Incremental.D` + `Incremental.generation` +
`Incremental.verified` for the production interface, and `Incremental.language`
with `Incremental.certifiedV` / `executionsV` for the history-language and
recursive-base endpoints (ordinary endpoints are `certified` / `executions`).
The old visible-client language is intentionally not equal to this language:
that contract incorrectly excluded source deletion. A public replacement must
switch its generation and sequential specification together. The endpoint audit
checks that all four public roots consume source undo/redo, exact-state kernels,
`CommonVerification.verify`, and `Raw.join_at_sizes`, and forbids reuse of the
old TreeMove Join or correctness certificate. Only standard logical axioms occur.

The source paper already supplies Isabelle proofs of unique parents,
acyclicity, permutation convergence, and SEC. Sal's contribution here is the
checked refinement to its existing independent sequential tree language and
the exact-state connection to its five-VC MRDT and recursive-base framework;
the source algorithm and its convergence result are not new research claims.

## Validation and present boundary

The 15 hand-derived PASS+FAIL SPOT blocks exercise accepted-to-rejected cycle
reclassification after late delivery, the failure of direct late application
without undo, full-state delivery-order equality, concurrent merge preserving
both operations, retention of rejected operations, recomputed undo metadata,
and self-move rejection. Source client controls cover deletion, moving a hidden
child, restoration, absent/hidden destinations, and independent-language
admission. Deletion hides a whole subtree while retaining descendant edges;
rescue reveals just the moved descendant; restoring its parent reveals the
retained subtree. Concurrent deletion/rescue merges in both operand orders
retain the rescue. Each block also rejects a tempting degenerate behavior.
No expected answer is generated by `#eval`.

This is a Lean implementation and kernel-checked refinement. As in the
existing model, the function-valued tree and transitive-closure ancestor test
are noncomputable. A finite-map carrier with executable ancestry checking,
runtime extraction, and performance measurements have not been established.
The production registry and its coverage inventories now select the incremental
carrier and source client language. Automation and paper measurement roots
select its five VCs and independent history proof. The old finite-event model
and its GC protocol remain internal dependencies; the new carrier is classified
as staged for GC, with exact package equality checked across the inventories. No GC algorithm or certificate is claimed for the new
carrier; any later GC support needs a separate compatible transport.

## Independent source review — 15 October 2026

The parent reviewed the original paper's Figure 4 and Sections 3.1, 3.6 and
4.1, alongside the staged algorithm and issuer. The earlier visible-destination
guard prevented source deletion. This revision fixes both generation and
independent legality, including hidden-child restoration. The parent review
also confirmed that the source permits forests with a separate trash root;
parent-existence in Section 3.6 belongs to an optional creation optimization,
not the base Figure 4 algorithm. The new wrapper therefore imposes no such
parent-existence requirement.

The initial eight-block port and both existing tree SPOT targets were rebuilt
by the parent before this correction. The revised 15-block target and four-root
dependency/axiom audit were checked with
`lake build Sal.MRDTs.Instances.TreeMoveIncrementalSPOT`. The parent independently rebuilt the revised target (3,418 jobs), reviewed
the algorithm, source comparison, guard, history proof and dependency audit,
and integrated the replacement. The full registry/coverage ledger build passed
3,864 jobs. Paper measurement and complete repository checks are recorded in
`experiments/paper-implementation/README.md` after integration.
