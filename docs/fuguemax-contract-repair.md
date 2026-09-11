# FugueMax public-contract investigation

Status: the exact enriched implementation has a machine-checked public
plain-list certificate and same-witness maximal non-interleaving theorem,
for ordinary and virtual certified execution. It is registered as `fugue-max`.
Datatype-state collection and an independent runtime remain absent.

Source of truth: the intended positional FugueMax API and its minting rule,
then public abstract contract, theorem statements, and executable checks.

Goal: connect public list correctness and maximal non-interleaving to the
same implementation and issuance, for ordinary and virtual executions. Do
not substitute `ProductionRGA.sided` or register only coordinate-level replay.

Candidate obstruction: `FMSig.State` retains only live coordinate records,
whereas `mGenInsAt` consults birth/origin records including deleted elements.
Two reachable generator histories may have identical `mFold` states but
require different prepared insertion operations at the same index and time.
If so, the exact generator does not factor through the existing state.

Formal oracle: a kernel-checked pair of reachable histories, equal materialized
states, distinct required prepared operations, and the corresponding
non-factorization theorem. Falsifier: the generated prepared operations agree,
or one history is unreachable. Positive control: the current weak issuance
accepts the produced operation; negative control: it cannot distinguish the
operation required by the other history with the same state.

Reality oracle: the repository's exact `mGenInsAt` rule and hand-derived
one-element/deleted-child example. This is an internal interface audit, not
external implementation validation. No changed framework interface or
physical metadata representation is silently assumed.

## Checked result

`FugueMaxContractSPOT.lean` establishes both histories under the actual
`MaxReach` constructors:

- `shortHistory`: insert identity 1 at index 0;
- `deletedChild`: additionally insert identity 2 after 1, then delete 2.

Their complete materialized `SState` values coincide, including the surviving
coordinate, not just the visible IDs. At replica 0, timestamp 4, index 1, the
short history generates a right child of 1. The other history generates a
left child of the retained birth of 2. Both show `[1,4]` after insertion, so
this is not a claim that the current visible list differs.

The existing weak `fApplicable` accepts both prepared operations on the short
state. `wrong_operation_not_generated` proves that the second operation cannot
be generated from the short history at *any* client position.
`exact_issuance_not_state_predicate` proves that no predicate receiving only
`SState` and the prepared operation can exactly characterize permitted
insertions for both histories. This is stronger than merely refuting a
deterministic state-only preparer.

These are literal kernel-checked controls and a general non-factorization
conclusion from the two witnesses, not a sampling result. Axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. `NegativeLedger` imports
the controls. The production registry remains unchanged.

The user approved retaining birth/origin metadata on the implementation/issuer
side while keeping the public sequential state a plain list. The repair below
implements that representation choice. It does not change the framework's
issuance context or put tombstones in the sequential state.
The existing `FuguePolicyGC` development establishes the analogous live-state
insufficiency for ordinary Fugue and offers full-mint and live-gap summaries.
Those summaries are not automatically FugueMax proofs: the latter also stores
right-origin tags in its variant alphabet. Reuse that approach where possible
instead of assuming that the complete event history must be retained.
The public contract must then combine list correctness and maximal
non-interleaving for the same execution, without assuming a separate
`MaxReach` proof in the public theorem.

## Approved repair

Claim: the live coordinate list and all insertion records suffice to reproduce
the exact positional generator. Delete-event records are unnecessary for
minting. The insertion records include deleted births, origins, and tagged
chains; this is an unbounded sufficient representation, not a collection
result or a proof of minimal storage.

Formal oracle: `FugueMax.prepareInsert_exact`, `prepareDelete_exact`,
`canIssue_insert_exact`, and `canIssue_delete_exact` in `FugueMaxIssuer.lean`.
Falsifier: any full history and client position for which the summary generates
a different record or changes the set of accepted records. All four claims
are machine-checked. `update_exact` and `minted_sync` prove local transition
and birth-union refinement, respectively.

`FugueMaxImplementation.lean` defines the enriched `FugueMax.datatype`:

- Raw state: the live coordinate list and a `Finset MRec` of insertion records.
- Update: change the live list and add an insertion's immutable birth record;
  deletion does not add a metadata record.
- Merge: existing three-way live-list merge and union of the two birth sets.
- Query: the plain list of live identities, as in the actual `MaxReach` model.
- Issuance: run the exact issuer check on an enumeration of the stored births.
- `rc`: the existing insertion-before-own-deletion relation.

The event envelope stores timestamp and replica once. `Payload` carries the
operation, origins, and birth chain. `recordOf` and `eventOf` are inverse
transports to the existing generation record; they do not assume a separate
execution or add a second conflict policy.

`FugueMaxIssuerSet.genAfter_eq_of_births` proves that coherent birth records
determine the generator independently of enumeration order and multiplicity.
The proof uses record uniqueness and key injectivity from `KInv` to show that
the successor argmax is unchanged. Consequently, the existential enumeration
in the issuance predicate cannot authorize a different operation.
`insertion_issuance_exact` and `deletion_issuance_exact` connect that predicate
to the actual `mGenInsAt` and `mGenDelAt` rules on coherent histories.
`rawFold_exact` proves full implementation-state refinement of local event
folds, not only query equality. `issuer_merge_refines` proves that the
executable list-based issuer merge implements the finite-set signature's
merge. The subsequent `join_of_mint` proof establishes the general
live-state merge/replay connection described below.

The check retains the existing total-index behavior: an out-of-range insert
uses the root anchor, and an out-of-range delete names sentinel zero and is a
no-op. The finite executable search includes representatives of those cases.
It enforces positive timestamps and the insertion rule's local Lamport bound.
Global event freshness remains the execution framework's responsibility.
The execution proof handles sentinel deletes separately; it does not apply
the old coordinate-replay premise that every delete has a birth witness.

## Controls and test scope

`FugueMaxIssuerSPOT.lean` checks:

- Both reachable histories accept their exact next insertion.
- The short history rejects the deleted-child history's prepared insertion,
  both in the executable guard and the finite-set signature's predicate.
- Deletion retains insertion metadata but no delete-event records.
- Removing deleted births changes the next generated record in the pinned
  counterexample.
- Incremental preparation, guards, updates, three-way merge, and post-merge
  minting agree with the original full-history model on generated forks.
- Reversing or duplicating birth enumerations does not change post-merge mints.

Plausible runs 500 cases each at seeds 1, 37, and 2026, maximum size 10, with
no failures or `gaveUp`. The fork generator uses at most two shared operations
and two operations on each branch, fresh disjoint timestamp ranges, and four
command choices (delete/front insert/end insert/middle insert). The exhaustive
backstop checks all 4,096 six-choice words. The dead-birth-discarding mutation
fails and shrinks once to `[1, 0]` (insert, delete); that trace is retained as
`shrunk_dead_birth_mutation`. The harness detects the lost metadata even before
another mint; the separate literal mint counterexample establishes the
behavioral consequence.

These are 5,596 sampled/bounded checks, not an unbounded merge proof or
external implementation validation. The general repair theorems and the
wrong-history guard controls use only the standard logical axioms. The two
larger full-fork literal tests use `native_decide` and therefore also trust
Lean's compiler; they are not dependencies of the general theorems.
`RefactorLedger` imports the new tests and checks the repair declarations.

## Certified-execution proofs

`FugueMax.invariants_of_mint` in `FugueMaxHonesty.lean` derives `KInv`,
`SLC`, and `RBk` from framework issuance. Strong induction on finite event
sets supplies the invariants on each event's strict causal past. The exact
issuer gives the new record's facts, and immutable birth lookups transport
them into the enclosing causally closed set. This is not an assumption of
`MaxReach` disguised as a history premise.

`FugueMaxReplayProof.lean` proves `join_of_mint`: the actual enriched
three-way merge has a set-relative replay witness. Live membership is
insertion membership minus observed deletions; sorted-coordinate uniqueness
gives list equality, and birth sets merge by union. A delete of sentinel zero
is a no-op; every nonzero delete has its birth in the causal past.

`replay_noninterleaving` combines that result with the generation invariants.
For either kind of `CertifiedExecution`, each existing version has one event
enumeration that replays to its exact enriched state and satisfies all three
`MaxNonInterleavingM` clauses. The caller supplies no separate `MaxReach`
assumption. The conclusion is still implementation replay plus
non-interleaving, not yet ordinary-list sequential refinement.

These general theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. `RefactorLedger` imports and checks them.

## Ordinary-list witness investigation

Candidate claim: construct all births with parents before children and
farther siblings before nearer siblings, then perform deletions. Naive
insert-before/insert-after on a plain identity/value list should produce
the actual visible list. The list has a root sentinel, removed on read;
sentinel deletion is a no-op. No birth records or coordinates are stored in
the abstract state. This is a proof-local construction order, not a second
public `rc` relation.

Falsifier: a generated fork whose abstract splice/filter fold disagrees with
`mView`. `FugueMaxSequentialSPOT.lean` tests 500 cases at each of seeds 1,
37, and 2026, maximum size 10, and all 4,096 six-choice fork words. All
5,596 checks pass with no `gaveUp`. The generator is the same bounded
shared-ancestor/two-branch construction used for the issuer tests. This is
differential evidence against the existing full-history model, not external
semantic validation or a general proof.

The literal sibling control expects `[1,2]`; ordinary timestamp-ascending
insert-after instead yields `[2,1]`. The deleted-child control expects `[1]`.
The two positive controls use `native_decide` for the executable sort; the
negative control is kernel-reduced with `decide`. The general proofs do not
depend on these tests.

`FugueMaxSequential.lean` proves `fmChainBefore_snocR_iff` and
`fmChainBefore_snocL_iff`, the chain-adjacency facts needed to turn sorted
coordinate insertion into an ordinary splice. The right-side hypothesis
uses the tagged FugueMax sibling order, not the sided-RGA freshness rule.
`exists_chain_construction` proves existence of a finite permutation ordered
by increasing depth and the farther-sibling relation. Its transitivity and
irreflexivity are proved; `construction_right` and `construction_left` give
the corresponding adjacency hypotheses for earlier records. The completed
refinement uses this order as described below.

## Completed public certificate

`FugueMaxListRefinement.lean` proves `splice_node` and `births_refine`:
under the construction order, each coordinate insertion agrees with a plain
insert-before/insert-after splice, and the whole insertion fold agrees.
`birth_parents_of_construction` proves that each nonroot parent is already
allocated in that fold. The deletion lemmas preserve this correspondence,
including sentinel no-ops and repeated deletion of the same identity.

`FugueMaxContract.lean` defines the independent `listSpec`. Its state is only
a list of identity/value pairs and a root sentinel, with no coordinates or
birth records. `listLegal` requires distinct positive event timestamps,
prior allocation and no prior deletion of nonroot insertion parents, and
prior allocation of nonzero deletion targets. The latter need not remain
live. `listRel` identifies the projected live implementation list with the
abstract list after removing the sentinel.

`staged_legal` proves legality of the constructed insertion/deletion witness.
`finalNodes_eq_live` proves exact live-list equality with any supported
respecting implementation replay. `verified` packages the resulting public
certificate. `correct` supplies one witness with legality, list refinement,
query agreement, and all three maximal-non-interleaving clauses. The proof
derives the generation invariants from the same `CertifiedExecution`; no
separate `MaxReach` premise is assumed. Both general capstones use only
`propext`, `Classical.choice`, and `Quot.sound`.

The production and state-GC coverage registries contain the exact enriched
package. `public-contracts.json` pins its implementation, issuance, `rc`,
plain-list specification, relation, and full same-witness conclusion.
Gate mutation tests reject replay/non-interleaving alone and list correctness
alone. The SPOTs now call the production `listStep`; literal legality controls
reject a sequential insertion after a deleted anchor and accept duplicate
deletion of a previously allocated identity.

Residual: birth storage is unbounded, no datatype-state collector or independent
FugueMax runtime is certified, and the contract ledger remains pending human
semantic review. The old coordinate-only `FMSig` is not this package.

Validation: `check-mrdt-refactor.sh` passes with 22 exact public contracts,
11 gate tests, 186 runtime tests, and 569 benchmark-schema checks. The runtime
tests are repository regressions, not independent FugueMax conformance tests.
`check-working-papers.sh` rebuilds all three PDFs and checks the paper ledgers.
