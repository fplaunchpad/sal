# Audit of the paper's correctness argument

Baseline: Overleaf `0450d4875b8155c8f98521f68a4dac50b6eb85c4`, fetched again
on 8 October 2026; Sal `paper1` after `935dfa9`, with the explicit theorem
connections added in this audit. The live manuscript has not been edited.
The accompanying [manuscript patch](paper1-manuscript-reconciliation.patch)
contains the proposed replacements against that exact Overleaf revision.

## Result

Both case studies use the five-VC merge proof. The separate sequential bridge
does not replace that proof: it establishes correctness against an independent
specification after merge correctness has been proved.

The exact paper OR-set instantiates the unrestricted result. Embedded RGA
instantiates a certified extension with a separately constructed sequential
history. Its proof does **not** establish uniqueness of every linear extension
of the public invariant order. This broader claim is unproved by this proof
chain, rather than refuted by the audit.

The manuscript currently includes the operational semantics, RA definition,
merge argument and OR-set sequential simulation. `rga.tex` contains only an
unused “Verified Tombstoned RGA” heading. The proposed section explicitly
describes **Embedded RGA**, the live-record implementation audited here; it
does not relabel the separate tombstoned implementation. Introduction,
implementation, evaluation and conclusion are currently headings only.

## The two theorem chains

| | Unrestricted exact OR-set | Issuance-certified Embedded RGA |
|---|---|---|
| Implementation | Timestamp-tag set; concrete state equality | Sorted live records with immutable coordinates; concrete state equality |
| Execution hypotheses | Raw ordinary or recursive-virtual reachability in the checked store | Original `generation Γ` certified ordinary or recursive-virtual execution; ordered prefix code; decidable equality and an inhabited value type |
| Merge theorem | Five concrete VCs → weakly closed canonical Join | Five concrete VCs + representation uniqueness, finite/initial representation and peel supply → represented Join; adapter to full-causal-closure internal canonical Join |
| Replay uniqueness | Every supported raw-public-order enumeration of the same event set has the same fold under global guarded laws | Legal causal implementation replays at represented prefixes; not every public-order-only word |
| Sequential labels | Payload `add/remove`; full-event lifting also available | Original timestamp, replica and insertion/deletion payload |
| Specification | Independent ordinary finite set | Independent tagged list with separately defined history legality |
| Final bridge | Soundness of every sequential event list plus concrete/specification commutation compatibility | An insertion-first word with exact stored-state reconstruction, both required orders and independent admission |
| Public conclusion | Specification-visible payload RA at every raw reachable configuration | Invariant-order, specification-visible full-event RA throughout certified execution |

### Exact OR-set: every premise is discharged

`ORSet.RawExecution.vcJoinAt` derives `JoinAt` through
`ConcreteMRDT.Raw.join_at_sizes` and `ORSet.GuardedRawVC.mergeVCs`.
The exact representation is canonical replay plus support. Its initial,
finite, uniqueness and reconstruction obligations are proved in
`GuardedRawORSetReplay`; the client assumes no Join theorem.

`ORSet.simulation` proves the total sequential premise using the ordinary
element view. `ORSet.specificationConflictsCovered` separately proves the
specification-order obligation. The new
[`ORSet.PaperContract.specificationRawRA` and `specificationRawRAV`](../Sal/MRDTs/Paper1/ORSetPaperContract.lean)
connect these facts to the **new VC-derived Join**, at the payload alphabet
used in the paper, for raw ordinary and virtual reachability respectively.
These statements have no external canonicality, history or client-issuance
premise. Certified variants are also checked.

The efficient OR-set has the same equation shapes and the same ordinary-set
sequential behavior, but its merge proof retains exact live-record
representation, causal closure and increasing causal timestamps. Its theorem
must be presented as an instance of the represented extension, not silently
identified with the exact set's weak-closure Join contract.

### Embedded RGA: every premise is discharged

`CertifiedRGAVC.Embedded.representationJoin` instantiates the concrete
induction using the original issuer's evidence and a representation by causal
folds. Its metadata relation retains all visibility. The two representation ↔
internal-canonical adapters in `CertifiedRGAExecution.Embedded` discharge
`CertifiedClosedExecution.ClosedJoinAt`; generic certified execution induction
then supplies every stored representation. The virtual-base theorem covers
recursive scratch merges as well as allocated versions.

`CertifiedRGAInvariant.closed` establishes the domain's initial state and
closure under every supported original event and merge. The domain is not a
test that the two operations can be freshly issued together. Replay does not
rerun issuance at a permuted state.

`CertifiedRGAInvariantHistory.canonical_valid_history` constructs one
insertion-first word and proves enumeration, invariant-order preservation,
exact concrete fold equality, specification visibility and admission for it.
The word is fixed independently of the query. The final
[`CertifiedRGAInvariantCertificate.versions`](../Sal/MRDTs/Paper1/CertifiedRGAInvariantCertificate.lean)
now invokes the named generic
`PaperPresentation.invariant_versions_of_exact_histories`.
This lift requires the selected fold to equal the stored state; it has no
arbitrary-list soundness or universal public-order uniqueness premise.
`correct`, `executions` and `executionsV` close the original certified case.

The implementation replay result remains separate:
`implementation_replay_equal` requires both enumerations to respect full
visibility. An insertion-first sequential word may move causal deletions, so
its exact reconstruction is justified by a datatype fold lemma, not by
applying that causal replay theorem outside its domain.

## Claim ledger and manuscript replacements

All machine-checked entries below refer to the mathematical store and trusted
datatype/specification definitions. They are not claims about a deployed
network implementation or every RGA design.

| Manuscript location | Finding / evidence class | Authoritative evidence | Correction in the patch |
|---|---|---|---|
| `opsem.tex`, configuration, Apply/Fork and LCA lemma | Model mismatch | `Configuration`, `Step`, `IsGCA`, `gca_events_of_storeInv` | Strict visibility, fresh causal-monotone timestamps, ranked fresh child on fork, GCA domination, and separately defined recursive virtual bases |
| `ralin.tex`, replay laws | Event/payload scope mismatch | `GuardedReplay.Laws` | User supplies payload policy; laws quantify over full events with the exact timestamp/replica guards; absorber uses actual noncommutation |
| `ralin.tex`, specification and projection | Overclaim of deterministic final state and irrelevant metadata | `HistoryMachine.toSpec`, `HistorySpec.withInputs`, `InvariantOrder.VersionsRA` | General admission is existential; choose a projection explicitly; RGA keeps original inputs |
| `ralin.tex`, RA definition; `seq_spec.tex`, broken set | Literal criterion does not reject chronological no-op removal: machine-checked separation | `CriterionCounterexample.mutant_rawRA`, `criteria_differ_on_reachable_mutation` | Add specification-conflicting visibility to the same witness; distinguish the old literal criterion |
| `ralin.tex`, determinacy/canonical states | Quantifier mismatch if used for certified replay | `ConcreteReplay.canonical_exists/canonical_unique`; `InvariantReplay.convergence_on` | Finite supported strict context for the global theorem; legal causal replays for the scoped theorem; do not interchange them |
| `proof_strategy.tex`, five VCs and Join | Missing reconstruction premises in a general represented extension | `ConcreteMRDT.Raw.MergeVCs`, `ReplaySupply`, `join_at_sizes` | Explicit representation, uniqueness, finiteness, jointly maximal peel and reconstructed states; strict smaller-union recursion |
| `proof_strategy.tex`, exact/efficient case distinction | Distinct proved closure contracts | `ORSet.RawExecution.vcJoinAt`; `EfficientORSet.GuardedRawVC.representationJoin` | Exact weak-closure specialization versus efficient causal/metadata representation |
| `proof_strategy.tex`, execution theorem | Internal witness existence is not public-order uniqueness | `CertifiedClosedExecution.canonicalConfig_of_execution` | State the internal-order Join contract and adapters; leave public order and independent history to the final bridge |
| `seq_spec.tex`, lifting and α simulation | Missing totality/determinism and stronger-criterion order premise | `SequentialSimulation.sound`, `CommutationBridge`, `PaperPresentation` | Explicit total deterministic sufficient method; compatibility for the same domain/order; exact chosen-history certified alternative |
| `rga.tex` / `main.tex` | Missing case study; heading names a different datatype | `CertifiedRGAInvariantCertificate` and instance definitions | Include the new Embedded-RGA section with its original signature, issuer, independent language, invariant and exact history argument |
| `motivation.tex`, efficient-set word and global-order explanation | Displayed update-only word does not witness rejection; incomplete sentence | The manuscript's displayed transitions; checked `ORSetExecution` histories | Include the distinguishing readIds result and singleton removal set; distinguish per-version histories from a single global history |

The patch uses the strengthened criterion as the primary definition, retains
the literal criterion as a comparison, and makes the commutation domain and
label projection explicit. These are substantive manuscript changes, not just
renamings of Lean definitions. No assertion is made that invariant-order RGA
already satisfies the old raw-order criterion: the checked comparison proves
otherwise on an actual certified execution.

## Validation and scope

The theorem ledger checks standard axioms and traverses proof dependencies.
It requires the new raw ordinary/virtual payload OR-set results to use the
concrete VC induction and actual OR-set VC bundle, and requires Embedded-RGA
correctness to use both its history construction and the named exact-history
lift. Existing raw-versus-invariant and birth/delete controls are retained.

Validation on 8 October 2026: `scripts/check-paper1.sh` and
`scripts/check-mrdt-refactor.sh` both exited successfully, including all 187
runtime tests and validation of 569 benchmark records. The patch passes
`git apply --check` against `0450d48`; applying it reproduces the reviewed
proposal sources. Tectonic compiles those sources to 25 pages, all visually
reviewed, with no unresolved-reference or overfull-box diagnostics.

The accompanying patch is a proposed mathematical revision for author review.
Its new RGA section is an added case study; empty evaluation/implementation
sections and bibliography development remain manuscript work outside this
correctness-chain audit. Broader public-order uniqueness for Embedded RGA is
not needed for the stated theorem and remains a separate research question.
