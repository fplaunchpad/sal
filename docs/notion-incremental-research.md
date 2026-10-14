# Structured incremental Notion core

Current integration: `paper1` includes this structural result and the subsequent
[compiled executable refinement](notion-executable-refinement.md). The following
measurements describe the earlier JavaScript adapter and structural proof
checkpoint; they are not native-runtime timings or the final combined proof
footprint. The current [paper measurement](../experiments/paper-implementation/README.md)
includes the original bridge and both refinement layers.


Research question: can stable identities, origin trees, interval ownership and
the restricted core slice shape eliminate full transaction replay and make
sequential correctness proofs modular?

The checked result is affirmative for structural reconstruction and proof
reuse. `NotionCoreStructuralMRDT` has exact query correspondence, the actual
five VCs, operational execution transport and the independent RA specification
under the original honest factory/client protocol. This is the typed
create/insert/delete/split core, not production Notion equivalence.

## Representation and design decision

The maintained Lean carrier is a finite set of immutable birth rows, erased
identities, creation links and marker-to-owner cuts. Updates decode one whole
transaction atomically; merges union facts and ignore their ancestor argument.
No transaction archive or query cache is a state field. Late arrivals integrate
by union regardless of source-key position; `late_integrate` records this law.

Queries derive tombstoned rows, traverse origin structure, reconstruct interval
stops from the next physical boundary, select each block's active owner record,
and order blocks by folding source-key-sorted creation links. They do not call
the transaction interpreter. Inactive title instances and deleted anchors are
retained. The Lean query recomputes structure on demand; it does not verify a
maintained JavaScript index or establish a query-time complexity bound.

The direct representation was chosen over the checked replay-cache alternative
because structural union removes dirty-suffix replay, including late lower-key
arrivals. `NotionCoreIncrementalReplay` and `NotionCoreIncrementalMRDT` retain the
correct cache alternative and its prefix-reuse budget as intermediate results.
The cache alone is not the final result.

A preserved counterexample explains why immutable starts/owners matter.
`NotionCoreIncrementalCounterexample.honestly_issuable_splits` constructs two
concurrent splits of `ab` at one. After union, a previously nonempty interval
must become empty. Keeping its old END endpoint retains `b` incorrectly.
`frozen_endpoint_control` rejects that frozen-stop representation, and
`direct_cut_control` checks the corrected answer `a | empty | b`. This is a
candidate-design obstruction, not a bug in the verified core or an impossibility
result against direct merging.

## Checked evidence

| Requirement | Evidence |
| --- | --- |
| Exact immutable row/deletion content | `StructuralFacts.birth_correspondence`, `erased_correspondence`; `StructuralRows.rows_correspondence` |
| Physical ordering, including late arrivals | `StructuralRows.honest_physical` |
| Immutable interval ownership across create/split/erase | `StructuralCuts.honest_records`; `StructuralRender.honest_cells` |
| Block order, including prebootstrap lower-key creates | `StructuralDisplay.honest_display` |
| Active text and empty inactive titles | `StructuralActiveText.blockText_active`; `StructuralRender.blockText_active` |
| Whole-document query correspondence | `StructuralRender.honest_observe` |
| Actual five VCs for the final query/carrier | `StructuralMRDT.fiveVCs` |
| Ordinary steps and canonical recursive merge bases | `StructuralExecution.step`, `stepV`; `StructuralMRDT.operational_reach` |
| Same independent sequential witness for all versions | `StructuralMRDT.versions_witness` |
| Selected RA criterion | `StructuralMRDT.specification_ra` |

Module names in the table abbreviate the `NotionCore` prefix. The final public
endpoints require the original protocol reachability and injective session
assignment. They do not require caller-supplied query answers, replay success,
partition/shape invariants, or archive-image equations. The intermediate
`ClosedQueryAgreement` contract is discharged by `honest_observe` in the final
assembly. The specification is the unchanged `NotionCoreMRDT.spec`, and history
transport preserves the reference's literal witness list.

The final assembly and intermediate/alternative modules jointly built in 3,517
jobs. Printed endpoint axioms are only `propext`, `Classical.choice` and
`Quot.sound`. Independent review checked renderer composition and history/
execution transport. `scripts/check-notion-incremental.sh` reproduces the build
and a smaller hash-pinned executable oracle run (network required).

## Executable evaluation

The standalone JavaScript adapter maintains origin/cut/delete/create indexes.
Its direct updates and merges do not replay transactions; queries traverse
retained structure. It retains the full archive for collision checks and the
existing reference client. That archive is counted in memory proxies.

The original 200 seeded honest workloads yielded 6,800 reference comparisons,
including 2,406 lower-key arrivals, 579 splits and 350 deletes. The creator-fold
supplement checks both display algorithms and increases comparisons to 12,400
on 200 cases. The final independent smaller run passed 1,240 comparisons across
20 cases, including 248 late arrivals and all hand-derived negative controls.

Five-repeat medians at 512 mixed updates were 9,451.7 ms versus 1.148 ms for
receipt integration, 27.153 versus 0.097 ms for full query, and 49.226 versus
0.799 ms for merge (reference versus indexed adapter). Every timed merge adds
an unseen concurrent transaction. The separate display comparison measured
0.1673 ms for creator-fold full query versus 0.0769 ms for tree display on the
512 mixed workload. These runs have different timing samples; they are not
identical benchmark observations to be subtracted from each other.

The reference eagerly reconstructs on updates/nonempty merges and caches the
result for queries. It also rebuilds mappings and checks invariants that the
adapter does not check inside each timed update. Preparation of positional
requests is excluded. These measurements demonstrate benefit on the recorded
workloads, not an asymptotic guarantee or a controlled comparison against an
equally optimized implementation with identical validation overhead. See
`experiments/notion-incremental/README.md`, raw JSONL and summary files for the
reproduction commands and memory methodology.

A separate retained-heap experiment used 12 isolated Node processes, three
repeats per engine/workload, at size 512. Median heap deltas were 545,432 versus
478,496 bytes for insertion and 694,912 versus 712,320 bytes for mixed work
(reference versus indexed adapter). Ranges overlap and the direction changes,
so these measurements do not establish general memory savings. Prepared
workloads are retained outside the measurement interval; engine archives and
representations are included. See `heap-observations.jsonl` and
`heap-summary.json` for raw deltas, ranges and runtime details.

The main Lean renderer uses the checked creator fold. The faster JavaScript
display tree has controls and a checked one-step graph bridge; its full generic
`TraversalFoldLaw` remains an explicitly unproved research proposition.
Creator-fold timing is recorded separately to evaluate the proved design
choice. Neither executable variant has a JavaScript-to-Lean refinement or
extraction theorem.

## Proof-work measurement and boundaries

`proof_metrics.py` records physical/nonblank source lines and syntactic theorem
counts, separating new endpoint dependencies, optional investigations and
reused modules. The final endpoint currently requires 1,933 new structural
lines plus 216 new cut-reconstruction/support lines. The existing reference
protocol's Notion-specific closure is 24,317 lines across 89 modules, reused by
the structural proof. Comments, controls and definitions count as source.

This establishes modest additional source volume through reuse, not a measured
reduction in total proof effort. No controlled independent implementation,
author-time measurement or from-scratch structured proof exists. The modular
boundaries are rows, ownership, display, rendering and generic execution/history
transport; the substantial source-specific invariant proofs remain dependencies.

The original honest factory/client protocol remains the preparation authority.
This work changes receipt integration, merging and observation. Direct local
positional preparation from only structural indexes is not established.
`StructuralIssuanceBoundary.next_counter_not_from_facts` proves a precise reason
to retain allocator metadata: honest erases at counters 3 and 9 can yield equal
semantic facts but next counters 4 and 10. Semantic facts cannot recover the
original allocation state. The executable retains the archive and uses the
reference client; it does not weaken issuance to an unconditional policy.

No paper, public site, GC module or production catalogue entry is changed by
this isolated research branch. The only development task list is
`PRIORITIZED_REMAINING_WORK.md`.
