# Current implementation-table measurement

Measured source: the current working tree based on `2854bec`, including the source undo/redo TreeMove replacement, certified same-record priority queue and structured/executable Notion. `current-counts.json` records this base revision and pins 444 measured Lean source files with verified SHA-256 hashes. All 444 hashes also match the committed source at `3d924a0`; `git_head` records the measurement base, not the later integration commit. The repository gate passed. The appendix and table are published to Overleaf at `97e92d7`, and the datatype Site is published as version 19.

Run from the Sal checkout with its checked current Lean build:

    python3 experiments/paper-implementation/measure.py --repo . --out /tmp/sal-paper-instances

The completed run imported RefactorLedger and applied the existing kernel declaration-dependency audit to 222 explicit implementation, issuance, independent-specification, VC, and end-to-end correctness roots. The 19 existing automation cases use actual CommonVerification.verify applications and input dependencies, rather than entire condition bundles. Set-wins map uses the generic PolicyExpansion.assemble derivation. Other proof routes include named raw five-VC declarations with the common finite-set merge induction, generic policy expansion, and the direct structural Notion assembly. The replacement priority queue consumes its named raw five VCs through the shared metadata Join induction, then uses an execution-scoped independent-history bridge. The table does not assert that every row invokes `CommonVerification.verify`. All audited roots have only the standard Lean axioms propext, Classical.choice, Quot.sound.

Counts are nonblank, noncomment physical lines in unions of complete declaration source ranges, including statements, proof bodies, proof-bearing definitions, finite descriptions, and packaging annotations. They are current dependency-footprint measurements, not handwritten proof-body counts, generated proof sizes, author hours, or historical automation effort. Generated theorem/definition range overlap is assigned to proof/support roles.

The roles are disjoint within each row in this priority: implementation/issuer definitions, independent-specification definitions, actual VC proof/input support, remaining sequential bridge and execution-certificate support. A complete conditions-root declaration is included as VC packaging annotation, while its sequential proof dependencies are charged to the last column. The last column includes reachable-state invariant proofs, representation/reconstruction arguments, client refinements when required by the selected endpoint, and endpoint execution packaging; it must not be labelled simply 'sequential proof body LOC'. Nonempty operation-policy declarations belong to the support closure because they are separate from the raw MRDTSig/issuer roots.

Framework/metatheory/interfaces/general history and policy modules and generic automation are shared. Concrete specialisations (including Automated*, Transfer*, finite input descriptions and the sequence kernels under Instances) are charged to the rows using them. The script contains the explicit classification. Dependencies shared between datatype rows, especially the grow-only store, embedded sequence kernels, Core/RichCore, and the flag dual, appear in multiple rows. Do not add row totals as repository LOC. measurement.json separately gives the deduplicated concrete and shared dependency unions and all source-line membership sets.

The three grow-only set carriers (AddStore, FinsetStore, pointwise-Boolean FlatGrowOnly) are combined by physical-line union into one paper row. Sided Peritext is counted once through its rendered interface, with both core and rendered dependency closures deduplicated before assigning columns. Rows progress by conceptual complexity, with related variants adjacent; this is not a ranking by proof LOC. There are 26 selected checked configurations and 24 resulting paper rows. This is not a count of distinct abstract datatypes. The historical unanchored Queue is excluded; anchored Queue is included. Ordinary OR-set, published Balegas, both corrected Neem flags, Neem remove-wins set, set-wins map, optional register, the same-record priority-queue adaptation, and the typed Notion core protocol are included. Notion is one combined structural/native case: its distinguished typed ledgers retain the original protocol, structural RA and executable refinement. It is not a VerifiedMRDT package, production Notion proof or whole-program JavaScript extraction. Production.registry separately has 18 exact VerifiedMRDT packages and contains the historical Queue; it is not the basis of this table's N. Historical 23-case automation JSON includes retired bounded-counter/counter duplicates and is not used.

I denotes a nontrivial datatype-specific local issuance guard. E denotes an execution-scoped sequential/history bridge using reachable-version evidence to select/admit an explaining history; it does not mean an extra invariant supplied by the caller. Every listed case provides ordinary and recursive-virtual execution correctness. Nontrivial rc here denotes a nonempty application OperationPolicy.before, not specification conflict or invariant-scoped event ordering. Seven rows have nontrivial rc: the two OR-sets, two flags, remove-wins set, set-wins map, and optional register. The replacement priority queue has I=yes, E=yes and empty rc: its guards apply to actual issuance, and its scoped bridge preserves independent specification conflicts despite commuting prepared effects. An empty application policy does not make sequence-event order trivial.

Evidence for E=no: SimpleEventPorts.*.simulation, ORSet.EventSpec.foldHistorySound, EfficientORSet.EventSpec.foldHistorySound, NeemFlagEvent.historySound, RemoveWinsSet.historySound, SetWinsMap.historySound use universal fold/simulation bridges. Evidence for E=yes: LWW.GuardedPort.history; RGA.ConcretePort.history; Instances.TreeMove.Incremental.history; GuardedPorts.Sheet.history; CertifiedMVRHistory.replay_history; CertifiedRGAInvariantHistory.canonical_valid_history; CertifiedSidedInvariantHistory.canonical_valid_history; CertifiedRGACoreCertificate.history; CertifiedRGARichCertificate.history; AnchoredQueue.History.schedule_publicWitness; FugueMaxNaturalCertificate.version_witness; BalegasBoundedCounterEvent.certifiedV; NotionCoreStructuralMRDT.versions_witness (reusing NotionCoreProtocol.versions_witness through proved query agreement); OptionalRegister.history; PriorityQueueSameRecord.historyAdequacy.

The three new Neem sources expose no query. Sal selects ordinary membership for remove-wins set, accumulating multimap lookup for set-wins map, and the greatest-timestamp active payload for optional register. Set retains older values at the same key, so the map specification accumulates values. Remove-wins set reserves timestamp zero for its initial removal tags; optional register requires positive timestamps to preserve the source's inactive/zero-payload refinement. Both use explicit positive-time issuance. OptionalRegister.sourceWellFormed derives the exact source refinement for actual stored versions, including recursive executions. The new measured columns (Def., Spec, VC support, Bridge/execution support) are respectively 28/18/434/168, 25/12/19/136, and 61/9/717/880.

Checked-in artifacts: `table.md` (paper columns and certification flags), `current-counts.json` (roots, counts, source hashes, and compressed line ranges), `implementation_table.tex`, `metatheory-counts.json`, and both counting scripts. A fresh instance run produces `roots.json`, full `measurement.json`, `kernel.log`, and `vc-evidence.log` in the selected output directory.

The checked-in `current-counts.json` compresses the same physical line sets into inclusive source ranges. Full raw dependency logs are regenerated by the command above, rather than checked in. Generic metatheory counts are independent of datatype support counts; reproduce with:

```sh
python3 experiments/paper-implementation/measure_metatheory.py --repo . --out /tmp/sal-paper-metatheory
```

See [the manuscript evidence note](../../docs/paper-implementation-evidence.md) for scope and source attribution. These are current footprint measurements, separate from historical author-effort reductions in vc-automation.

## Structured and executable Notion accounting

The independent retained-slot specification and original history witness are
reused. Structural renderer/transport and indexed-runtime refinement proofs are
additional support: they prove the new implementation returns the same answer
on the unchanged honest protocol. The Notion row counts both the reference and
new implementation dependencies, including the executable typed wire/request
boundary and the concrete certificate wrappers. It excludes the benchmark
harness, IO loop/timers and optional unproved tree-display optimization.
The compiled core has operation and query refinement theorems; the RA endpoint
belongs to the structural MRDT. Compiler/runtime and JSON/source conversion
remain explicit execution boundaries.

Both Notion ledger modules are now classified as concrete datatype support.
Previously the directory-based shared-metatheory rule omitted the original
concrete wrapper. Changes to this row therefore include that correction as
well as the new implementation and refinement proofs. Source line roles remain
disjoint: a larger definition footprint can move helper definitions previously
counted under bridge support into the MRDT column.

Current Notion columns are **729 / 112 / 73 / 18,082** (MRDT / Spec / VCs /
Bridge). The previous 316 / 112 / 153 / 15,288 row is not a like-for-like
proof-reduction baseline: 103 old VC lines now belong to Bridge, 56 old Bridge
definition lines now belong to MRDT, and the structural VCs add 23 lines. No
previously counted concrete lines were dropped. The combined concrete union
adds 3,127 lines, including the newly charged 79-line original ledger wrapper
and 64-line new wrapper. The unchanged independent specification still costs
112 lines. The original finite-store VC route is measured from actual verifier
application evidence; the structural carrier directly uses `TransferSimple.assemble`,
so its complete VC dependency closure is charged and recorded in
`direct_vc_dependency_roots`.

## Full priority queue and consolidated sided Peritext

The single `add-wins-priority-queue` row measures
`Instances.PriorityQueueSameRecord.D` and its derived local `rmvMax` client.
This intentional adaptation of Algorithm 2 selects the innate priority and
acquired increments from the same latest surviving Add. Inc attaches to observed
Add identities; observed Remove disables those records. Reinsertion resets
priority. Preparation retains the source Add-absent and Inc/Remove-present
guards. The independent finite priority-map machine uses total Add/overwrite,
additive Inc with absent no-op, and Remove with absent no-op; it stores no Add or
increment metadata. Empty, membership, priority and deterministic maximum queries
are certified for ordinary and recursive executions. Maximum ties select the
greatest element ID. Derived extraction returns the locally observed pair and
issues its observed Remove; it makes no atomic global-extraction claim.

The replacement roots are under `Sal.MRDTs`:

- Implementation: `Instances.PriorityQueueSameRecord.D`, `generation`, `rmvMax`.
- Specification: `Paper1.PriorityQueueSameRecord.spec`, `seqRmvMax`.
- VCs: `Paper1.PriorityQueueSameRecord.fiveVC`.
- Bridge: `Paper1.PriorityQueueSameRecord.executions`, `executionsV`,
  `rmvMax_refines`, and `Instances.PriorityQueueSameRecord.getMax_sound`,
  `getMax_none_iff`, `prepared_remove_effect`,
  `prepared_remove_issued`.

Its Def./Spec/VC-support/Bridge-support counts are **98 / 28 / 99 / 1,285**.
The previous **62 / 31 / 433 / 370** row measured the retired retained-increment
variant and is not a proof-reduction baseline. The replacement audit passes:
3,424 targeted Lean
jobs, 562 declarations using only standard logical axioms, and actual
ordinary/recursive endpoint ancestry through the named five VCs, shared finite
Join induction, exact issuer provenance, ordinary present/absent replay,
identified increment aggregation and full-query composition. Seven PASS+FAIL
blocks cover the repair, maximum and client behavior. The published MCW source
model and its checked ordinary-specification obstruction remain separate.

Sided Peritext's core and rendered interfaces contribute to one `sided-peritext-rich-core` row: **208 / 67 / 149 / 3,072**. Its roots include both `SidedPeritext.Core`/`generation` and `RichCore`/`richGeneration`, both `CertifiedRGACoreCertificate.language` and `CertifiedRGARichCertificate.language`, both core/rich merge-VC roots and both history/ordinary/recursive execution endpoints. Per-role declaration dependencies are united before disjoint column assignment. There is no additional core row.

This completed run audits **222 roots / 444 source hashes**, reports **26 configuration rows / 24 paper rows**, and has deduplicated unions of **47,361 concrete** and **8,477 shared** source lines. These unions are separate from the retained metatheory-only census. Fresh measurement logs were generated in `/private/tmp/sal-pq-current-counts`; their compact roots/hashes/ranges are checked in here.

## Incremental tree move

The `tree-move` row now measures `TreeMove.Incremental.D`, its source client guard,
and its independent in-place tree language. The implementation maintains a tree
and descending undo log, implements late-delivery undo/insert/redo, and exchanges
states by delivering the other log. The source reserves no special children;
our editor wrapper reserves root/trash and requires fresh event identifiers.
It permits deletion to trash, hidden-node restoration and absent destinations.

Its Def./Spec/VC-support/Bridge-support counts are **85 / 20 / 178 / 256**.
The previous finite-event carrier counted 56 / 15 / 65 / 94. The added proof work
establishes exact log/tree refinement and its independent history theorem.
The five VCs use the shared verification interface; ordinary and recursive
execution results consume that proof and the actual undo/redo refinement.
Fifteen positive/negative test blocks pass, and the parent rebuilt them
independently. The representation uses noncomputable trees and ancestry;
these are mathematical implementation and proof counts, not runtime measurements.

The public registry retains 18 packages, with the incremental carrier replacing
the old tree entry. Its older GC proof remains separate; the new carrier's GC
classification is staged. No GC result is used in this paper's table.

TreeMove integration validation passed: **3,870 Lean build jobs**, **18 exact public
contracts**, **13 certificate controls**, **187 runtime tests** and **569 benchmark
records**. All audited theorem roots use only standard Lean logical axioms.

The same-record priority-queue integration gate passed **3,875 Lean build jobs**,
**18 exact public contracts**, **13 certificate controls**, **187 runtime tests**
and **569 benchmark records**. The full log is
`/private/tmp/sal-pq-full-gate.log`. Measurement and checked integration are
complete. Published: Sal `3d924a0`, Overleaf `97e92d7`, and
[datatype Site version 19](https://sal-datatype-reference.fizzyearth10.chatgpt.site/#priority-queue-same-record).
The rendered main text remains 23 pages; references start on page 24.
