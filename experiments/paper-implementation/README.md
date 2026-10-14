# Current implementation-table measurement

Measured source: the current working tree based on `b45a145d5f316241bb6536fa495ef35d9f48df74`, including the full-query priority-queue port and structured/executable Notion. `current-counts.json` records this base revision and pins 439 measured Lean source files with SHA-256 hashes verified against the working tree. The hashes identify the measured source, including uncommitted port files; `git_head` alone is not a claim that those files are already committed.

Run from the Sal checkout with its checked current Lean build:

    python3 experiments/paper-implementation/measure.py --repo . --out /tmp/sal-paper-instances

The script imports RefactorLedger and applies the existing kernel declaration-dependency audit to 223 explicit implementation, issuance, independent-specification, VC, and end-to-end correctness roots. The 19 existing automation cases use actual CommonVerification.verify applications and input dependencies, rather than entire condition bundles. Set-wins map uses the generic PolicyExpansion.assemble derivation. Other proof routes include named raw five-VC declarations with the common finite-set merge induction, generic policy expansion, and the direct structural Notion assembly. The full priority-queue query interface transports its existing raw five VCs through `Automation.QueryLift.transport`. The table does not assert that every row invokes `CommonVerification.verify`. All audited roots have only the standard Lean axioms propext, Classical.choice, Quot.sound.

Counts are nonblank, noncomment physical lines in unions of complete declaration source ranges, including statements, proof bodies, proof-bearing definitions, finite descriptions, and packaging annotations. They are current dependency-footprint measurements, not handwritten proof-body counts, generated proof sizes, author hours, or historical automation effort. Generated theorem/definition range overlap is assigned to proof/support roles.

The roles are disjoint within each row in this priority: implementation/issuer definitions, independent-specification definitions, actual VC proof/input support, remaining sequential bridge and execution-certificate support. A complete conditions-root declaration is included as VC packaging annotation, while its sequential proof dependencies are charged to the last column. The last column includes reachable-state invariant proofs, representation/reconstruction arguments, client refinements when required by the selected endpoint, and endpoint execution packaging; it must not be labelled simply 'sequential proof body LOC'. Nonempty operation-policy declarations belong to the support closure because they are separate from the raw MRDTSig/issuer roots.

Framework/metatheory/interfaces/general history and policy modules and generic automation are shared. Concrete specialisations (including Automated*, Transfer*, finite input descriptions and the sequence kernels under Instances) are charged to the rows using them. The script contains the explicit classification. Dependencies shared between datatype rows, especially the grow-only store, embedded sequence kernels, Core/RichCore, and the flag dual, appear in multiple rows. Do not add row totals as repository LOC. measurement.json separately gives the deduplicated concrete and shared dependency unions and all source-line membership sets.

The three grow-only set carriers (AddStore, FinsetStore, pointwise-Boolean FlatGrowOnly) are combined by physical-line union into one paper row. Sided Peritext is counted once through its rendered interface, with both core and rendered dependency closures deduplicated before assigning columns. Rows progress by conceptual complexity, with related variants adjacent; this is not a ranking by proof LOC. There are 26 selected checked configurations and 24 resulting paper rows. This is not a count of distinct abstract datatypes. The historical unanchored Queue is excluded; anchored Queue is included. Ordinary OR-set, published Balegas, both corrected Neem flags, Neem remove-wins set, set-wins map, optional register, the Sal retained-increment priority queue, and the typed Notion core protocol are included. Notion is one combined structural/native case: its distinguished typed ledgers retain the original protocol, structural RA and executable refinement. It is not a VerifiedMRDT package, production Notion proof or whole-program JavaScript extraction. Production.registry separately has 18 exact VerifiedMRDT packages and contains the historical Queue; it is not the basis of this table's N. Historical 23-case automation JSON includes retired bounded-counter/counter duplicates and is not used.

I denotes a nontrivial datatype-specific local issuance guard. E denotes an execution-scoped sequential/history bridge using reachable-version evidence to select/admit an explaining history; it does not mean an extra invariant supplied by the caller. Every listed case provides ordinary and recursive-virtual execution correctness. Nontrivial rc here denotes a nonempty application OperationPolicy.before, not specification conflict or invariant-scoped event ordering. Eight rows have nontrivial rc: the two OR-sets, two flags, remove-wins set, set-wins map, optional register, and priority queue. An empty application policy does not make sequence-event order trivial.

Evidence for E=no: SimpleEventPorts.*.simulation, ORSet.EventSpec.foldHistorySound, EfficientORSet.EventSpec.foldHistorySound, NeemFlagEvent.historySound, RemoveWinsSet.historySound, SetWinsMap.historySound, and AddWinsPriorityQueue.Full.historySound use universal fold/simulation bridges. Evidence for E=yes: LWW.GuardedPort.history; RGA.ConcretePort.history; GuardedPorts.Tree/Sheet.history; CertifiedMVRHistory.replay_history; CertifiedRGAInvariantHistory.canonical_valid_history; CertifiedSidedInvariantHistory.canonical_valid_history; CertifiedRGACoreCertificate.history; CertifiedRGARichCertificate.history; AnchoredQueue.History.schedule_publicWitness; FugueMaxNaturalCertificate.version_witness; BalegasBoundedCounterEvent.certifiedV; NotionCoreStructuralMRDT.versions_witness (reusing NotionCoreProtocol.versions_witness through proved query agreement); OptionalRegister.history.

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

The single `add-wins-priority-queue` row measures `Instances.AddWinsPriorityQueue.FullD` and the derived local `rmvMax` client, not a second per-element implementation. The independent finite-map model supplies empty, membership, priority and deterministic maximum queries. Maximum ties select the greatest element ID. Maximum soundness/completeness and the returned-pair/local-effect client refinement are proved; two replicas may select the same pair concurrently. This is the Sal retained-signed-increment variant, not the source paper's per-record Most-Change-Win algorithm or atomic global extraction.

The exact selected roots are under `Sal.MRDTs`:

- Implementation: `Instances.AddWinsPriorityQueue.FullD`, `Paper1.AddWinsPriorityQueue.Full.generation`, `Instances.AddWinsPriorityQueue.rmvMax`.
- Specification: `Paper1.AddWinsPriorityQueue.Full.spec`, `Paper1.AddWinsPriorityQueue.Full.seqRmvMax`.
- VCs: `Paper1.AddWinsPriorityQueue.Full.fiveVC`.
- Bridge: `Paper1.AddWinsPriorityQueue.Full.executions`, `executionsV`, `rmvMax_refines`, `prepared_remove_effect`, plus `Instances.AddWinsPriorityQueue.getMax_sound` and `getMax_none_iff`.

Its Def./Spec/VC-support/Bridge-support counts are **62 / 31 / 433 / 370**. The audit checks full ordinary/recursive certificate ancestry through the source five VCs, generic merge induction, query-only transport and independent full-query bridge. Twenty-three PASS+FAIL controls cover priority and full-interface/client behavior.

Sided Peritext's core and rendered interfaces contribute to one `sided-peritext-rich-core` row: **208 / 67 / 149 / 3,072**. Its roots include both `SidedPeritext.Core`/`generation` and `RichCore`/`richGeneration`, both `CertifiedRGACoreCertificate.language` and `CertifiedRGARichCertificate.language`, both core/rich merge-VC roots and both history/ordinary/recursive execution endpoints. Per-role declaration dependencies are united before disjoint column assignment. There is no additional core row.

This refresh audits **223 roots / 439 source hashes**, reports **26 configuration rows / 24 paper rows**, and has deduplicated unions of **46,417 concrete** and **8,379 shared** source lines. These unions are separate from the retained metatheory-only census. The full gate passed **3,865 Lean jobs**, **13 certificate controls**, **187 runtime tests**, and **569 benchmark records**; the 18-package uniform registry is unchanged. Fresh raw measurement/logs were generated in `/private/tmp/sal-priority-full-counts`; their compact roots/hashes/ranges are checked in here.
