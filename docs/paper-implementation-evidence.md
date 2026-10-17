# Implementation section: scope and evidence

Manuscript checkpoint: Overleaf `f627efa`, including the datatype appendix and priority queue; the collaborator’s abstract update `3eb1248` is preserved. Current implementation measurement: the working source based on `b45a145d5f316241bb6536fa495ef35d9f48df74` (14 October 2026), including the full-query priority queue and structured/executable Notion. The measurement pins 439 working-source files by SHA-256; its base revision does not assert that uncommitted port files already occur in that commit.
This is evidence for the manuscript, not a development task list.

## Section plan

Use one **Implementation and Case Studies** section. Remove the empty Evaluation
input. Allocate roughly 2–3 pages: checked metatheory and its proof size;
a datatype/proof-size table; a short automation paragraph; and the Notion core
case study and three reproduced demo failures. Keep GC entirely outside this paper.

The main narrative should distinguish convergence/state reconstruction from the
independent sequential-history bridge. Counts measure source code, not person-hours
or the fraction of proofs discovered automatically. No new proof-automation or
performance campaign is needed for this section.

## Claims and scope

- Mechanized sufficient-condition argument: the five merge VCs imply the join
  property under the explicit representation/replay/closure premises; execution
  induction establishes stored-state reconstruction; an independent history
  bridge proves the selected RA criterion. The certified route retains issuance
  and execution evidence. The exact generic roots and proof-line census accompany
  this note.
- The current paper's short join statement does not enumerate all of these
  premises. In particular, metadata dependency closure can retain commuting
  predecessors, and representation uniqueness and replay supply must be justified.
  The implementation paragraph states these premises; the formal sections must
  preserve their scope when reconciled. This section is not evidence that every
  current manuscript statement is a literal transcription of Lean.
- Distinguish application-level `rc` from the resulting event order and
  specification-conflict visibility. Empty `rc` does not mean all edits may be
  replayed in arbitrary order.
- Count checked configurations rather than claiming every row is a different
  abstract datatype. Consolidate the three grow-only-set carrier representations;
  keep the two OR-set implementations and named sequence/rich-text representations
  visible. The paper-facing catalogue now contains 26 checked configurations,
  consolidated into 24 rows: three grow-only representations share a row, sided Peritext has one rendered-interface row, and the retained-increment priority queue is included. The 18-package registry and existing 19-case
  automation selection are separate counts.
- Do not claim all complex datatypes were previously unverified. Prior work
  includes convergence proofs (Peritext) and machine verification (TreeMove).
  The supported claim is verification in this framework against independent
  sequential histories, with the stated source adaptations.

The three added Neem cases preserve their concrete operation and merge equations,
with explicit query choices because the sources provide no query. Remove-wins set
uses ordinary membership, generalizes the source's two elements to a finite
universe, and reserves timestamp zero for genesis through positive-time issuance.
Set-wins map uses accumulating multimap lookup: Set retains older values at the
same key. Its natural-number timestamp carrier extends the source's positive
carrier and needs no issuance guard. Optional register retains the source's
finite map, counter/flag arithmetic, and averaging branch; its selected read is
the greatest-timestamp active payload. Positive issuance and the actual
`OptionalRegister.sourceWellFormed` theorem recover the source refinement for
every stored version, including recursive executions. Remove-wins set and
set-wins map have universal history bridges (E=no); optional register has an
execution-scoped bridge to an independent scalar optional-register machine
(E=yes). All three have nontrivial application `rc` and ordinary/recursive
execution certificates derived through the five merge VCs.

## Notion evidence

The pinned public JavaScript demo is an executable oracle, not a verified
implementation extracted from Lean. The typed create/insert/delete/split core
has an end-to-end protocol theorem:

- `Sal.MRDTs.Instances.NotionCoreProtocol.versions_witness` covers every stored version.
- `Sal.MRDTs.Instances.NotionCoreProtocol.specification_ra` specializes the result to heads.
- `NotionCoreMRDT.fiveVCs` reuses `NotionTransactionSet.fiveVCs` with the actual document query.
- `NotionCoreMRDTClient.insert_effect`, `split_effect`, and `erase_effect` connect
  real prepared local requests to their positional effects.
- `Sal/MRDTs/Metatheory/NotionCoreLedger.lean` retains exact theorem types and an
  explicit initialization witness, separately from the uniform package registry.

References: `docs/notion-integration.md`, `docs/notion-core-correspondence.md`,
`docs/notion-bugs.md`, `experiments/notion-oracle/sources.json`,
`regressions.mjs`, and `regression-observations.jsonl`.

There are three confirmed honest-client bugs, all in the broader demo involving
merge-block/formatting: selected characters not bolded; an unselected character
in another block bolded; splitting at zero moves only part of the displayed
suffix. The Lean counterexamples check the relevant contract mismatch or
restricted interval-rule model. They do not mechanize every JavaScript setup
step. Source extraction and production Notion correspondence are not proved.
The old final paragraph in `docs/notion-bugs.md` saying the core proof is
incomplete is stale; the current protocol ledger and integration handoff supersede it.

## Appendix recommendation

Do not paste the entire live Site into the submission. It includes detailed
implementation machinery and would obscure the main result. Preserve a static,
versioned supplementary datatype reference, with definitions, operation signatures,
issuance guards, source citations, and exact theorem links. If space permits,
include a compact specification appendix for the difficult cases (FugueMax,
bounded counter, Peritext, and Notion), plus one complete Notion bug trace.
The main paper should be understandable without visiting the Site. Resolve the
venue's appendix/page-budget rules before including any appendix in the submission.

## Current measurements and source audit

[Reproducible measurement bundle](../experiments/paper-implementation/README.md), [table](../experiments/paper-implementation/table.md), [generic theorem audit](../experiments/paper-implementation/metatheory-audit.md), and [datatype citation/source audit](../experiments/paper-implementation/source-audit.md).

Validation checked all **439** recorded working-source hashes, all **24** paper-row column partitions and their line totals. The instance audit resolves **223** distinct roots and permits only `propext`, `Classical.choice` and `Quot.sound`. It reports **26 configuration rows / 24 paper rows**, with **eight** nontrivial application-rc rows. The deduplicated dependency unions are **46,417 concrete / 8,379 shared LOC**. The retained metatheory-only census is separately **4,020 lines**, with **1,688 shared automation theorem lines**; these are not the same dependency-union metric.

The full integration gate passed **3,865 Lean jobs**, **13 certificate controls**, **187 runtime tests** and **569 benchmark records**. The uniform public gate remains at 18 exact packages. The priority-queue audit checks 459 declarations and the full ordinary/recursive endpoint ancestry. The earlier Notion failure-trace/native-oracle figures are recorded evidence; this measurement refresh did not rerun those discovery campaigns. Recorded Site version 17 predates this full-query refresh and is not evidence of current Site synchronization.

The retained Neem Def./Spec/VC-support/Bridge-support footprints are **28/18/434/168** (remove-wins set), **25/12/19/136** (set-wins map) and **61/9/717/880** (optional register). The full Sal priority queue is **62/31/433/370**. The single sided Peritext row unions core/rendered interfaces and is **208/67/149/3,072**. The measurement retains actual `CommonVerification.verify` evidence for 19 selected automation cases, generic policy expansion for set-wins map, named raw five-VC routes and the direct structural Notion assembly. It does not claim that every row uses the same verifier application. Counts describe dependency source ranges, not handwritten proof-body size or author effort.

The priority-queue implementation roots are `Instances.AddWinsPriorityQueue.FullD`, `Paper1.AddWinsPriorityQueue.Full.generation` and `Instances.AddWinsPriorityQueue.rmvMax`. Specification roots are full `spec` and `seqRmvMax`; the VC root is full `fiveVC`. Full `executions`/`executionsV`, `rmvMax_refines`, `prepared_remove_effect`, and implementation `getMax_sound`/`getMax_none_iff` supply bridge and intent support. The independent finite priority map certifies empty, membership, priority and actual maximum queries, with greatest-element-ID ties. Derived maximum removal returns the local observed pair and removes its identity; it preserves increments and carries no atomic global-extraction guarantee. The full source paper's per-record Most-Change-Win algorithm remains outside this flattened Sal variant.

## Recorded manuscript preview (`f5aad25`)

At the recorded manuscript checkpoint, the local Overleaf checkout contains `implementation.tex` and
`implementation_table.tex`, with bibliography additions. `main.tex` includes
that section, removes the empty Evaluation input, and loads `array` for the
table. No other manuscript section was edited. The pre-existing local
`main.pdf` was preserved.

[Compiled review PDF](paper-implementation-preview.pdf): the recorded draft has
27 pages total; the implementation table is on page 22 and references begin
on page 25, after the end of the body. The body therefore extends onto page 25
and exceeds the stated 23-page budget. This includes the author's newly supplied
Related Work and Conclusion; a separate empty Conclusion input also remains.
The preview matches Overleaf commit `f5aad25`. The integration did not trim
unrelated manuscript sections.

Tectonic compilation succeeds; new citations and cross-references resolve.
The table on page 22 was rendered and visually checked. The existing overfull box in
`proof_strategy.tex` remains outside this edit; the implementation section and table have
no overfull boxes. The Lean ports and their audits belong to code commit
`4069f75`; the subsequent structural/native integration is recorded below.


## Structured Notion integration

The Notion row now includes the structural MRDT, compiled indexed algorithm,
original independent history proof and both refinement layers. Its current
columns are 766 definition / 133 specification / 73 VC-support / 20,630
bridge-and-execution lines, after the block-merge extension of the typed core
(measured at `2d227ed`, 448 pinned files). This includes concrete certificate wrappers formerly
misclassified as shared. See the measurement README for exact role movements;
the smaller VC column is not a proof reduction. The earlier structural-Notion refresh preserved the other datatype rows. The earlier 223-root measurement additionally included the full priority-query/client interface and sided Peritext consolidation. The block-merge refresh changed only the Notion row; the export now audits 252 roots.

The structural target has actual operational reach and RA theorems. The compiled
runtime has receipt/merge representation preservation, honest-domain progress,
registered-query agreement and constructive loading of a closed honest version.
It does not have a separate unrestricted native Configuration RA package.
The unchanged specification is reused through proved equality of observations;
new datatype-specific refinement dependencies are counted rather than hidden.
