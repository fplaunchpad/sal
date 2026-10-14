# Implementation section: scope and evidence

Manuscript snapshot: Overleaf `5e51f35`; checked Sal `paper1` code snapshot `4069f75ea054b9820e428018db15b4dc4372a3af` (14 October 2026), including the three new Neem ports. The measurement JSON pins the sources by SHA-256 and retains `c9e945d` as the revision at which measurement began.
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
  consolidated into 24 rows. The 18-package registry and existing 19-case
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

Validation checked all 400 recorded source hashes, all 24 per-row column partitions, and each reported line total. The generic theorem census is 4,020 lines, with 1,688 shared automation theorem lines. The instance audit resolved 181 distinct roots and checked their standard-axiom dependencies. The table has seven nontrivial application-rc rows. The three Notion failure traces and positive formatting control were freshly rerun.

The source hashes match both the working tree and code commit `4069f75`.
The public datatype reference was deployed as Site version 16 with all 24 entries.
The final integration gate passed 3,821 Lean jobs, 187 JavaScript runtime tests,
and 569 benchmark records.

The new rows' Def./Spec/VC-support/bridge-and-execution footprints are
28/18/434/168 (remove-wins set), 25/12/19/136 (set-wins map), and
61/9/717/880 (optional register). The measurement retains the 19 existing
CommonVerification.verify cases, adds the generic policy-expansion derivation
for set-wins map, and includes six named raw five-VC cases. Counts describe
dependency source ranges, not handwritten proof-body size or author effort.

## Draft and validation

The local Overleaf checkout now contains `implementation.tex` and
`implementation_table.tex`, with bibliography additions. `main.tex` includes
that section, removes the empty Evaluation input, and loads `array` for the
table. No other manuscript section was edited. The pre-existing local
`main.pdf` was preserved.

[Compiled review PDF](paper-implementation-preview.pdf): the current draft has
24 pages total; the implementation table is on page 22 and references begin
on page 23. The manuscript therefore reaches 22 pages before references.
The preview PDF matches the compiled manuscript at Overleaf commit `5e51f35`.

Tectonic compilation succeeds; new citations and cross-references resolve.
The table on page 22 was rendered and visually checked. The existing overfull box in
`proof_strategy.tex` remains outside this edit; the implementation section and table have
no overfull boxes. The Lean ports and their audits belong to code commit
`4069f75`; this evidence update changes only documentation.
