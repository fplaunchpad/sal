# Paper revision: essential changes and presentation choices

15 October 2026. Revised after Claude's fourth appendix review and KC's
instruction to favour understandability over mechanization-level detail.
Baseline: Overleaf `803a9a4`, Sal `ae7e1c8`, datatype Site version 20.
Minor edits and reference corrections are published in Overleaf `1664c1d`.
This is an author-facing review; `PRIORITIZED_REMAINING_WORK.md` remains the
only development task list. Earlier audit and publication detail is retained
in this file's Git history.

The 26 implementations have checked Lean proofs. The remaining issue is how
the manuscript states the conditions those proofs use. Keep the simple account
in Sections 4–6 and explain the certified extension in Section 7. Put detailed
side conditions and their proofs in the appendix, referenced by the theorem.
Do not reproduce Lean interfaces or add a proof-route alphabet to Table 1.

Minor bookkeeping can be implicit where the meaning is clear. A condition
that changes whether a theorem is true must be stated or explicitly referenced.
GC remains outside this paper.

## Recommended changes, in priority order

### 1. Complete the commutation assumption — Section 4

Keep Kartik's `rc-non-comm` formulation for unequal operations. Add the missing
assumption that events carrying the same operation commute under the same
comparison conditions. Having no `rc` edge does not itself establish this.
Without the missing case, the determinacy proof is incomplete.

Make the qualification explicit beside the new assumption:

> The equal-operation assumption uses the same event and state restrictions
> as `rc-non-comm`. Section 7 describes these restrictions for certified
> implementations.

Do not state unconditional equal-operation commutation: efficient OR-set,
optional register and MVR have counterexamples outside their certified law
domains. Section 3 needs no additional lemma or timestamp assumption here.
Same-replica visibility ordering already follows from the operational rules
and is stated there.

Use one convention explaining that the implementation laws concern event
instances, while the author supplies `rc` on operations. In particular,
`cond-comm` tests the actual absorbing event. Put the detailed timestamp,
replica and certified-event guards with the formal statements; do not
introduce several new kinds of commutation in the running prose.

### 2. State the ordering required of the explaining history — Sections 4 and 6

Add one requirement to the RA-linearizability witness: it preserves visibility
between updates whose order matters in the sequential specification, as well
as `lo_E`. The same sequence must satisfy both requirements and explain the
query answer.

Present `spec-non-comm` as a sufficient condition for obtaining this ordering,
rather than a mandatory requirement on every implementation. Keep the datatype
laws as hypotheses of the verification theorems, rather than building all of
them into the definition of RA-linearizability. Native RGA needs this change:
its concrete insertions commute, but their sequential list operations need not.
The broken-removal example remains a useful motivation.

This is a short definition/theorem adjustment; no additional taxonomy is
needed. Keep concrete equality for implementation states.

### 3. Explain the certified extension — principally Section 7

Retain the two-proof structure: the five VCs establish the implementation
result; a separate proof establishes agreement with the sequential
specification. Explain three generalizations in familiar terms:

- **Which events and states the laws concern.** Issuance and execution facts
  justify restricting the relevant comparisons and states. The restriction
  must also cover states used by the proof when it reorders already-issued
  events, not just states stored at replica heads. Where commutation uses an
  invariant, use it consistently in the visibility and absorber clauses.
- **Which causal predecessors a merge proof retains.** Some implementations
  need commuting predecessors too. Bounded counter and MVR use the full causal
  past. Keep Section 5's simpler choice, then explain the more general choice
  in Section 7. Closure and the induction's maximal-event choice must change
  consistently; give those details in the appendix.
- **Which sequential histories must be legal.** For a certified execution,
  construct one permitted history with the correct query answer. This need
  not establish that every possible implementation fold is a legal sequential
  history. Issuance evidence for this argument does not necessarily restrict
  the update or merge equations themselves.

Before the certified theorem, explain the event restriction briefly:

> These assumptions concern the event pairs compared by the proof.
> Same-replica events are already ordered by visibility. For MVR, issuance
> additionally ensures that a write overwrites only observed writes, so
> concurrent issued writes commute.

Explicitly include equal-operation commutation among the restricted
assumptions. The same-replica observation alone does not justify MVR's
restriction; its observed-overwrite argument is also needed. Keep the exact
guards in the appendix, separately for each law.

State the history requirement in words: the selected history respects the
required implementation and specification ordering, is admitted by the
sequential specification, and explains the implementation's query answer.
Retain the qualification above that state restrictions cover reconstruction
states as well as stored states.

A suitable *summary*, not yet a complete formal theorem, is:

> Under the stated preservation and reconstruction conditions, the five VCs
> establish convergence of certified executions. If certified history adequacy
> also holds, those executions are RA-linearizable with respect to the
> sequential specification.

The theorem must reference precise appendix conditions. These include initial
and update/merge preservation, uniqueness of represented states, and the
smaller-state reconstruction needed by the induction. Do not assume the final
merge result as a premise of its own proof. Do not claim that every arbitrary
fold agrees where the checked result only establishes agreement of permitted
replays.

Two changes belong alongside this explanation:

- Define issuance operationally: check `G(e,s)` at the actual source state in
  the issuing Apply step. Keep the existing sentence that guards are not
  rechecked during reconstruction. An existential replay with a passing guard
  is not automatically equivalent to checking the source state.
- Repair the RGA example using Appendix A's checked specification and history
  argument. Root `0` is reserved. Do not argue that concrete insertion
  noncommutation forces anchor-before-use: native RGA's insertions commute.
  Show why the chosen history both admits the operations and gives the right
  list; enabledness alone does not establish the latter.

The simple presentation is the unrestricted special case, after items 1–2 are
repaired. Lean has several related interfaces, not a single existing theorem
whose name alone certifies all rows. Check the correspondence of the proposed
statement to each proof family before saying it covers all 26. This is an
internal validation requirement, not another table for the reader.

### 4. Make the small proof repairs — Sections 4–6

| Location | Minimal change | Why it matters |
|---|---|---|
| Canonical states and Section 5's induction | State the event-set domain on which `can(E)` is defined, including the weakly closed subsets used by the proof. Give the precise domain in the appendix if necessary. | Causal closure alone does not cover all uses in the induction. |
| Sequential labels | Keep `ops`; state once that labels retain the identities needed by the specification. | RGA needs the inserted identity. No separate projection framework is needed. |
| Simulation condition (iii) | Require the specification to admit the query transition returning the implementation's answer. | Merely constraining answers *if* admitted is vacuous when no answer exists. |
| State after a specification history | Use relational execution, or state determinism before treating the reached state as a function. | The stated transition-system definition does not automatically imply determinism. |

These are local mathematical corrections, not reasons to expand the exposition
with implementation terminology.

### 5. Correct the prior-work distinction — Section 2 and summary claims

Wang's single total sequence and Soundarapandian et al.'s configuration-wide
partial relation are different requirements. Figure 2's opposing branch orders
refute the former; they do not alone refute the latter. Explain the latter's
problem through an absorber outside a version changing the ordering inside
that version. The bottom-up construction problem should be explained
separately. Carry this distinction into the abstract, introduction, Section 4
and related work wherever they make the same claim.

Do not claim a convergence counterexample merely because two permitted replay
orders differ. Attribute convergence to the state-agreement theorem and its
hypotheses, not to query-history admission alone. Say briefly that recursive
merges may compute a base state without allocating a version, and refer to the
extension proof. No GC discussion is needed.

### 6. Align the headline and implementation claims

KC approved this abstract sentence, published in Overleaf `109323c`:

> We mechanize the framework and its extension to issuance- and
> execution-certified implementations in Lean, and verify 26 implementations
> against their sequential specifications.

Keep the Notion case-study mention. Use the same scope when updating the
introduction. This is a fair description of the mechanization; it does not
replace the theorem work in item 3.

The implementation section already distinguishes restrictions on algebraic
laws from issuance/protocol evidence used by a history proof. Keep that
paragraph concise and refer to Section 7 after its revision. Do not restore an
exhaustive exception list or claim that any use of a scoped proof means the
raw update equations fail.

## Lower-priority readability

Deduplicate the two flag entries and repeated sequence kernels when practical.
Rename an insertion anchor where it clashes with `merge(l,a,b)`'s branch `a`.
Keep the existing datatype explanations and source references. These edits
should not delay fixing a false theorem premise or an incorrect attribution.

## What is already resolved

Overleaf commit `1664c1d` (15 October) corrects grammar, missing set braces in the
Section 2 example, the direction stated for following parent links, and the
wording about the initial-state abstraction condition. Appendix B now says
that we record source hashes and request traces in the code repository.
These edits do not implement the substantive theorem repairs above.

The bibliography pass consolidates `Peepul` into `Vimala`, and folds the
separately listed extended versions into the corresponding published entries,
retaining their arXiv links. It corrects the Banyan thesis to a master's thesis
([title page](https://kcsrk.info/papers/shashank_ms_thesis.pdf)), adds the
priority-queue paper's pages 302–312, fixes the F* title and protects proper
names and acronyms. Author, title, year, venue and page metadata were checked
against publisher-deposited Crossref records; VeriFx was checked against
[Dagstuhl's record](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.9).
The Notion blog's author list and date agree with its original page.
The Banyan conference paper and thesis remain separate publications.
All 42 cited references resolve; there are no duplicate citation keys or
DOIs, duplicate labels, or unresolved cross-references. The PDF compiles
without overfull boxes, retains 23 main-text pages, and has 72 pages in total.
The remaining prior-work interpretation issues are still tracked in item 5.

Claude's round-4 review found no new appendix correctness errors. The checked
corrections include efficient OR-set's conditional-commutation example, the
concurrent priority-queue comparison, bounded counter's causal dependencies,
all four Sided Peritext boundary rules, the tree-move specification and
Notion's reference reconstruction.

AegisSheet now explicitly distinguishes its persistent cutoff mask from
Scala's observed-remove purge: an unseen concurrent edit can survive in Scala
but be masked by our model. The theorem concerns the model's specification;
it is not a Scala-equivalence theorem. That limitation is already visible in
the appendix and Site.

Native RGA and incremental tree move have unrestricted update/merge laws on
their declared states; tree move's state type includes log/tree coherence.
Notion's union laws are also unrestricted. Their separate history proofs use
issuance or protocol evidence. The earlier review's identification of two RGA
certificate files was mistaken and has been corrected.

Published corrections: Sal `84afa3a`, `4863cc7`, `ae7e1c8`; Overleaf `803a9a4`;
Site version 20. The previous checked manuscript had 23 main-text pages,
references beginning on page 24, and 72 pages including supplementary material.
The repository gate passed 3,876 Lean jobs, 18 public contracts, 13 controls,
187 runtime tests and 569 benchmark records. All 444 measured source hashes
were unchanged. The abstract-only revision also compiles without overfull
boxes or unresolved references; visual review confirms the wording, and the
main text still ends on page 23.

## Evidence for author verification

| Question | Checked source |
|---|---|
| Kartik's split assumptions | [SplitPolicy.lean](../Sal/MRDTs/Paper1/SplitPolicy.lean) |
| Specification visibility and RGA compatibility | [EventBridge.lean](../Sal/MRDTs/Paper1/EventBridge.lean), [RGAConcretePort.lean](../Sal/MRDTs/Paper1/RGAConcretePort.lean) |
| Invariant-preserving order | [InvariantOrder.lean](../Sal/MRDTs/Paper1/InvariantOrder.lean) |
| Dependencies and five-VC induction | [ConcreteMetadata.lean](../Sal/MRDTs/Paper1/ConcreteMetadata.lean), [ConcreteJoin.lean](../Sal/MRDTs/Paper1/ConcreteJoin.lean) |
| Execution/history interfaces | [ConcreteVCExecution.lean](../Sal/MRDTs/Paper1/ConcreteVCExecution.lean), [ConcreteHistoryBridge.lean](../Sal/MRDTs/Paper1/ConcreteHistoryBridge.lean) |
| Actual issuance evidence | [Certificates.lean](../Sal/MRDTs/Framework/Certificates.lean) |
| Appendix counterexamples | [AppendixReviewControls.lean](../Sal/MRDTs/Paper1/AppendixReviewControls.lean) |
| Aegis source difference | [Scala audit](aegissheet-scala-audit.md), [regression](../audits/aegissheet/AegisSheetRegressionSuite.scala) |

These pointers support the author audit; their names need not enter the paper.
