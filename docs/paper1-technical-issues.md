# Sal paper: consolidated technical review

15 October 2026. Combines Claude's [review](paper1-claude-review.md) with the
Codex [section review](paper-writing-review.md) and
[reconciliation note](paper1-formalism-reconciliation.md), checked against
paper commit `6089af1` and Sal `paper1` commit `1f9c30d`.
This is a review record, not another development task list.

The main issue is correspondence: the paper's stated assumptions and
criterion do not yet describe all the checked case studies. This does not
show that their Lean proofs are wrong. It means the paper must state the
theorem those proofs actually establish. Tightening prose alone will not
resolve this.

“Confirmed” below means checked against the current manuscript and the cited
source or Lean declarations. Recommendations are proposed manuscript changes,
not claims that those changes have already been made. GC stays outside this paper.

## Changes in priority order

Items 1–4 establish the criterion and assumptions used by the case studies;
items 5–8 repair the supporting proof statements and examples. Item 9 is
also submission-critical and can be handled in parallel with both groups.
Item 10 then aligns the headline claims with the repaired theory. Finish with
the smaller corrections below. This orders the manuscript work by dependency;
it does not make the later correctness issues optional.

### 1. Complete Kartik's commutation assumptions

**Confirmed — §4, displayed datatype laws.** The paper exempts equal operation
labels from `rc-non-comm`, but does not separately require equal-label events
to commute. The determinacy proof needs that missing case. Applying the exact
same event twice is not the issue: two events can carry the same operation
and different identities.

**Change:** keep Kartik's unequal-operation formulation and add equal-operation
commutation, on the same eligible-event and state domains. State the event
guards explicitly. The policy remains a relation supplied on operations.

Vimala confirms that equal operations have no policy edge. That fact alone
does not establish their commutation; the separate assumption is still needed.
This corrects Claude's suggested remedy: deleting the unequal-operation guard
is not necessary. Lean already proves equivalence between the split and
combined formulations, including the certified and invariant-restricted forms.

**Evidence:** [SplitPolicy.lean](../Sal/MRDTs/Paper1/SplitPolicy.lean),
`guarded_iff_repaired`, `Certified.existing_iff_repaired`, and
`Invariant.existing_iff_repaired`.

### 2. Put specification ordering in the criterion used by the case studies

**Confirmed — §4, RA-linearizability and `spec-non-comm`; §7 theorem.**
The paper makes implementation/specification commutation compatibility
mandatory. Native RGA cannot satisfy it: concrete birth-record additions
commute, while the corresponding list operations need not. Its checked proof
instead chooses a history that preserves visibility between
specification-conflicting updates directly.

**Recommended change:** require the same history to respect both `lo_E` and
visibility between updates that do not commute in the sequential
specification. Present `spec-non-comm` as a sufficient way to obtain the latter
property, rather than a mandatory law excluding the RGA case study. Update
the lifting statements consistently. The no-op-remove example still motivates
this requirement.

**Evidence:** [EventBridge.lean](../Sal/MRDTs/Paper1/EventBridge.lean),
`EventVersionsSpecificationRA`; [RGAConcretePort.lean](../Sal/MRDTs/Paper1/RGAConcretePort.lean),
`globalCompatibility_impossible`.

### 3. State the certified five-VC extension, including its state domain

**Confirmed — §§4–5 and §7; Table 1.** The general exposition quantifies over
all implementation states and claims uniqueness for all allowed folds.
Several checked implementations use a justified set of states and certified
events. §7 currently restricts executions but does not state the corresponding
commutation, representation and reconstruction assumptions.

**Change:** define the state invariant and its preservation, restrict the
relevant laws explicitly, and state the conditions that allow the inductive
proof to reconstruct smaller states and retain required predecessor events.
Then state the five-VC sufficient-condition theorem on that domain. Preserve
concrete state equality. Merely saying “reachable states” or “operations that
can both be issued here” is insufficient: already-issued updates are also
applied during reconstruction.

For the independent history proof, distinguish one suitable history from
every linear extension. Do not claim the stronger result for a case study
whose theorem only supplies the former.

**Evidence:** [InvariantOrder.lean](../Sal/MRDTs/Paper1/InvariantOrder.lean),
`Commutes`, `Closed`, `VersionsRA`; the certified replay and execution
theorems linked in the [correctness audit](paper1-correctness-audit.md).

**Coverage correction:** the current table uses `AnchoredQueue.publicQueue`,
not the old `Instances.Queue` in Claude's obstruction. Its public certificate
concludes invariant-restricted RA-linearizability. The MVR row does use
`MVRLive`, but its proof derives restrictions on concurrent issued events.
An impossibility over arbitrary events does not refute that certified result.
Complete the per-row theorem mapping before saying all rows instantiate one
unrestricted theorem; an extra jargon-heavy table column is not essential.

Round 2 adds a concrete dependency-set obstruction. Bounded counter and MVR
use full causal metadata, not merely noncommuting visibility. For bounded
counter, `empty_metadata_causal_obstruction` proves that two same-replica
increments yield 1 under the body's empty-base VC4 merge and 2 under the
required update. Generalizing the dependency relation requires changing
closure, peeled-event maximality and reconstruction premises together. The
Lean interface is `MetadataDependencies`, with noncommuting visibility
contained in `before` and `before` contained in visibility. Relation inclusion
alone does not discharge `PeelChoice`/`ReplaySupply`.

Event-law domains also differ. Efficient OR-set and optional register use
different-replica exactness and actual-event conditional commutation; MVR
uses eligible **concurrent** writes and causally ready represented prefixes.
Its causal overwrite example crosses replica IDs, so simply exempting
same-replica pairs does not cover MVR. The implementation section now states
these distinctions explicitly. This qualifies the table's coverage claim;
the formal body extension remains to be stated.


### 4. Make the operation-label convention explicit

**Clarification from Vimala — §2 labels, §4 sequential specification, §§6–7.**
Vimala proposes keeping `ops`, with any required timestamp and replica identity
included as arguments of the operation label. This is a valid presentation;
a separate projection function `f` is not necessary.

**Change:** state that convention explicitly and apply it consistently to the
sequential labels and simulation conditions. The ordinary-set specification
can ignore these arguments; RGA retains the inserted identity named by later
operations. Keep the distinction between the operation-level policy supplied
by the datatype author and the event information exposed to a specification.
The current §4 text alone describes `ops` as projecting the operation out of
`(t,r,o)`, while §7's insertion label also includes `t`; this connection needs
one explicit explanation, not a new abstraction.

### 5. Give canonical states the domain used by the induction

**Confirmed — §4 order/determinacy/canonical-state definitions; §5 VCs.**
Section 4 requires causal closure. Section 5 removes maximal events and uses
sets closed only under noncommuting predecessors. Such a set need not be
causally closed, so the earlier definition does not cover every use of `can`.
For example, if `a` is visible to a commuting event `b`, removing `a` from
`{a,b}` leaves a weakly closed set `{b}` that is not causally closed. Vimala
has asked Kartik to confirm this point; his response is pending.

**Change:** state existence and uniqueness on the exact finite, supported,
weakly closed domain used by the raw proof. State the certified reconstruction
domain separately. Check every canonical-state expression in the VCs and
Join lemma against those premises. This is a theorem-scope correction, not
just a terminology replacement.

### 6. Check issuance at the actual source state

**Confirmed — §7, definition of certified executions.** The current definition
requires a guard to hold at *some* ordered replay of predecessors. The intended
operational condition checks it at the replica head where the event was
created. Those are not interchangeable without a state-agreement argument.

**Change:** add `G(e,s)` to the issuing Apply step and retain that issuance
evidence. Keep the existing explanation that reconstruction does not issue
the event again. State the state-agreement premises used when transferring
this evidence into the history proof.

**Evidence:** [Certificates.lean](../Sal/MRDTs/Framework/Certificates.lean)
and the [formal reference](paper1-formal-reference/main.pdf), certified-execution
definitions.

### 7. Replace the RGA example with the specification and argument actually proved

**Confirmed — §7 RGA example.** The manuscript uses a retained list plus
tombstones and guarded deletion. The checked native-RGA specification uses a
live list plus an allocation registry, a live-anchor insertion condition and
total deletion. Its concrete insertions commute, contradicting the example's
claim that `lo_E` must order an anchor's birth before its use.

**Change:** use the checked specification, handle root `0` separately, and
explain how the proof selects an admitted history with the correct query
answer. Enabled operations alone do not establish answer agreement: two
insertions after the same anchor can be legal in either order and produce
different lists.

**Evidence:** [RGAConcretePort.lean](../Sal/MRDTs/Paper1/RGAConcretePort.lean),
[RGAIdentified.lean](../Sal/MRDTs/Paper1/RGAIdentified.lean), and Appendix A's
native-RGA entry.

### 8. Require the sequential specification to admit the returned query answer

**Confirmed — §6, simulation condition (iii); §4 specification notation.**
Condition (iii) only says that an admitted answer equals the implementation's
answer. It is vacuously true when no answer is admitted. Also, an arbitrary
transition relation need not have a unique state after a history.

**Change:** directly require the query transition labelled with the
implementation's answer to exist. Use relational execution notation, or
explicitly assume determinism before writing the reached state as a function.
The current update condition (ii) already requires a transition: earlier
notes claiming it too is implication-only are stale.

### 9. Distinguish Wang's total sequence from Neem's partial relation

**Confirmed — abstract, Introduction, §2, §4 discussion and Related Work.**
Wang fixes a single total sequence. Neem fixes one configuration-wide partial
relation `lo_C`; each replica may have a different linear extension of its
restriction. These are not equivalent requirements.

Figure 2's opposing branch orders refute a single total sequence. They do
not refute Neem's definition: both branch witnesses can extend its partial
relation. The separate issue with Neem is that an event outside a version
can remove an ordering edge inside that version. The resulting restriction
need not determine a unique implementation fold.

**Change:** distinguish these two problems throughout. Attribute the forced
cycle to the total-sequence requirement. Explain why Sal searches for absorbers
inside the event set being explained. Identify Figure 2's annotations as Sal's
version-relative relations. Explain the failure of constructing a merged
history from branch endings separately. Do not claim a counterexample to SEC
from this figure alone.

**Evidence:** Neem source, `lin.tex`, Definitions `lin-relation` and `lin`;
Claude review §2, independently cross-checked. No new implementation proof is
needed to correct the attribution.

### 10. Scope the convergence and recursive-merge claims correctly

**Confirmed — abstract/Introduction/conclusion; §3 recursive-base paragraph.**
Admission of query histories alone does not imply equality of hidden
implementation states. Convergence follows from the canonical or represented
state theorem and its hypotheses. Also, recursively combining common
ancestors produces a base state, not necessarily an allocated version.

**Change:** attribute convergence to the relevant sufficient-condition
theorem. Scope “all linearizations produce the same state” to that theorem's
domain. Give a concise statement of the recursive-base extension and point
to its proof, rather than treating the computed base as an allocated LCA.
Do not add GC to this discussion.

## Completed local corrections — 15 October

The small corrections below are applied in paper commit `6089af1`, with the
matching appendix source and formal-reference numbering updated in Sal. The ten substantive issues above
remain open; this pass does not change the RA criterion or theorem domains.

| Location | Completed correction |
|---|---|
| §3 Apply rule and explanation | Union the event-set components as `⋃ w ∈ dom(S), E(w)`, rather than unioning state/event-set pairs. |
| §§3–6 version terminology | Use “stored version” for `dom(S)` and retain “active replica” for `dom(H)`. |
| §4 example | Checked that the repeated-event typo was already fixed: the sequence is `[A_p,A_q,R_p]`. |
| §5 principal downset | Explain that every other member precedes the event through a path, in a linear extension containing the downset. |
| §5 Join lemma | Remove the undefined word “supported”; the explicit `E_i ⊆ E_C` premise remains. |
| §5 VC4 explanation | Identify `B` as the base and `e(B)` as the second branch. |
| §5 worked example | State the smaller-union induction arguments before applying VC4; fix `A_p`, set braces and malformed parentheses. |
| §5 `Admissible` | Confirmed that the formula already uses `E_i`. |
| Formal reference | Reorder the displayed equations and update proof references: VC4 is causal delta, VC5 is shared redistribution. The PDF is rebuilt. |
| Related Work/conclusion | The empty duplicate Conclusion heading was removed in `edacc2c`. |
| Bibliography | Use `NotionCRDTBlog` consistently and remove the duplicate `Notion` entry. |
| Paper appendix | Replace the ten prose uses of “Neem” with the cited authors or source implementation. Internal citation keys and Lean identifiers remain unchanged. |
| Throughout edited sections | Correct grammar and typos; replace hard-coded definition/lemma numbers with cross-references; use `rd_a` consistently for the set query. |
| Implementation section | The section is present; framework/per-MRDT obligations and proof columns are explained. |

Validation: the paper and formal reference compile; the main text ends on page
23, references start on page 24, and there are no missing citations, undefined
references, duplicate labels or overfull boxes in the final build. The required
Sal repository checks passed.

Appendix follow-up (paper commit `8628d1e`): each of the 24 datatype entries now places its source
citations immediately below the heading, and the appendix prose no longer
names Sal. Appendix B explains the three public Notion-demo bugs, including
the requests, expected and observed results, and the scope of the Lean checks.
The pinned JavaScript regression rerun reproduced all three failures and passed
the nearby formatting control. These additions do not resolve the ten
substantive issues above.

## Appendix corrections and case-study integration

Claude's eight appendix findings have been corrected. Parent review checked the
efficient OR-set execution scope, both Sided Peritext interfaces and boundary
semantics, LWW's unrestricted history language, RGA/map references, FugueMax's
guard, and Notion's deterministic command behavior with duplicate IDs. Each
of the 24 entries retains source citations and now starts with an explanation
of its operations. Merge arguments consistently use `merge(l,a,b)`.

The new TreeMove implementation performs the source paper's incremental
undo/insert/redo, retaining the tree and old-parent log. The parent independently
built its 15 positive/negative test blocks (3,418 jobs), checked its exact-state
five-VC and ordinary/recursive sequential proofs, and integrated it into the
production registry and coverage inventories. Deletion to trash, hidden-node
restoration and descendant rescue are supported. The appendix gives the new
state and equations. The separate legacy GC proof is not claimed for this
carrier; GC remains outside this paper.

The revised appendix compiles and its TreeMove, Notion and table pages have
been visually checked. The table's variant explanation is now part of the
preceding paragraph; Sided Peritext is marked as an adaptation. Measurement and
publication revisions are recorded in the paper implementation report. Published
as Sal `2854bec`, Overleaf `2a11435` and datatype Site version 18 (source snapshot
`2854bec`). The parent checked the Site diff and rendered TreeMove page; all
1,090 mathematical expressions passed rendering validation.

The same-record priority-queue repair now has a complete independent-history
certificate. Parent review of Algorithm 2 and §5.1.3 confirmed that the published
query can combine the latest insertion's initial priority with another
insertion's increments. Its priority-12 witness conflicts with ordinary
reset/additive semantics under specification-conflicting visibility; the source
claims convergence, not that sequential theorem. The intentional repair selects
both contributions from one latest surviving Add, retaining observed increment
attachments, observed removals and the actual Add-absent / Inc-and-Remove-present
preparation guards. The independent finite-map specification uses total
Add/overwrite, additive Inc with absent no-op, and Remove with absent no-op.

`PriorityQueueSameRecord.historyAdequacy` constructs per-element causal replays
and composes one history explaining every query, including maximum. The
ordinary/recursive certificates consume the named five VCs and shared finite
Join induction; the audit passed 3,424 jobs and 562 declarations with only
standard axioms. Maximum soundness/completeness and derived local removal's
returned pair, effect and actual issuance guard are proved. Seven PASS+FAIL
blocks pin the repair. The replacement has I=yes, E=yes and empty application rc;
seven table rows retain nonempty rc. Measurement and checked integration are
complete: base `2854bec`, 222 roots, 444 source hashes, 26 configurations / 24
paper rows, and PQ columns 98 / 28 / 99 / 1,285. The full gate passed 3,875 Lean
jobs, 18 exact public contracts, 13 certificate controls, 187 runtime tests and
569 benchmark records (`/private/tmp/sal-pq-full-gate.log`); measurement logs are
in `/private/tmp/sal-pq-current-counts`. Published as Sal `3d924a0`, Overleaf
`97e92d7`, and datatype Site version 19, with the new panel pinned to `3d924a0`.
All 444 measured source hashes match that committed snapshot. Parent checked the
rendered table, appendix equations and live Site. Main text remains 23 pages,
references start on page 24; the complete document has 70 pages. Earlier
checkpoints above describe the TreeMove publication, not this replacement.

These appendix and case-study changes do not resolve the substantive theory
issues listed above.


## Appendix round 2 — verified corrections and review qualifications

Checked against Sal `85428c3` and paper `97e92d7`; the corrections below
are applied and locally verified for publication. No datatype algorithm or existing certificate
was changed in response to this review.

| Finding | Result and correction |
|---|---|
| R2-1, bounded counter | Confirmed VC4 scope mismatch; appendix states the full-causal dependency choice and displays the existing 1-versus-2 obstruction. Body work remains under priority 3 above. |
| R2-2, priority queue | Confirmed editorial error: both algorithms reset after remove/reinsert. Replaced the purported separating trace with two concurrent Add/Inc branches: published answer 12, same-record answer 11; ordinary causal outcomes are 2, 3, 11, 13. |
| R2-3, MVR | Confirmed for current MVRLive.D. Added causal overwrite noncommutation and the concurrent-issued-event scope. |
| R2-4, efficient OR-set | Confirmed: identical-label exemption avoids the body's rc-non-comm objection; payload cond-comm fails instead. Added a kernel-checked counterexample and actual-event absorber explanation; corrected certificate citations. |
| R2-5, efficient OR-set source | Confirmed; source already stores replica/timestamp/element triples. Attribution corrected. |
| R2-6, Sided Peritext | Three timestamp-sensitive boundary cases confirmed. The proposed universal deletion-collapse claim is false: a checked example retains a newer marked character after both original anchors are deleted. Appendix states all four boundary rules and the exact collapse conditions. |
| R2-7, AegisSheet | Guard checks supplied roster membership, not acknowledgement evidence, and does not bound the cutoff by observed timestamps. Documented this limit. Round 3 corrects the source comparison: Scala removes observed updates and retains unseen concurrent edits; the model's persistent timestamp mask differs. The proof establishes the model specification, not Scala equivalence. |
| R2-8, optional register | Added same-replica Set noncommutation and corrected the witness to all Unsets/their visible predecessors first, remaining Sets second, each timestamp-sorted. |
| R2-9, TreeMove | Replaced the specification's implementation test with candidate acyclicity; fixed rejection-test polarity and identified the proved equivalence. |
| R2-10, Notion | Corrected block/instance ownership; defined the reference reconstruction used by the guard and shortened executable-proof discussion. |
| R2-11, order citations | Removed dormant nonempty RGA-family event-order citations from empty-policy entries. |

The new `AppendixReviewControls.lean` retains hand-derived PASS+FAIL controls
for all four Sided Peritext boundaries, deletion with surviving grown text,
a nearby genuine collapse, and the efficient OR-set operation-level
conditional-law failure. These are review regressions, not extra premises of
production certificates. Main theorem definitions remain unchanged.

Lower-priority readability work remains: deduplicate the flags and repeated
sequence kernels, and complete symbol hygiene across the long entries. It is
not a substitute for the body-level corrections above.

Validation: the full repository gate passed 3,876 Lean jobs, 18 public
contracts, 13 certificate controls, 187 runtime tests and 569 benchmark records.
All 444 measured source hashes remain unchanged. The manuscript compiles to
72 pages. A subsequent page-boundary check found four conclusion lines on
page 24; the round-3 edit removes the repeated conclusion inventory to recover
the 23-page main-text limit. The root README was reviewed and now
links this remaining theorem-scope work. The Site preparation contains 25
panels and 1,296 checked KaTeX expressions. Round-2 corrections were pushed as Sal `84afa3a` and Overleaf `328e995`.
Site publication was held for the round-3 source correction below.

## Appendix round 3 — source fidelity and scope presentation

Claude independently confirmed all eleven round-2 corrections. Two follow-ups:

- AegisSheet's paper prose about purged contents does not justify equating our
  timestamp mask with its Scala implementation. Scala removes observed cell
  updates; a concurrent unseen edit survives and can revive the row with its
  new value. The appendix now states this difference explicitly. Evidence:
  `docs/aegissheet-scala-audit.md`, the concurrent purge/edit regression in
  `audits/aegissheet/AegisSheetRegressionSuite.scala`, and
  `AegisSheet.cellOverwritten` / `AegisSheet.Sequential.versionPurged`.
- The implementation paragraph's named list of state-restricted examples was
  incomplete. It now describes the classes of conditions and defers each
  datatype's exact scope to the appendix. Invariant-scoped commutation,
  represented merge states and protocol issuance are distinct restrictions;
  a protocol guard alone does not imply that raw update commutation fails.
  The native RGA and incremental tree-move update/merge laws hold on their
  declared states; issuance enters their independent history proofs. Tree
  move's declared state already requires log/tree coherence. Notion's union
  laws also hold universally, while document correspondence uses its protocol.
  `CertifiedRGARichCertificate` concerns Sided Peritext RichCore, not plain RGA;
  `CertifiedSidedInvariantCertificate` concerns Sided RGA. Consequently the
  proposed count of rows outside the unrestricted theorem cannot be inferred
  merely from a declaration containing the word `Scoped`.

No new theorem or source-equivalence claim follows from these editorial fixes.
The formal body extension remains priority 3. Duplicated datatype descriptions
and the anchor/merge-branch symbol collision remain lower-priority work.

### Publication checkpoint after round 3

Corrections are published as Sal `84afa3a` / `4863cc7`, Overleaf `803a9a4`,
and datatype Site version 20. The Site source is
`f6734e46959a992d5db8df9fcb960419db66dce5`; its 13 corrected panels link to
Sal `4863cc744c2b0924bb61fd3d8a38f909e1833677`. Deployment
`appgdep_6ad048b4aa4481918d12d620d95f38dd` succeeded at the existing public URL.
Parent verified the live Aegis source-difference note and final source pin.
The final PDF has 72 pages: main text ends on page 23 and page 24 starts with
references, with no conclusion spill. No overfull boxes or unresolved references
were reported. The proof-size table is unchanged. The general certified theorem
statement and the lower-priority readability items remain open above.
