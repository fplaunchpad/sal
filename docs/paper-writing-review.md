# Sal manuscript review — section-by-section starting point

Reviewed 14 October 2026. Manuscript: Overleaf **`bd18900`**, fetched and
fast-forwarded into `/Users/kc/repos/Sal_paper`. Mechanization: Sal `paper1`
**`12886ba`**, including the final natural-specification proofs in `706036c`.
This review expands the [concise paper reconciliation](paper1-formalism-reconciliation.md),
which has been synchronized to the same manuscript and proof baselines. It is
not a second development task list. No manuscript
prose has been edited by this review. The local `main.pdf` was already modified;
it was preserved and has not been used to establish the current page count.

**Scope:** GC is excluded from this paper, including contributions, evaluation
and future-work discussion. It belongs to a separate paper. The existing
`gc.tex` is not included by `main.tex`. The paper budget is 23 pages; the exact
venue accounting for references/appendices must be checked before budgeting.

## Overall assessment

The manuscript has a substantial motivation, operational model, proposed
criterion, five-VC argument and ordinary OR-set simulation. The latest revision
adds an introduction. The principal missing contribution is the extension to
issuance-certified executions and justified representation invariants, followed
by an independent sequential-history bridge. Without that extension the text
does not yet describe the results for the principal sequence case studies.

The paper should distinguish two proof obligations throughout:

1. The five merge VCs and supporting replay/representation laws establish the
   implementation's stored-state reconstruction and convergence.
2. A separate bridge supplies an admitted independent sequential history,
   with the required implementation order, specification-conflicting visibility
   and query answer on the **same witness**.

For positional APIs there is also a local correspondence lemma: preparing a
client edit and executing its generated message has the requested visible
effect. This supports the specification's interpretation; it is not a sixth
merge VC or a replacement for the global history theorem.

## Claims missing from the contribution list

| Claim worth including | Checked evidence | Qualification needed |
|---|---|---|
| Lean mechanization of the criterion and sufficient-condition metatheory | [Production ledger](../Sal/MRDTs/Metatheory/RefactorLedger.lean), [formal reference](paper1-formal-reference/main.pdf) | Claims concern the mathematical store and specified implementations, not arbitrary deployed networking code. |
| The same five merge equations support certified implementations | [Correctness audit](paper1-correctness-audit.md), `CertifiedRGAVC`, `CertifiedRGAExecution` | State original issuance, independently justified invariant, representation uniqueness and reconstruction/replay supply. Do not advertise arbitrary-public-order replay uniqueness. |
| Independent, shared natural specifications across representations | [Coverage table](natural-sequential-specifications.md), `ORSetSharedSpecification.admits_iff` | Both OR-sets share ordinary-set semantics. Count proof configurations separately from distinct ADTs. |
| Natural sequence case studies, including complete FugueMax bridge | `FugueMaxNaturalCertificate.correct`, `correctV`; `RGAClientPhysical`; `EmbedRGAClientLocal`; `SidedRGAClientLocal` | FugueMax uses the justified invariant order and retains stable IDs/left origins. Other RGA global contracts retain identified-operation languages. Local positional correspondence does not imply a globally position-only history. |
| Reusable VC automation with measured author effort | [Automation report](../experiments/vc-automation/README.md) and its fixed-baseline reports | Distinguish generated obligations, finite author laws, existing issuer evidence and sequential-bridge proof effort. No claim of invariant discovery. |
| Recursive merge-base correctness | Formal reference Definition 3.4/Theorem 5.7; ordinary/virtual certificate pairs | A recursive base is a computed state, not necessarily an allocated version or an “actual LCA.” Keep the main statement concise. |

The first four are central to the research story. Automation merits an
implementation/evaluation claim. Recursive bases can be a concise supported
extension with details outside the main proof narrative. Maximal noninterleaving
is additionally available for FugueMax on the same witness; mention it only
with its precise property and scope, rather than making all sequence results
depend on it.

## Section review

### Abstract — `main.tex:28`

Empty. Write it after fixing the contribution list: problem with the existing
criterion/proof construction, version-relative repair, five-VC theorem plus
sequential bridge, mechanization and representative evidence. Use a checked
coverage count only after reconciling the evaluation inventory.

### 1. Introduction — `introduction.tex`

Now present in `bd18900`; earlier notes calling it empty are obsolete.

- Lines 76–87 and 109–114 overstate what the RA definition itself establishes.
  Explain which implementation laws and canonical/represented-state theorem
  establish convergence. Observational history admission alone does not
  establish equality of hidden implementation states.
- “Respects the visibility relation” is too broad: identify the required
  noncommuting/specification-conflicting edges. Full causal preservation is not
  the criterion used by every sequential witness.
- “All valid linearizations ... produce the same state” needs the raw global
  theorem's domain; it is not the certified RGA/Fugue theorem.
- “Avoids constructing linearizations of merged versions” should refer to
  building them from the chosen branch sequences. The sequential bridge can
  still construct a witness.
- Add certified execution, Lean mechanization and evaluated coverage/automation
  to the contributions. OR-set as a running example is supporting evidence,
  not a substitute for these contributions.
- Review the opening generalization about CRDTs: the semilattice description
  should be scoped to state-based CRDTs. Keep source comparisons precise and
  check them against the cited papers when editing related work.

### 2. Motivation — `motivation.tex`

Substantial and useful. Keep the natural ordinary-set example, the global-order
counterexample, and the defeater for the branch-last-event construction.

- The bottom-up explanation is duplicated around lines 441–480; retain one
  account. It consumes space needed for the certified case study.
- State precisely whether each example refutes a criterion, demonstrates a
  limitation of a proof construction, or distinguishes convergence from
  independent specification correctness. These are different claims.
- The no-op-remove example is rejected by specification compatibility/the
  stronger visibility obligation; the literal implementation-order-only
  criterion can accept it. Preserve that distinction when shortening prose.
- Check Wang/Neem comparison against the cited definitions before making a
  blanket statement about all existing RA-linearizability definitions.

### 3. Operational semantics — `opsem.tex`

Present, with a raw Apply rule and ordinary allocated-ancestor Merge rule.

- Add the certified execution interface: which requests may be issued from a
  source state and what execution evidence is retained. Explain original
  issuance separately from applying an already-issued event in a replay.
- `range(S)` contains state/event-set pairs; the global event union at lines
  61 and 87 must project their event-set components.
- “Active version” currently means every stored version. Distinguish this from
  current replica heads when stating quantified results.
- Lines 118–122 promise recursive merging without its operational definition.
  State the computed-base extension and point to its checked theorem; avoid
  saying recursion creates an allocated actual LCA.

### 4. RA-linearizability and canonical states — `ralin.tex`

Present; this section needs the most careful mathematical correction.

- Lines 155–181: retain Kartik's unequal-operation `rc-non-comm` formulation,
  but add equal-operation event self-commutation. State the eligible event
  guards explicitly. Payload inequality alone leaves a gap in determinacy.
  Evidence: [SplitPolicy](../Sal/MRDTs/Paper1/SplitPolicy.lean).
- Line 31 quantifies commutation over every state. Keep this as the raw
  specialization and introduce the independently closed invariant domain for
  certified cases. Do not silently replace it with “both operations can be
  issued here”: replay and issuance have different roles.
- Restore explicit `f : Events → U` and `ops_f` around lines 138–153. Ordinary
  OR-set can erase metadata; sequence IDs and escrow replica accounts cannot
  be erased indiscriminately.
- State specification-conflicting visibility on the same witness, and present
  event-specific implementation/specification compatibility as a sufficient
  way of preserving it. Payload noncommutation merely witnesses some metadata
  pair; it does not establish noncommutation of the actual events.
  Evidence: [ProjectedCriterion](../Sal/MRDTs/Paper1/ProjectedCriterion.lean),
  [InvariantOrder](../Sal/MRDTs/Paper1/InvariantOrder.lean).
- Canonicality is defined for causally closed sets, but the next section uses
  weakly closed sets and peeled downsets. Give existence/uniqueness on the
  exact induction domain, including finiteness; keep the certified theorem
  separate from arbitrary-linear-extension uniqueness.
- An arbitrary relational sequential machine need not reach a unique state.
  Avoid function notation for its run without a determinism premise.

### 5. Five-VC proof — `proof_strategy.tex`

The five equations and the defeater walkthrough are present. `bd18900` improves
the VC3 explanation and removes the undefined `Supported` use in VC2.

- `Admissible` still uses unbound `E` instead of `E_i` (around lines 83–89).
- A downset contains the event itself; every other member precedes it in a
  respecting extension, not necessarily by a single direct `lo` edge.
- Supply closure/existence premises for every canonical state in VC2–VC5.
- Present the certified reconstruction extension explicitly: commuting causal
  predecessors may still provide required metadata. The peel must preserve
  semantic order and reconstruction dependencies. Acyclicity alone is not
  this supply theorem.
- The local theorem assumes more than five bare equations: policy/replay and
  representation hypotheses must be visible in its statement.
- Manuscript VC4 is causal-delta and VC5 shared redistribution; the formal
  reference numbers these oppositely. Choose one numbering and align the
  reference when editing; compare equations by name meanwhile.

### 6. Sequential specification bridge — `seq_spec.tex`

Present, with ordinary-set simulation and the broken-remove example.

- Lines 99–109 are implication-only conditions: if no matching specification
  transition exists, both hold vacuously. Require matching update/query
  transitions to exist, or explicitly restrict this shortcut to a total
  deterministic machine with pure queries. Quantify the complete event.
- The lifting theorem must carry any policy/compatibility assumptions required
  by the target RA definition. At line 82 invoke its premise, not itself.
- Keep the all-linear-extensions route as one sufficient theorem. Add the
  certified same-witness history route used by RGA/Fugue; do not require every
  public-order extension to be admitted by their guarded specifications.
- Explain the local client-request/message correspondence separately, ideally
  with the positional edit equation already in the formal reference.
- Keep `alpha` as an implementation-to-specification refinement map. It is not
  an observational quotient replacing concrete equality in the five VCs.

### Sequence case study — `rga.tex`

Only a “Verified Tombstoned RGA” heading, and **not included by `main.tex`**.
Choose the case study deliberately before writing. Embedded RGA provides a
clear certified five-VC example; native tombstoned RGA is a different
implementation and should not lend its name to the embedded proof. FugueMax
can illustrate the stronger natural-specification result with retained origins.
The case study must show the issuer, invariant, five-VC connection, independent
specification and final history bridge. Avoid presenting a separate local
list theorem as the complete contribution.

### Implementation and evaluation — `implementation.tex`, `evaluation.tex`

Both headings only. Missing: Lean architecture and trusted boundary, how
finite obligations become five VCs, what the RDT author supplies, measured
proof effort, and an evidence-linked coverage table.

Use separate columns for merge VCs and sequential bridge. Include meaningful
negative controls. Separate proof configurations from distinct ADTs and from
runtime packages. The automation corpus has 21 retained configurations; the
published bounded counter and the two source flags have separate checked
certificates and are not measured cases in that corpus. Do not add these
numbers and call the result a count of distinct datatypes.

Counter inventory check: `FlatCounters.Counter` and `FlatCounters.IOC` both
instantiate the same integer-delta implementation with constant delta 1. Their
single-operation alphabets differ only by constructor naming. `FlatCounters.PN`
also permits delta -1, so its API is broader; all three share integer state,
merge `a + b - ancestor`, and the generic proof. Recommend one counter-family
row represented by PN, mentioning increment-only as a restriction. This is a
presentation recommendation; the current 21-case measured inventory has not
been changed. The bounded escrow counter is a separate datatype because its
issuance, rights and transfer semantics differ.

For obligation counts, the policy expansion has 17 merge/replay schemas plus
8 separately reported policy/event laws. Other templates use different
interfaces; there is no single global expansion count. Describe native Lean
tactic discharge as proof automation, with the finite laws and issuer evidence
still supplied by the author; do not advertise invariant discovery.

**Evidence hygiene before copying tables:** the automation README still calls
Fugue's obstruction the current endpoint in several places. The reconciliation
note now corrects that obsolete “20 positive history results and Fugue's
obstruction” summary. The former live-parent language is still refuted, but the new
natural-origin language has a complete certificate. Existing effort tables do
not measure that new bridge. Correct status labels without inventing updated
line-count measurements.

### Related work and conclusion

Both headings only. Related work should distinguish the criterion from its
verification method, compare precisely to Wang and Neem, and explain the role
of independent sequential specifications and certified invariants. Avoid
generic criticism covering every CRDT/RA approach. The conclusion should state
the theorem scope and the evaluated evidence. GC is excluded here too.

## Correspondence with the concise reconciliation

| Reconciliation item | Review location |
|---|---|
| 1. Split policy laws | Section 4: equal-operation commutation and event guards |
| 2. Label projection and compatibility | Section 4: explicit labels and same-witness specification visibility |
| 3. Canonicality domain | Sections 4–5: closure, finiteness and peeled sets |
| 4. Simulation transition existence | Section 6: nonvacuous matching transitions |
| 5. Certified extension | Sections 3–6 and the missing sequence case study |
| 6. Recursive bases | Section 3 and the contribution-scope table |
| 7. Coverage and evidence | Implementation/evaluation, including current Fugue status and historical measurements |
| 8. Contributions and unfinished prose | Abstract, introduction, related work and conclusion |

The additional motivation comments concern exposition and source comparison;
they do not change the mathematical correction list. The review's broader
writing suggestions are proposals for discussion, not manuscript edits already
made. Both documents exclude GC.

## Suggested editing order

First agree the contribution list and theorem scopes using this review. Then
edit Sections 3–6 and the certified case study, fill implementation/evaluation,
and return to the introduction/abstract/related work/conclusion. We can discuss
each section before changing it. Preserve author prose where it already says
the right thing; the review is not a request for a wholesale rewrite.

## Review limits

This review reads the current LaTeX and checked Lean declarations, with an
independent Sol6.1 audit of the formal core. It does not claim a fresh PDF
layout/page-budget check, a final distinct-datatype count, new author-effort
measurements, or completed literature verification. Those are identified
writing/evaluation tasks, not completed results.
