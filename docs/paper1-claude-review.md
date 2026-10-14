# Paper 1 review: criterion, Section 2, and technical defects

Reviewer: Claude (Opus 5.5), 2026-10-14. This covers the manuscript in
`~/repos/Sal_paper` at Overleaf commit `04f5f20` plus the uncommitted local
changes present on 2026-10-14: the table/appendix integration and the Figure 1
layout edit. I read every file that `main.tex` builds: introduction,
motivation, opsem, ralin, proof_strategy, seq_spec, issuance, implementation,
implementation_table, related_work and conclusion. For the appendix I read the
preamble and the OR-set and RGA entries. I checked the claims against Neem's
source (`_references/Neem/lin.tex`) and against the Lean definitions that the
table's endpoints conclude. Line numbers refer to the manuscript files as of
that date.

Evidence labels: **verified** means checked against source or Lean;
**proposal** means suggested wording or structure; **decision** means the
choice belongs to KC.

## Summary

1. **The stated theory is not the certified theory.** The headline claim
   (RA-linearizability for 26 configurations) holds against two Lean criteria
   that the paper does not state. Def. 4.5 and its `Laws` are a third, weaker
   or differently shaped criterion. For several rows they are not satisfiable
   at all. See §1.
2. **One law, as written, breaks Theorem 4.3.** The exemption `o₁ ≠ o₂` in
   rc-non-comm allows same-label concurrent events that do not commute and
   are not ordered. See §1.2.
3. **Section 2 misattributes the global-order failure to Neem.** Neem's
   definition fixes one configuration-wide *partial* relation, not one total
   sequence. The execution of `fig:defeater` is RA-linearizable under Neem's
   definition. The forced-cycle argument refutes Wang's single sequence only.
   Neem's actual defect is non-locality of absorbers. See §2.
4. Smaller technical defects in §§4–7 and the related-work section. See §3.

None of the fixes below needs a new proof. All the Lean statements already
exist.

## 1. The criterion mismatch (submission-critical)

### 1.1 What the Lean development actually proves

| Name | Lean | Content |
|---|---|---|
| P | `Paper1/RALinearizability.lean:33` `VersionsRALinearizable` | per version and query, ∃π, a permutation of E respecting `paperOrder` (= Def. 4.1 with global commutation), admitted by Spec |
| V | `Paper1/EventBridge.lean:66` `EventVersionsSpecificationRA` | P plus π respects `projectedSpecVisibility`: `vis a b ∧ ¬ Spec.Commutes a b` |
| S | `Paper1/InvariantOrder.lean:77` `InvariantOrder.VersionsRA` | V with commutation replaced by commutation on a domain `Inv` that is `Closed` (initial state, issued updates, merge of arbitrary Inv states); `versions_universal` proves S(True) = V |

The counted endpoints, as audited by the Codex review (`claude_codex.md`,
21:52 entry): plain RGA concludes V; embedded RGA, sided RGA and FugueMax
conclude S. The remaining rows are not yet classified.

In all three criteria the specification sees **whole events**
(`projectedLabels id`), not payload-only operations.

### 1.2 Defects in the paper's `Laws` (ralin.tex l.155 onward)

**L1 (verified). `o₁ ≠ o₂` in rc-non-comm breaks Theorem 4.3.** Lean's
`RestrictedLaws.noncomm_exact` (`RestrictedReplay.lean:37`) ranges over
events and has no exemption. Combined with `no_chain`, it forces every pair of
same-operation events to commute. The paper's version lets two concurrent
events with the same label fail to commute while lo leaves them unordered. Two
linear extensions can then fold to different states, and the proof sketch of
Thm. 4.3 ("rc-non-comm and cond-comm ensure that swapping adjacent unordered
events does not change the state") does not go through. Such pairs exist:
`PolicyObstructions.Queue.same_payload_noncommute` has two `enq 7` events that
do not commute.
*Fix:* delete "∧ o₁ ≠ o₂". State that the law then implies every operation
commutes with itself, which is Neem's original reading.

**L2 (verified). The operation-level Laws are unsatisfiable for the queue
and MVR.** `PolicyObstructions.{Queue,MVR}.no_restricted_policy`: commutation
depends on payload metadata and timestamps (`metadata_control`), so no
operation-only rc can be exact. Rows built on these types cannot be instances
of §4 as written.
*Owed:* identify which table rows use `Instances.Queue` or `MVRLive` and
which criterion they conclude.

**L3 (verified). spec-non-comm fails for plain RGA.**
`RGAConcretePort.globalCompatibility_impossible` (l.69). `RGAM_all_comm` makes
every implementation pair commute, while the strict identified spec
distinguishes insert/delete orders. Hence Thm. `thm:certified`, which assumes
`Laws(D, Spec)`, does not apply to the paper's own RGA example.

**L4 (verified). Spec labels.** `ops(π)` (ralin l.138) strips the timestamp
and replica. The RGA example's label `addAfter(t, ℓ)` needs t. The paragraph
that introduced a label projection is commented out (ralin l.140–153), and the
appendix specifications are written over (t, r, o) labels.

**L5 (verified). Causal versus weak closure.** Def. 4.1, Thm. 4.3 and
Def. 4.4 require E to be causally closed. §5 applies `can` and `lo` to weakly
closed sets: `E₁∖{e}`, `↓e∖{e}`, and the `Admissible` predicate. If e is
lo-maximal in E₁ ∪ E₂ but has a commuting vis-successor in E₁, then
`E₁∖{e}` is not causally closed and `can` is undefined there.
*Fix:* state Def. 4.1, Thm. 4.3 and Def. 4.4 for weakly closed sets.

### 1.3 Recommended alignment (decision)

- **(a) Recommended.** Adopt **V** in Def. 4.5. Clause 1 becomes: π is a
  linear extension of `(E, lo^C_E ∪ svis_E)`, where
  `svis_E = {(a,b) ∈ E² | a vis b ∧ ¬(a ↔_S b)}`. Remove spec-non-comm from
  `Laws`. The buggy OR-set paragraph (identity `rem`) survives almost
  verbatim as the motivation for `svis`: the witness `rem · add` violates
  `vis(add, rem) ∧ add ↮_S rem`.
  Then present **S** as a stated extension in §7. That means defining
  `↔_Inv`, `Closed(Inv)`, the Inv-scoped Laws and VCs, and one theorem:
  Thm. 4.3 through Lemma 5.2 hold with `↔_Inv` when Inv is Closed.
  The implementation section already refers to this "scoped certified-history
  extension", which the paper currently never defines.
- **(b)** Keep the current `Laws` and restrict the claims to rows that
  satisfy them. That removes RGA and its variants, plus the queue/MVR rows,
  which is about a third of the table.

**Motivation for each layer (proposal).** `globalCompatibility_impossible`
motivates V: a natural sequence specification cannot be combined with a
global spec-non-comm law. The raw-order obstructions
(`CertifiedFugueRawOrderObstruction.lean`) and L2 motivate S. This mirrors
§2: global versus indexed, applied to the laws rather than to the order, and
it makes the mismatch a contribution rather than a caveat.

**Labels (proposal, which also resolves the RGA-spec question).** Say that
labels are events. A natural specification may ignore t and r, as the OR-set
specification does. The RGA specification reads t only as the identity that
the client's insertion names, never as replica bookkeeping. This answers the
reviewer question "why is an identity-carrying RGA specification natural
after §2.2 criticises Wang?".

### 1.4 Table support (proposal)

Add a criterion column (P / V / S) to `implementation_table.tex`, generated
by `render_table.py` from the type of each ledger endpoint's conclusion so
that it cannot go stale. Prose qualification alone does not let a reader
tell which rows instantiate which theorem.

## 2. Section 2 (motivation.tex) under the correct reading of Neem

**Fact (verified).** Neem Def. 3.5 (`lin.tex:296`): one relation `lo_C` over
all events of configuration C. An rc edge is dropped if an absorber exists
*anywhere in C*. Neem Def. 3.9 (`lin.tex:400`): for every head replica,
∃π extending the restriction of that same `lo_C`, with `π(σ₀)` equal to the
state. Neem does not require the sequences to be projections of one total
order. Wang (`_references/RA-Linearizability/main.tex:1696–1709`) does use one
total sequence.

**S2.1 (verified).** l.179, "Both these representations are identical": false.

**S2.2 (verified).** `fig:defeater` is RA-linearizable under Neem. At the
final configuration both rc edges are absorbed and `lo_C` keeps only
`A_p→R_p` and `A_q→R_q`. Then v6 is explained by `A_p·R_p·A_q` and v7 by
`A_q·R_q·A_p`. The text at l.360 and l.384–388, and the summary ("the
original OR-set cannot be shown correct with respect to the natural set
specification"), hold only for a single global *sequence* (Wang).

**S2.3 (verified). The forced cycle is the right argument against Wang.**
Take `q = rd_a` at v6 and at v7, both returning true. State these reads
explicitly, because the figure shows states, not reads. Given
`A_p vis R_p`, the only order of `{A_p, R_p, A_q}` with `rd_a = true` is
`A_p·R_p·A_q`, which forces `R_p < A_q`. Symmetrically, v7 forces
`R_q < A_p`. Adding visibility gives `A_p < R_p < A_q < R_q < A_p`. The
argument uses only vis and the reads, not rc. Replace "Every other
candidate sequence would also fail in a similar way" (l.386) with it.

**S2.4 (proposal). The argument against Neem: locality.** `lo_C` at v6
depends on R_q, an event v6 has not seen. Before R_q is issued, `lo_C`
contains `R_p→A_q`; afterwards it does not. So the relation that explains a
version changes when unrelated replicas act. Once R_q exists it no longer
determines the fold of E(v6): `A_p·A_q·R_p` ↦ {} also extends it. The
event-set-indexed `lo^C_E` repairs exactly this. The argument needs no SEC
countermodel.

**S2.5 (verified). Weaken ralin l.294.** "The original definition does not
ensure SEC" needs a countermodel: an implementation satisfying Neem's laws
and an execution with two versions over E(v6) holding different states. What
Fig. 2 establishes is that the restriction of `lo_C` to E(v6) does not
determine the fold.

**S2.6 (proposal). Rewrite of l.390, "root cause".** Use a two-sided
diagnosis. A global total sequence is too strong (the cycle). A global partial
relation with configuration-wide absorbers is non-local and does not
determine states (S2.4). The repair indexes the relation by the event set
being explained. Suggested lead sentence: "Wang fixes one total sequence;
Neem fixes one partial relation `lo_C` for the whole configuration; we index
the relation by the event set being explained."

**S2.7 (verified). The bottom-up paragraph (l.451 onward) is misattributed.**
"This becomes possible due to the presence of a global linearization order"
is wrong. Under Neem's own `lo_C`, both branch witnesses are forced by their
states (v6 = {(a,2)} forces `A_p·R_p·A_q`; v7 forces `A_q·R_q·A_p`), both end
in an add, and v8 = {} needs a final remove. Peeling the last event of a
branch fails regardless of the global order.
*Proposed:* "Bottom-up linearization assumes that some linearization of the
merged version ends with the last event of a branch's linearization; Fig. 2
shows that this can fail even when every version is correctly linearized."
Keep the commented-out claim that none of Neem's Fig. 12 rules applies out of
the paper until it is checked, since it bears on Neem's soundness argument.

**S2.8 (verified).** The `fig:defeater` caption attributes the per-version
annotations to Neem. They are `lo^C_{E(v)}` (Def. 4.1): for example
`R_p→A_q` at v6, which Neem's `lo_C` would not contain.

**S2.9 (proposal).** Keep concrete and abstract states visibly apart: σ for
tagged sets, φ for the abstract set, as `seq_spec.tex` already does.
Section 2 is risky at l.381, where "would exactly result in the state
{(a,2)}" sits next to "belongs to the natural specification".

## 3. Other technical defects (verified)

- **seq_spec, condition (iii) is in the wrong direction.** As written ("if
  `α(σ) --q⇒b--> α(σ)` then `query(σ,q) = b`"), it holds vacuously when the
  spec admits no answer at α(σ), and so does not give
  `ops(π)·(q ⇒ query(...)) ∈ Spec`. Def. 4.2 assumes neither totality nor
  determinism. *Fix:* require `α(σ) --q ⇒ query(σ,q)--> α(σ)`. Also,
  `ρ(φ₀)` as "the state it reaches" needs determinism; use relational
  wording otherwise.
- **The issuance RGA example** (issuance.tex) has three problems:
  - It uses a retained list with tombstones and membership-guarded deletion.
    The certified `RGAEventSpec` (appendix §RGA) uses a live list plus an
    allocation registry, live-anchor insertion and unconditional deletion.
  - Its claim that "inserting after the anchor does not commute with adding
    the anchor" is false for the certified implementation (`RGAM_all_comm`).
  - It concludes adequacy from enabledness alone. Read agreement also needs a
    chosen witness order: fresh insertions in increasing timestamp order, as
    the `RGASequential` bridge does. Two inserts after the same anchor are
    both enabled in either order but yield opposite lists.

  It also needs an explicit exception for the root anchor 0. *Fix:* rewrite
  to the appendix specification with this witness argument.
- **ralin l.296:** `[A_q,A_q,R_p]` should be `[A_q,A_p,R_p]`.
- **proof_strategy:**
  - The Join lemma (l.527) says "supported and weakly closed", but "supported"
    is defined only in a commented-out block. Use `E_i ⊆ 𝓔_C`.
  - The VC4 prose says "the second branch (state B) is simply the downset of
    e". B is the base (the state of `↓e∖{e}`), and e(B) is the branch.
  - Typos: "it's pre-conditions", "linearing".
- **related_work.tex** says Neem "requires a single global order … some
  executions do not admit such an order". Per §2, `lo_C` always exists; the
  defect is non-locality and non-determinacy. It also declares
  `\label{sec:conclusion}` while `conclusion.tex` emits an empty
  `\section{Conclusion}` with the same label: a duplicate label and an empty
  section in the PDF.
- **references.bib** has `Notion` and `NotionCRDTBlog` for the same blog
  post. The introduction cites `NotionCRDTBlog` and the related-work section
  cites `Notion`, so the bibliography lists the post twice.

## 4. The locked introduction (risks only; no edits proposed)

- "a global order satisfying the requirements of every version need not
  exist". This is defensible only if §2 defines the requirements as including
  the version-local rc edges (S2.4, S2.6).
- "Such methods rely on a global order, which our definition does not
  require". This conflicts with S2.7.
- "We prove that all valid linearizations … produce the same state". This is
  true only after L1 is fixed.
- l.72: "Apart from of this" is a typo.

## 5. Table, attribution and layout decisions

- **Sided RGA (verified).** It puts RGA's sibling order on Fugue's two-sided
  tree: an insert stores a side bit and an immutable (side, Δ) path, with no
  right origin. Same-side siblings sit newest-nearest-anchor: decreasing Δ on
  the right, increasing Δ on the left. Fugue orders same-side siblings by
  ascending id, so `Fugue.lean:1036 fugue_not_maximally_noninterleaving`
  applies. It is not FugueMax, which orders right siblings by right origin and
  has its own row. `sided_allR_read_eq` equates the all-right instance with
  embedded RGA; the link to published RGA goes through further theorems. Do
  not cite Kleppmann et al. 2019, which Weidner and Kleppmann describe as
  flawed and from which Sal does not derive.
  *Recommended:* `Sided RGA~\cite{Roh,FugueMax}`, with the footnote "an
  adaptation of RGA to the two-sided tree of Weidner and Kleppmann;
  same-side siblings are ordered newest-nearest-anchor; neither Fugue nor
  FugueMax (separate row)."
- **Sided Peritext (approved by KC; done by Codex).** One rendered row. The
  core is the same Σ, do and merge with a component query, so it is a proof
  layer. The cells are the deduplicated union of the two dependency closures.
- **Priority queue (integrated by Codex).** Label it a Sal variant
  (sum of retained increments), not the Internetware 2023 per-add-record
  Most-Change-Win algorithm. The policy is same-element remove/add.
  `rmv_max` is a local client composition (get_max followed by remove(id)),
  not an atomic replicated update, and must not be listed as a verified
  update operation.
- **Figure 1 (approved by KC; applied).** The OR-set implementation is set
  as two side-by-side `algorithmic` minipages in a full-width float. It is
  five lines tall instead of nine and has no overlap. The wrapfigure trial
  was rejected because it overlapped the footnote and running foot and left a
  three-line text column.
- **Appendix size.** About 40 pages (pp. 28–67). Check the venue's rules;
  it may need to ship as a separate supplement.

## 6. Suggested order of work

1. Local fixes that change no claim: L1, L4, L5, and everything in §3.
2. **Decision:** alignment (a) or (b) from §1.3. With (a), write V into
   Def. 4.5 and add S as a §7 extension, then add the generated criterion
   column (§1.4).
3. **Decision:** the Section 2 rewrite (S2.1–S2.9), with the matching fixes
   to the related-work section and the `fig:defeater` caption.
4. A final consistency pass of the locked introduction against the rewritten
   §2 (§4 risks).

## Evidence index

- Neem: `_references/Neem/lin.tex:296` (Def. lin-relation), `:400`
  (Def. lin). The published OOPSLA'25 PDF, Defs. 3.5 and 3.9, pp. 111:13–14,
  was cross-checked by Codex.
- Wang: `_references/RA-Linearizability/main.tex:1696–1709`.
- Lean criteria: `Sal/MRDTs/Paper1/RALinearizability.lean:24-38`,
  `EventBridge.lean:66`, `InvariantOrder.lean:14-91`,
  `RestrictedReplay.lean:36-80`, `ProjectedCriterion.lean:13-26`,
  `SpecificationVisibility.lean`.
- Obstructions: `PolicyObstructions.lean`,
  `RGAConcretePort.lean:69`, `CertifiedFugueRawOrderObstruction.lean`.
- Sided RGA: `Instances/SidedEmbedRGA.lean:74-78`,
  `SidedEmbedRGA_Intent.lean:140-147`, `Fugue.lean:1036`,
  `experiments/paper-implementation/source-audit.md:34`.
- Review exchange: `claude_codex.md` (Claude–Codex thread, 2026-10-14).
