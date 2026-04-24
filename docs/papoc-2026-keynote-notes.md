# From Convergence to Confidence — honest assessment

*Companion notes for the PaPoC 2026 keynote.*

## Opening frame

The title draws a line between two claims we make about verified CRDTs. *Convergence* — two replicas that have received the same ops agree on state — is what most verification efforts, including our own PLDI22 Certified MRDTs and the Sal framework, have historically produced. *Confidence* is what a practitioner actually needs: assurance that the verified artifact does what the paper says it does.

The gap between the two is bigger than we let on in prior papers. This week's work on the Peritext read-side is the sharpest evidence of that gap we have.

## The vacuousness gradient

RA-linearizability VCs are not uniformly meaningful across RDTs. Some proofs engage with the data type's semantic content; others prove near-trivial commutativity of grow-only state. Across the Sal suite:

| Tier | Character | Examples | VCs prove... |
|---|---|---|---|
| **A** — Convergence ≈ Correctness | State *is* the semantic content | LWW-Register, Max/Min-Register, PN-Counter, Bounded-Counter, MAX-Map | Lattice-join commutativity / arithmetic — real content |
| **B** — Substantive convergence | Merge does non-trivial computation | Multi-Valued-Register, LWW-Map, LWW-Element-Set | Conflict collection / tombstone handling — real content |
| **C** — Vacuous convergence | State is grow-only bag; meaning lives in the read | OR-Set, OR-Set-Efficient, Enable-Wins-Flag, Shopping-Cart, Grow-Only-*, RGA, Add-Win-PQ, **Peritext** | Grow-only union / max — near-trivial |

Roughly half the Sal suite — and all of the most *interesting* RDTs — sit in Tier C. For Tier C, "verified" without read-side theorems is overclaiming. The 24 convergence VCs prove union commutativity; the actual semantics (which characters are formatted, which elements are in the set, which items are at the head of the priority queue) lives in a read-side function that the convergence proof never mentions.

This is orthogonal to op-based vs state-based. An op-based Tier-C CRDT would be equally vacuous if its proof characterizes only order-independence of ops without saying what those ops *mean* under the read.

## The Peritext case

Peritext is the cleanest Tier-C example in the suite. Four grow-only state components: `chars`, `afters`, `deleted`, `marks`. The 24 VCs prove each converges under union. None of them constrain how those components combine to produce formatted rich text.

Before this week, the Peritext formalization said nothing about:
- Whether `startSide` / `endSide` anchor bits were load-bearing (they weren't — stored in state, never consulted).
- Whether the `isAdd` / `mark_opId` priority rule resolved overlapping marks correctly.
- Whether tombstoning a character preserves the formatting of everything else.
- Whether concurrent inserts at a span boundary fall inside or outside per the paper's expand/contract semantics.

What landed this week on both CRDT and MRDT sides:

- **`visible_lt` inductive** — four-rule characterization of RGA visible order (parent-child, sibling via `opid_max`, left-descendant-of-sibling, transitive).
- **`in_span_visible`** — paper-faithful visible-order span-membership predicate, replacing a buggy `in_span_boundary` approximation (see next section).
- **Ex 1–8 intent-preservation theorems** — every example in paper §A.2 that can be captured in our current model. Ex 4 (color-LWW within same `markType`) remains a principled gap pending a state-shape change.
- **`bold_expand_reach`** — closes the Ex 7 bold-expand gap via opId comparison: characters reachable from `endId` through afters-chains where every step post-dates the mark are in the span.
- **`wf_afters`** acyclicity invariant — yields `visible_lt` irreflexivity / antisymmetry and drops an explicit hypothesis on the Ex 8 negation.
- **`is_rga_traversal` / `readRichText_list`** — Prop-valued list-form spec for downstream consumers.
- **Removal of ~800 lines** of an earlier buggy parallel track built on `in_span_boundary`.

Net effect: Peritext now carries analogues of both the paper's §A.1 convergence and §A.2 intent-preservation. The 648 VCs across the Sal suite are a *substrate* for correctness, not correctness itself. This week lifted exactly one of the Tier-C RDTs (Peritext) from substrate-only to substrate + intent-preservation.

## Specification drift — the cautionary tale

The first read-side predicate I wrote for Peritext was `in_span_boundary`. It looked plausible: four boundary cases (c = startId, c = endId, c is after-startId, c is after-endId), each with a side-bit lookup. I wrote it from a surface reading of §3.3. Proofs went through: Ex 2, Ex 3, Ex 5 positive/negative, anchors-survive-tombstones — ~400 lines of theorems across CRDT and MRDT, all kernel-checked.

The predicate's `after_of c endId → endSide` clause encoded the **opposite** of what paper §3.3 specifies. Under `endSide = true` (bold-expand-after), the predicate *included* post-endId inserts. Paper §3.3 says such inserts should be *excluded* under link-contract, and the corresponding bold-expand case needs opId comparison that the predicate didn't do.

I didn't catch it from proofs. Proofs validate the PROOF, not the SPEC. The predicate was self-consistent; the theorems were true about the predicate; nothing in the proof obligation catches "does this predicate match the paper." The bug was caught only when I wrote `in_span_visible` as an alternative and noticed the two predicates disagreed on Ex 8.

This is the verification analogue of "your tests pass but the code is wrong." Writing more proofs doesn't help. The fix requires spec validation — a separate activity from proof checking.

## Where SMC fits

Optimal stateless model checking isn't redundant with proofs; it fills a specific gap: **spec validation**.

- **SMC:** enumerates short executions (3 replicas, 4 ops). For each resulting state, checks whether a read-side predicate agrees with a reference implementation. Fast (seconds to minutes). No universal claim.
- **Proofs:** verify a property holds for all executions given a spec. Slow (sessions to weeks). Universal.

The two compose in a pipeline:

1. Write the read-side predicate.
2. Validate it with SMC against thousands of short traces and a trusted reference (for Peritext: the TypeScript reference implementation from the paper's artifact).
3. Commit proof effort to the validated predicate.

The `in_span_boundary` bug would have been caught by SMC in minutes. Instead we caught it via careful paper re-reading days into proof writing, after ~400 lines of proof had gone through against the wrong predicate. The scaling argument for SMC: it makes spec-validation cheap enough to do routinely, instead of relying on the rare researcher who re-reads §3.3 with a skeptical eye after the proofs look complete.

Optimal SMC specifically (reducing redundant schedule exploration) is what makes this tractable at useful scales — for Peritext, the read-side state space branches on op interleavings in ways that naïve enumeration would not finish. OSR brings this down to something a CI job could run.

## Agent–human collaboration — honest assessment

This week was heavy AI-human collaboration. Claude (Anthropic's assistant) did substantial lifting; KC did substantial correcting. An honest breakdown:

**What Claude was good at:**
- Translating paper prose into Lean predicates (`visible_lt` inductive rules, `bold_expand_reach`, `is_rga_traversal`).
- Mechanical CRDT → MRDT ports. Every theorem ported with sub-linear effort.
- Re-proving downstream when a predicate definition changed (we redefined `in_span_visible` mid-session and reclosed everything).
- Writing parameterized theorems universally quantified over states, opIds, replicas — not small concrete traces.
- Proof structure: `rcases`, `split_ifs`, manual induction on inductives where SMT didn't apply.
- Closing roughly 85 by-sal sorries / Blaster-admits across the suite in the past week (OR-Set, Add-Win-PQ, Shopping-Cart, RGA, etc.), genuinely tightening the kernel-checked fraction.

**What Claude was bad at (caught by KC's pushback):**
- **Spec design.** The `in_span_boundary` bug came from a Claude-written predicate. Writing a plausible-looking predicate without cross-checking against the paper's small examples is a failure mode the model does not self-correct.
- **Honest framing.** Twice in this session I claimed Ex 7 bold-expand was "inherently state-based-impossible" and produced hand-wavy arguments. KC pushed back ("does op-based assume a global clock? I don't understand."); on re-examination, the rule uses opId comparison, which is state-recoverable. Overclaiming impossibility to avoid doing work is a real failure mode.
- **Scope estimation.** I claimed 6–10 hours for recursive-traversal existence; realistic estimate under the current framework (where `set α := α → Bool` doesn't enumerate) is 15–20. Better to be honest and descope than oversell and underdeliver.
- **Knowing when to stop.** Left alone, agents extend proofs past need. Human judgment anchors scope.

**The pattern that worked:**

1. Human reads paper, asks sharp question: *"why is `startSide` never consulted?" / "bag convergence is vacuous, isn't it?" / "is op-vs-state really fundamental, or do you just mean opId comparison?"*
2. Agent investigates, proposes an answer.
3. Human pushes back on fuzzy claims.
4. Agent refines or retracts.
5. Repeat.

The human isn't micromanaging. They're posing questions that reframe the work, and catching slippage when the agent overreaches. The agent does the execution. This is a natural specialization of labor: proofs and refactors for the agent, judgment and honest framing for the human.

## Push-button is a spectrum

The "push-button" branding covers a range of automation levels, and the honest story is a four-tier breakdown:

| Layer | Automation | Example |
|---|---|---|
| Convergence VCs (Tier A/B) | Push-button via `by sal` | LWW-Register |
| Convergence VCs (Tier C) | `by sal` + Blaster-admit fallback; occasional kernel-reconstruction needed | OR-Set-Efficient |
| Read-side convergence | Mostly automated via `funext` + `grind` on pointwise state equality | `readRichText_visible_convergent` |
| Intent-preservation theorems | Human-directed, agent-assisted; SMT helps but doesn't close | `bold_expand_in_span_visible` |
| Spec design | Human, with agent helping to draft | `in_span_visible` predicate, `bold_expand_reach` |

TCB gradient is orthogonal: kernel-checked > Blaster-admit (Z3-validated, TCB-enlarging) > tested / SMC'd (no formal guarantee). This week closed ~85 Blaster-admits across the suite (OR-Set MRDT: 17 of 20; OR-Set-Efficient MRDT: 17 of 21; Add-Win-PQ MRDT: 18 of 23; RGA MRDT: 9 of 9; several smaller CRDT closures). The remaining ~12 Blaster-admits are concentrated in a few specific files and are listed in the README.

## What's still honestly open

- **Existence of `is_rga_traversal`** for every state. Requires either a framework-level enumeration extension to `Set_Extended` or per-theorem `Finset` hypotheses. Current spec is usable but non-existential.
- **`wf_afters` preservation** under `do_` and `merge`. Holds for states reachable from `init_st` via finite op sequences, but needs an inductive trace proof.
- **Tombstone-scanning on insert** (Peritext §4.2.2). Designed in `docs/tombstone-scanning-design.md`; 8–15 hour multi-session effort; breaks four-component independence and requires re-verifying ~15 VCs.
- **Ex 4** (color LWW on same `markType`). Requires adding a `markValue` field to `MarkOp` — state-shape change; mechanical VC re-proofs expected.
- **Tier-C RDTs beyond Peritext.** OR-Set, RGA, Add-Win-PQ, Shopping-Cart all have convergence VCs but no paper-faithful read-side theorems. Each is a Peritext-shaped effort (not as large; the read-sides are simpler).

## Closing

The talk's thesis: convergence is necessary, not sufficient. For Tier-C RDTs — which is most of the interesting ones — the semantic content of the data type lives in the read, and the convergence proof doesn't engage with it.

Push-button tooling covers convergence reliably. Read-side theorems are semi-automated with agent assistance. Spec design stays human and is the hardest layer. SMC fits as the spec-validation step that makes the pipeline robust to the failure mode demonstrated by the `in_span_boundary` bug this week.

The honest claim for a verified CRDT is not *"proven correct"* but:

> *Proven convergent on these state components, with these read-side semantic theorems against this paper-faithful predicate, validated against these SMC trace-level examples, with these open follow-ups.*

That's a mouthful. It's also the claim that deserves confidence.
