# Peritext in Sal vs. the paper

Cross-reference between the Lean formalization in
`Sal/{CRDTs,MRDTs}/Peritext/` and the CSCW 2022 paper:

> Geoffrey Litt, Sarah Lim, Martin Kleppmann, and Peter van Hardenberg.
> *Peritext: A CRDT for Collaborative Rich Text Editing*. Proc. ACM
> Hum.-Comput. Interact. 6, CSCW2, Article 531 (November 2022),
> 36 pages. <https://doi.org/10.1145/3555644>

This document is a living map: where the Lean matches the paper,
where it deliberately departs, and where follow-up work is flagged.

## Formalization target

The paper describes an **op-based** CRDT; our Lean is a **state-based**
reformulation. The two are equivalent in expressive power (paper §2.3),
but the correctness criteria land in different places:

| Paper | Our Lean | Notes |
|---|---|---|
| Convergence (Thm A.1, §A.3) | 24 RA-linearizability VCs (per variant) | Pointwise equality on each state component. CRDT has four components (`chars : map`, `afters : map`, `deleted : map`, `marks : set`); MRDT has three (`chars : set CharRec`, `removed : set OpId`, `marks : set`). Per-replica snapshot rather than op-log consistency. Both variants are fully sorry-free. |
| Causality preservation (§A.1) | Framework-level assumption | Sal's state-based model assumes causal delivery; the VCs verify the local reconciliation rule. |
| Intention preservation (§A.2, 8 examples) | Characterization theorems in `Peritext_ReadSide.lean` (mirrored on both CRDT and MRDT sides) | See the table below. |

## Intent-preservation: paper examples ↔ Lean theorems

| Paper | Section | Lean theorem | Status |
|---|---|---|---|
| Ex 1 — insertion within a span | §3.1, §A.2 | `insert_within_span_in_span_visible` (both sides) + `in_span_visible_propagate` / `_of_reach` | ✅ Paper-faithful via visible-order; caller provides the right-side bound from RGA geometry in their specific scenario. |
| Ex 2 — overlapping same-type Adds | §3.2, §A.2 | `partial_overlap_all_adds_formatted_visible` | ✅ |
| Ex 3 — different mark types coexist | §3.2, §A.2 | `different_type_adds_coexist_visible` | ✅ |
| Ex 4 — overlapping same-type different-values (colors) | §3.2.1, §A.2 | **Not expressible in our model** | Our `MarkOp` has `markType : ℕ` but no per-mark `value` field. Ex 4's resolution (LWW among distinct color values of the same markType) requires representing both "red" and "blue" as instances of the same markType, which we can't. Encoding each color as a distinct markType would make `different_type_adds_coexist_visible` apply — but that's the opposite of Ex 4's intent. |
| Ex 5 — conflicting bold vs non-bold | §3.2.1, §A.2 | `add_wins_over_concurrent_remove_visible` (positive) + `no_add_cover_implies_unformatted_visible` (negative) | ✅ Deliberate departure on the priority rule — see below. |
| Ex 6 — overlapping comments via distinct markType | §3.2.2, §A.2 | Follows from `different_type_adds_coexist_visible` | ✅ (Comments encode each instance with a unique `markType`; the theorem then applies.) |
| Ex 7 — bold-boundary insertion expands | §3.3, §A.2 | `ex7_bold_older_sibling_in_span` (cross-sibling case) + `bold_expand_in_span_visible` (post-endId region) | ✅ Two complementary results: the cross-sibling case (insert lands before `endId` in visible order) uses the standard visible-order bound; the post-`endId` bold-expand region uses `bold_expand_reach`, which identifies afters-descendants of `endId` reachable via chains of post-mark-opId characters (paper's §3.3 "grab new inserts at the after-side" encoded via opId comparison). |
| Ex 8 — link/comment-boundary insertion doesn't expand | §3.3, §A.2 | `ex8_link_descendant_visible_lt_endId` (positive) + `ex8_link_descendant_not_in_span_visible` / `_of_wf` (full negation, link case) | ✅ Under link semantics (`endSide = false`), afters-descendants of `endId` are correctly excluded. Full negation uses the `wf_afters` acyclicity invariant. |
| Table 1 — "Can marks overlap?" | §3.4 | Emergent from `formatted_visible` being per-`markType` | ✅ |
| Table 1 — "Do marks expand?" | §3.4 | Captured by Ex 7 / Ex 8 visible-order demos above | ✅ |

Plus one additional theorem not tied to a specific paper example:

- `anchors_survive_tombstones_visible` — tombstoning any character
  leaves the formatting of the other visible characters unchanged.
  Implicit in the paper's §4.4 discussion of tombstoned anchors; we
  state it as a parameterized theorem over all states.

## Deliberate departures

**Priority rule.** The paper §4.4 prescribes pure LWW by `opId` — the
mark op with the highest `opId` wins, regardless of its `isAdd` bit.
We instead use **"Add beats Remove, then LWW by opId"** (`mark_beats`
in `Peritext_ReadSide.lean`). The paper itself calls Ex 5's outcome
"arbitrary deterministic," so both rules satisfy the paper's
*intent*; our rule picks the more user-friendly deterministic branch
— concurrent formatting isn't silently overridden by a stale
`RemoveMark` that happens to have a higher `opId`. The `mark_beats`
docstring documents this decision in full.

**List vs. per-char `readRichText_visible`.** The paper (§4.4) presents the
rendered document as a list of `{text, format}` spans. Our
`readRichText_visible` is instead a per-character function whose
exact signature depends on the variant:

- **CRDT:** `OpId → Option (ℕ × (ℕ → Bool))` — `(codepoint,
  markType → is-formatted)` per visible char.
- **MRDT:** `OpId → Option (ℕ → Bool)` — just the formatting
  function; the codepoint lookup is skipped because in the MRDT's
  set-of-triples `chars` representation, payload lookup at an `OpId`
  requires `Classical.choose` on an existential.

The list form is available as `readRichText_list` (both sides), a
Prop-valued spec via `is_rga_traversal`: callers construct the
traversal externally and prove it satisfies the spec. See
*Still pending* below for the existence-theorem follow-up.

## Infrastructure summary

The read-side is built on the RGA visible-order relation `visible_lt`
(four-rule inductive: parent-child, sibling, left-descendant-of-sibling,
transitive closure) and its reflexive closure `visible_le`. On top of
those:

- `in_span_visible` — paper-faithful covering predicate with side-bit
  refinements on both boundaries.
- `mark_wins_visible` / `formatted_visible` / `readRichText_visible`
  — read-side projection built from `in_span_visible` plus
  `mark_beats` (Add-beats-Remove then LWW).
- `is_rga_traversal` + `readRichText_list` — list-form presentation
  as a Prop-valued spec; callers construct a traversal externally
  and prove it satisfies the spec (the framework's `set α := α → Bool`
  doesn't natively enumerate; see `docs/list-form-readrichtext-design.md`).
- Congruence lemmas (`_eq_of_afters_eq` family on CRDT,
  `_eq_of_chars_eq` on MRDT) lift pointwise state equality through
  the inductive relations.
- Insert-monotonicity chain (`after_of_preserved_under_insert`,
  `afters_reach_preserved_under_insert`, `visible_lt_preserved_under_insert`,
  `visible_le_preserved_under_insert`) powers the Ex 1 insert-within-span
  closure.
- `wf_afters` — state-level acyclicity invariant on `afters`, with
  `visible_lt_asymm_of_wf` and `visible_le_antisymm_of_wf` as
  corollaries.
- `bold_expand_reach` — paper §3.3 bold-expand region past `endId`,
  characterized by afters-chain reachability through post-mark-opId
  characters only. Embedded as the second disjunct of `in_span_visible`'s
  `endSide = true` right bound.

## Still pending

- **Existence of `is_rga_traversal`** for every state — requires
  either a finite-carrier extension to `Set_Extended` (framework-wide
  refactor) or per-theorem `Finset` hypotheses threaded through the
  read-side. The current spec is usable without existence.
- **Preservation of `wf_afters` under `do_` / `merge`.** Holds
  structurally for states reached from `init_st` but needs an
  inductive trace proof.

### How Ex 7 / bold-expand is captured: `bold_expand_reach`

Paper §3.3's bold-expand rule says: under `endSide = after`, the end
anchor grabs inserts that arrive at or past `endId`. Op-based Peritext
recovers "arrives after the mark" from opId comparisons — every op
carries a `(replica, counter)` opId, and comparing `c.opId` against
`mark.opId` tells you whether `c` was inserted after the mark was
created. This information is state-recoverable (opIds are stored in
state), so bold-expand can be formalized in a state-based model.

We capture this via the `bold_expand_reach` inductive predicate:

```lean
inductive bold_expand_reach (s : concrete_st) (m : MarkOp) : OpId → Prop
  | at_endId : bold_expand_reach s m (mark_endId m)
  | step {c c_parent} :
      after_of s c c_parent = true →
      bold_expand_reach s m c_parent →
      opid_max (mark_opId m) c = c →    -- c.opId > mark.opId
      bold_expand_reach s m c
```

A character `c` is in the bold-expand region iff there's an
afters-chain from `c` back to `endId` where every step's character
post-dates the mark (`c.opId > mark.opId`). Pre-mark siblings break
the chain, so older characters at the boundary are correctly
excluded. New post-mark inserts are correctly included.

`in_span_visible`'s right bound under `endSide = true` is the
disjunction `visible_le c endId ∨ bold_expand_reach s m c` — the
standard link-contract bound OR the bold-expand region.

**Caveat on truly-concurrent inserts.** Two ops that are HB-incomparable
to the mark may have `opId > mark.opId` or `opId < mark.opId` depending
on replica-counter interleaving. Our rule commits to the total order
given by `opid_max`, which matches the RGA sibling tiebreak and is
therefore consistent with how visible order is computed. Replicas
agree on both, so convergence is preserved.

## Paper implementation details not modelled

- **Tombstone-scanning on insert (§4.2.2).** The paper's `Insert`
  scans the marks set when placing a character after tombstones
  that are span endpoints (so "frolicked" lands outside the link
  in Fig 6). Our `do_` has no mark awareness. Adding it breaks the
  four-component independence of our state and would require
  re-verifying the 24 VCs. See `docs/tombstone-scanning-design.md`.
- **Op-set compression at anchor boundaries (§4.3, Algorithm 1).**
  We store a flat `set AnchorAttachment` rather than per-position
  op-sets. Observationally equivalent for convergence; an
  implementation that refactors to op-set form would need to
  re-prove the VCs.
- **Incremental patch emission (§4.5).** UI-layer concern; not part
  of the state-based spec.

## Out of scope

These are acknowledged as future work in the paper itself (§5):

- **Block-level structure** (paragraphs, headings, lists, nested
  blocks).
- **Embedded non-text objects** (images, horizontal rules). Our
  `Insert` carries `ch : ℕ` — a single codepoint — with no block
  or media support.

## Related files

- `Sal/CRDTs/Peritext/Peritext_CRDT.lean` — spec + 24 VCs.
- `Sal/CRDTs/Peritext/Peritext_ReadSide.lean` — read-side projection
  + paper-semantic theorems.
- `Sal/MRDTs/Peritext/{Peritext_MRDT,Peritext_ReadSide}.lean` — MRDT
  counterparts. The MRDT's `eq` is pointwise `==` on each set
  component, which lifts via `funext` + `Prod.ext` to full
  functional equality on the state — making
  `readRichText_visible_convergent` a tidy chain of component-wise
  `funext`s then `rw`, rather than the CRDT's simp-heavy rewrite
  through the `mysel_c` / `contains` / ... abstractions.
- `docs/porting-op-based-crdts.md` — general recipe; Peritext is
  the worked example throughout.
