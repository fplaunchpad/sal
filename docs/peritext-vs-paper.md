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
| Ex 1 — insertion within a span | §3.1, §A.2 | `covered_interior` + `covered_interior_propagate` + `covered_interior_of_reach` | **Sound approximation.** One-step and chain-form propagation both proved; full RGA-visible-order fidelity is the remaining gap. |
| Ex 2 — overlapping same-type Adds | §3.2, §A.2 | `partial_overlap_all_adds_formatted` | ✅ |
| Ex 3 — different mark types coexist | §3.2, §A.2 | `different_type_adds_coexist` | ✅ |
| Ex 4 — overlapping same-type different-values (colors) | §3.2.1, §A.2 | **Not expressible in our model** | Our `MarkOp` has `markType : ℕ` but no per-mark `value` field. Ex 4's resolution (LWW among distinct color values of the same markType) requires representing both "red" and "blue" as instances of the same markType, which we can't. Encoding each color as a distinct markType would make `different_type_adds_coexist` apply — but that's the opposite of Ex 4's intent. |
| Ex 5 — conflicting bold vs non-bold | §3.2.1, §A.2 | `add_wins_over_concurrent_remove` (positive) + `no_add_cover_implies_unformatted` (negative) | ✅ Deliberate departure on the priority rule — see below. |
| Ex 6 — overlapping comments via distinct markType | §3.2.2, §A.2 | Follows from `different_type_adds_coexist` | ✅ (Comments encode each instance with a unique `markType`; the theorem then applies.) |
| Ex 7 — bold-boundary insertion expands | §3.3, §A.2 | `expand_contract_end_after`, `expand_contract_start_after` | ✅ |
| Ex 8 — link/comment-boundary insertion doesn't expand | §3.3, §A.2 | `expand_contract_end_before`, `expand_contract_start_before` | ✅ |
| Table 1 — "Can marks overlap?" | §3.4 | Emergent from `formatted` being per-`markType` | ✅ |
| Table 1 — "Do marks expand?" | §3.4 | Captured by the four `expand_contract_*` theorems | ✅ |

Plus one additional theorem not tied to a specific paper example:

- `anchors_survive_tombstones` — tombstoning any character leaves the
  formatting of the other visible characters unchanged. Implicit in
  the paper's §4.4 discussion of tombstoned anchors; we state it as
  a parameterized theorem over all states.

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

**List vs. per-char `readRichText`.** The paper (§4.4) presents the
rendered document as a list of `{text, format}` spans. Our
`readRichText` is instead a per-character function whose exact
signature depends on the variant:

- **CRDT:** `OpId → Option (ℕ × (ℕ → Bool))` — `(codepoint,
  markType → is-formatted)` per visible char.
- **MRDT:** `OpId → Option (ℕ → Bool)` — just the formatting
  function; the codepoint lookup is skipped because in the MRDT's
  set-of-triples `chars` representation, payload lookup at an `OpId`
  requires `Classical.choose` on an existential.

Both forms are stronger as a specification (pure function of state)
but less ergonomic for downstream consumers than the list form. A
list form requires an RGA traversal, which is the same dependency
we'd need for complete Ex 1 fidelity (see below).

## Deferred work (follow-ups)

**Full RGA-visible-order formalization.** Needed to close the
remaining gap in Ex 1 and to fix a semantic bug in
`in_span_boundary` (see below).

Foundation has landed:

- `visible_lt` / `visible_le` relations defined inductively (four
  rules: parent-child, sibling, left-descendant-of-sibling,
  transitive closure), plus a partial-order API (refl, trans,
  composition) and two derived theorems (`visible_lt_of_afters_reach`,
  `visible_lt_of_cross_sibling`).
- `in_span_visible` — paper-faithful covering predicate using
  `visible_lt` / `visible_le` with side-bit adjustments.
- `mark_wins_visible` / `formatted_visible` / `readRichText_visible`
  — parallel read-side projection using `in_span_visible`.
- One demonstration theorem (`formatted_visible_of_lww_add_winner`)
  showing the migration pattern.

**Still pending:** migrating the rest of the read-side theorems
(`expand_contract_*`, `partial_overlap_all_adds_formatted`,
`different_type_adds_coexist`, `no_add_cover_implies_unformatted`,
etc.) from `in_span_boundary` to `in_span_visible`, and restating
`readRichText_convergent` against `formatted_visible`. This is the
step that closes Ex 1 fully and also repairs the semantic bug noted
below.

### Semantic bug in `in_span_boundary` (use `in_span_visible` instead)

Cross-checking against the paper uncovered a bug in the
`in_span_boundary` predicate's fourth clause:

```
if after_of s c endId then endSide    -- the buggy clause
```

This says: a char `c` inserted as a direct afters-descendant of
`endId` is covered by the mark iff `endSide = true`. But the paper's
semantics at §3.3 (Ex 8, link-no-expand) is the **opposite**: with
`endSide = after` (= `true`), inserts immediately after `endId`
fall **outside** the span.

`in_span_boundary`'s other three clauses are also approximate (the
`after_of c startId` one has a similar mismatch for the
startSide=false interior case). Concretely, the theorems proved
against `in_span_boundary` (e.g., `expand_contract_end_after`) are
true-about-`in_span_boundary` but don't match the paper's intent.

`in_span_visible` does match the paper. A follow-up migration moves
the theorems onto the correct predicate.

**Tombstone-scanning on insert (§4.2.2).** The paper's `Insert`
algorithm inspects the marks set when placing a character after
tombstones that are span endpoints (so "frolicked" lands outside the
link in Fig 6). Our `do_` doesn't have mark awareness; adding this
breaks the clean four-component-independence of our state and
requires the 24 VCs to be re-verified.

**Op-set compression at anchor boundaries (§4.3, Algorithm 1).** We
store a flat `set AnchorAttachment` rather than per-position op-sets.
The two representations are observationally equivalent for
convergence purposes, but an implementation that refactors into the
op-set form would need to re-prove the VCs.

**Incremental patch emission (§4.5).** UI-layer concern; not part of
the state-based spec.

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
  `readRichText_convergent` a tidy chain of component-wise `funext`s
  then `rw`, rather than the CRDT's simp-heavy rewrite through the
  `mysel_c` / `contains` / ... abstractions.
- `docs/porting-op-based-crdts.md` — general recipe; Peritext is
  the worked example throughout.
