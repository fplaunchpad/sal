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
| Convergence (Thm A.1, §A.3) | 24 RA-linearizability VCs | Pointwise equality on the four state components; per-replica snapshot rather than op-log consistency. |
| Causality preservation (§A.1) | Framework-level assumption | Sal's state-based model assumes causal delivery; the VCs verify the local reconciliation rule. |
| Intention preservation (§A.2, 8 examples) | Characterization theorems in `Peritext_ReadSide.lean` | See the table below. |

## Intent-preservation: paper examples ↔ Lean theorems

| Paper | Section | Lean theorem | Status |
|---|---|---|---|
| Ex 1 — insertion within a span | §3.1, §A.2 | `covered_interior` + `covered_interior_propagate` | **Sound approximation.** Captures the afters-chain case; full RGA-visible-order fidelity is deferred. |
| Ex 2 — overlapping same-type Adds | §3.2, §A.2 | `partial_overlap_all_adds_formatted` | ✅ |
| Ex 3 — different mark types coexist | §3.2, §A.2 | `different_type_adds_coexist` | ✅ |
| Ex 4 — overlapping same-type different-values (colors) | §3.2.1, §A.2 | Implicit via `mark_beats` LWW branch | Trivial standalone corollary of `add_beats_remove` — not yet spelled out. |
| Ex 5 — conflicting bold vs non-bold | §3.2.1, §A.2 | `add_beats_remove` (positive) + `no_add_cover_implies_unformatted` (negative) | ✅ Deliberate departure on the priority rule — see below. |
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
`readRichText` is a `OpId → Option (ℕ × (ℕ → Bool))` function —
stronger as a specification (pure function of state) but less
ergonomic for downstream consumers. The list form requires an RGA
traversal which is the same dependency we'd need for complete Ex 1
fidelity; see below.

## Deferred work (follow-ups)

**Full RGA-visible-order formalization.** Needed to close the
remaining gap in Ex 1: the paper's "within the span" applies to any
character in visible-traversal order between `startId` and `endId`,
not just those reachable via an afters-chain. A chain-form
`covered_interior_of_reach` theorem was drafted and backed out; its
proof runs into Lean's induction-hypothesis generalization in a way
that needs careful motive handling. The full traversal relation
would also unlock a list-form `readRichText`.

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
  counterparts; the MRDT's `eq` lifts to functional equality more
  cleanly, which makes `readRichText_convergent` a three-line proof
  vs. the CRDT's simp-heavy rewrite chain.
- `docs/porting-op-based-crdts.md` — general recipe; Peritext is
  the worked example throughout.
