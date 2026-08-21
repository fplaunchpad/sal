# Sided Peritext flagship audit

## Result

The production JavaScript and the current Lean flagship implement different
Peritext architectures.

- JavaScript exports `peritextSidedEmbedRGA` as `peritext` and combines a sided
  text kernel with a separate mark store.
- `peritextFlagship` uses `E Γ PeritextElt`. It encodes characters and mark
  boundaries as payloads in one-sided generic EmbedRGA.
- Lean `S Γ` cannot instantiate the fused construction because `SOp.ins` and
  `SRec` fix the payload to `Nat`.
- `marksGC_render_congr` proves state-GC preservation over one-sided `EState
  Nat` and `StablePrefixMap`. It does not state preservation for `SState` or
  the production sided policy graph.

This is a missing proof, not a renaming or certificate-packaging gap.

## Research question

- **Goal:** Prove an end-to-end certificate for the shipped
  `PeritextSidedEmbedRGA` architecture.
- **Candidate claim:** Sided text composed with the mark store satisfies the
  same distributed, local sequential, and state-GC conclusions as the current
  one-sided flagship.
- **Falsifier:** A legal sided history for which the independent rich-text
  editor or the never-collected twin renders differently.
- **Formal oracle:** A new product certificate, rendered sequential theorem,
  and mark-aware extension of `SidedRGA_FuguePolicyGC`.
- **Reality oracle:** Differential traces against
  `runtime/src/datatypes/peritext.js` and `compactibleSidedPeritext`.

## Required proof chain

1. Define the Lean operation/state correspondence for sided text plus the mark
   store used by JavaScript. Do not reuse the refuted rehoming design.
2. Package the existing sided Join theorem and a genuine mark-store theorem
   through the product interface. Supply a generation policy for anchors,
   sides, mark identifiers, and Lamport timestamps.
3. Define an independent sequential rich-text machine over the combined
   operation alphabet. Prove rendered equality, not a `True` relation.
4. Lift retention roots and mark-pair collection to the sided policy graph.
   Prove continuation and delayed-operation preservation against the
   never-collected twin.
5. Instantiate the distributed and both-GC fields, then replace—not silently
   reinterpret—the one-sided `peritextFlagship` paper endpoint.

## Current evidence boundary

`peritextFlagship` remains a valid machine-checked result for
`PeritextEmbedRGA`. `sidedVerified`, sided sequential soundness, Fugue policy
results, and sided policy GC remain valid component results. No existing
theorem composes those components into the shipped rich-text datatype.

## First completed link

`Peritext_Sided/PeritextSided_Core.lean` now defines the runtime-shaped
reachable representation: an insert-only subset of `S Γ`, a grow-only delete
set, and a grow-only unique-`mid` `MarkD` store. `coreGuard` rejects the unused
OR-set removals and native sided deletes, checks live deletion targets, and
checks mark timestamps, live endpoints, and freshness. `core_join_at` composes
the three algebraic Join results. `mintHonest_text` and `coreGeneration` prove
that product mint evidence supplies the sided history premise. PASS/FAIL mark
controls are checked. The module uses only standard axioms.

This closes the algebraic and generation layers. It deliberately does not yet
claim rendered intent, byte-codec correspondence, or state-GC preservation.
