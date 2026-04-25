# OR-Set in Sal vs. the literature

Cross-reference between three Lean formalisations and the canonical
OR-Set reference:

| Lean file | Variant |
|---|---|
| `Sal/CRDTs/OR_Set/OR_Set_CRDT.lean` | State-based CRDT (adds + tombstones) |
| `Sal/MRDTs/OR_Set/OR_Set_MRDT.lean` | State-based MRDT (LCA replaces tombstones) |
| `Sal/MRDTs/OR_Set_Efficient/OR_Set_Efficient_MRDT.lean` | Compressed MRDT — one tag per `(rid, elem)` pair |

Reference:

> Marc Shapiro, Nuno Preguiça, Carlos Baquero, Marek Zawirski.
> *A comprehensive study of Convergent and Commutative Replicated
> Data Types.* INRIA Research Report RR-7506, 2011.

This document is the OR-Set counterpart of `peritext-vs-paper.md` and
`aw-crpq-vs-paper.md`.

## Formalisation target

The reference presents OR-Set as both an op-based CRDT (Spec 14) and
a state-based CRDT (Spec 15) in §3.3.5. The headline semantic claim
is **add-wins**: a concurrent Add and Rem on the same element resolve
to the element being present, because the Rem only retracts add-tags
its originating replica had observed.

| Paper | Our Lean | Notes |
|---|---|---|
| Convergence (Spec 15 + INRIA Theorem 5.1) | 24 RA-linearizability VCs (per variant) | All closed. CRDT and MRDT both use grow-only set components joined by union; the efficient MRDT uses `(rid, ts, elem)` triples with per-replica deduplication. |
| Add-Wins resolution | `add_wins_over_concurrent_remove` (all three variants) | State-based stand-in: the new add-tag is fresh in `s` (CRDT) / in the LCA `l` (MRDT) — i.e. the Rem's snapshot didn't observe it. |
| Lookup semantics | `lookup` predicate (all three variants) | CRDT: ∃ tag `(e, ts) ∈ adds ∧ (e, ts) ∉ tombstones`. MRDT: ∃ `(ts, e) ∈ s`. Efficient MRDT: ∃ `(rid, ts, e) ∈ s`. |
| Sequential Add; Rem retracts | `add_then_remove_extinguishes` | The `Rem`'s filter (or tombstone-add) sweeps every observed `(e, _)` tag, so a sequential `Add; Rem` on one replica leaves `e` not-live. |

## Intent-preservation: paper claims ↔ Lean theorems

| Claim | Lean theorem (CRDT) | Lean theorem (MRDT) | Lean theorem (Efficient MRDT) | Status |
|---|---|---|---|---|
| **Lookup convergence.** Equal states give equal `lookup`. | `lookup_convergent` | `lookup_convergent` | `lookup_convergent` | ✅ |
| **Lookup after Add.** A fresh Add immediately makes the element live. | `lookup_after_add` (premise: tag fresh in tombs) | `lookup_after_add` | `lookup_after_add` | ✅ |
| **Add-Wins headline.** A concurrent Add survives a Rem whose snapshot does not include its tag. | `add_wins_over_concurrent_remove` (premise: tag fresh in both `adds` and `tombstones` of common pre-state) | `add_wins_over_concurrent_remove` (premise: tag ∉ LCA `l`) | `add_wins_over_concurrent_remove` (premise: `(rid, ts, e) ∉ l`) | ✅ |
| **Sequential Add then Rem retracts.** | `add_then_remove_extinguishes` | `add_then_remove_extinguishes` | `add_then_remove_extinguishes` | ✅ |

## Concurrency premise — state-based stand-in

Same convention as `peritext-vs-paper.md` and `aw-crpq-vs-paper.md`:

- **CRDT side.** "Concurrent" means the new add-tag is fresh in
  the common pre-state's `adds` and `tombstones`. Under that
  premise, the Rem's `filter (Prod.fst s) (·.1 = e)` cannot
  capture the new tag because it isn't yet in `s.adds`. After
  merge, the new tag is in the union of `adds` but not the union
  of tombstones.
- **MRDT side.** The new tag sits in `a \ l` after the standard
  three-way set merge `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)`, so it
  bypasses any filtering on the Rem branch entirely.
- **Efficient MRDT.** Same as MRDT, with `(rid, ts, e)` triples;
  the `Add`'s per-replica filter (drop prior `(rid, _, e)`) is
  irrelevant to the survival argument since the new triple is
  fresh in the LCA.

## Why these are non-trivial vs. the 24 VCs

The 24 RA-linearizability VCs prove **state convergence** under
merge — both components grow-only, joined by union. They never
mention the word "lookup", "live", or "add-wins". A reader of just
the 24-VC files would conclude "the union converges" but learn
nothing about *what an element being in the OR-Set means*. The
read-side theorems above are the OR-Set's actual semantics.

This matches the Tier-C pattern from `papoc-2026-keynote-notes.md`:
the 24 VCs are necessary but vacuous, and the user-visible behaviour
lives entirely in the read-side projection.

## Files at a glance

| Purpose | Path |
|---|---|
| State-based CRDT (24 VCs) | `Sal/CRDTs/OR_Set/OR_Set_CRDT.lean` |
| State-based MRDT (24 VCs) | `Sal/MRDTs/OR_Set/OR_Set_MRDT.lean` |
| State-based MRDT, compressed (24 VCs, with Blaster admits) | `Sal/MRDTs/OR_Set_Efficient/OR_Set_Efficient_MRDT.lean` |
| CRDT read-side | `Sal/CRDTs/OR_Set/OR_Set_ReadSide.lean` |
| MRDT read-side | `Sal/MRDTs/OR_Set/OR_Set_ReadSide.lean` |
| Efficient MRDT read-side | `Sal/MRDTs/OR_Set_Efficient/OR_Set_Efficient_ReadSide.lean` |
