# Multi-Valued Register in Sal vs. the literature

Cross-reference between

| Lean file | Variant |
|---|---|
| `Sal/CRDTs/Multi_Valued_Register/Multi_Valued_Register_CRDT.lean` | State-based CRDT |
| `Sal/MRDTs/Multi_Valued_Register/Multi_Valued_Register_MRDT.lean` | State-based MRDT |

and the canonical MVR reference:

> Marc Shapiro, Nuno Preguiça, Carlos Baquero, Marek Zawirski.
> *A comprehensive study of Convergent and Commutative Replicated
> Data Types.* INRIA Research Report RR-7506, 2011, §3.2.2 (Spec 14).

This document is the MVR counterpart of `peritext-vs-paper.md`,
`or-set-vs-paper.md`, and `aw-crpq-vs-paper.md`.

## Faithfulness to the paper

**The current Sal MVR implements classical replace-on-write
semantics**, matching paper Spec 14:

- **Concurrent writes both survive.** Two replicas issuing `Write v₁`
  and `Write v₂` concurrently end up with both visible after merge.
- **Sequential writes overwrite.** A `Write v₂` issued after observing
  `Write v₁` retracts `v₁` from the visible set.

The translation to Sal's state-based framework uses the same
**snapshot-in-op-payload** trick as `Add_Win_Priority_Queue`'s `Rmv`
and `OR_Set`'s `Rem`: each `Write v O` carries the prepare-time
snapshot `O ⊆ ℕ` of currently-visible timestamps, and `do_`
additively unions `O` into a separate `removed` component. This
keeps `rc := Either` everywhere and the 24 VCs trivialise via
pointwise-union.

| Aspect | Paper | Our Lean | Faithful? |
|---|---|---|---|
| Op set | `put(v)` (Spec 14) | `Write v O` where `O` is prepare-time snapshot | ✅ Same op surface; snapshot is implementation-internal. |
| State | per-replica observed-set | `(writes, removed) : set (ts × v) × set ts` | ✅ The pair carries both "what's been written" and "what's been retracted by some snapshot". |
| `value()` query (Spec 14 line 14) | observed-set values | `is_visible_value v ≔ ∃ ts, (ts, v) ∈ writes ∧ ts ∉ removed` | ✅ |
| Concurrent writes both survive | Antichain in version DAG | `concurrent_writes_both_visible` | ✅ |
| Sequential writes overwrite | observed-set replacement | `sequential_write_supersedes` | ✅ The supersession is encoded by the snapshot premise. |
| Convergence | Theorem 5.1 | 24 RA-linearizability VCs (CRDT and MRDT) | ✅ All closed via `by sal`. |

## Intent-preservation: paper claims ↔ Lean theorems

| Claim | Lean theorem (CRDT) | Lean theorem (MRDT) | Status |
|---|---|---|---|
| **Visible-value convergence.** Equal states give equivalent `is_visible_value`. | `is_visible_value_convergent` | `is_visible_value_convergent` | ✅ |
| **Visible after Write.** A fresh write makes its value visible. | `visible_after_write` | `visible_after_write` | ✅ |
| **Concurrent writes both survive (headline).** | `concurrent_writes_both_visible` | `concurrent_writes_both_visible` | ✅ |
| **Sequential write supersedes prior.** A `Write` whose snapshot includes a prior `ts` puts that ts in `removed`, retracting its value from the visible set. | `sequential_write_supersedes` | `sequential_write_supersedes` | ✅ |

## Why this matters vs. the previous simplified port

A prior version of Sal's MVR was a **simplified accumulating
variant**: `Write v` just added `(ts, v)` to a single grow-only set,
with no replacement. That variant is technically correct as a CRDT
(grow-only sets converge under union) but does *not* match the
paper's MVR semantics: under the simplified variant, sequential
writes did **not** overwrite, which is the defining property
distinguishing MVR from a write-only log.

**This is also where Sal now diverges from the upstream Neem F*
artefact.** The original Neem F* implementation
(`_references/neem_fstar_repo/code/{crdts,mrdts}/Multi-valued_register/App_mrdt.fst`)
uses exactly the simplified accumulating design that Sal inherited:

```fstar
type concrete_st = S.t (int & nat)
let do s ((ts,(_,Write v))) = S.add (ts,v) s
let merge a b = S.union a b           -- CRDT
let merge l a b = S.union l (S.union a b) -- MRDT
```

Sequential writes don't overwrite there either, so Spec 14's
headline property — *"concurrent writes both survive **and**
sequential writes overwrite"* — held only in the first half. The
current Sal MVR is therefore *more paper-faithful than the F*
original it was ported from*, achieved by the snapshot-in-op-payload
trick (same mechanism as `Add_Win_Priority_Queue`'s `Rmv` and
`OR_Set`'s `Rem`).

The current implementation closes that gap. The state shape
`(writes, removed)` and snapshot-based `do_` together let us:

- Prove `concurrent_writes_both_visible` as the headline MVR property.
- Prove `sequential_write_supersedes` (would not hold in the
  simplified variant).
- Keep `rc := Either` everywhere and close all 24 VCs via `by sal`,
  paying nothing for the upgrade.

## State shape — comparison with relatives

| RDT | State | Op |
|---|---|---|
| `Grow_Only_Set_CRDT` | `set elem` | `Add e` |
| `OR_Set_CRDT` | `(set (elem × ts), set (elem × ts))` (adds, tombstones) | `Add e`; `Rem e` snapshots tagged-by-elem |
| `Multi_Valued_Register_CRDT` (this file) | `(set (ts × v), set ts)` (writes, removed) | `Write v O` where `O` is a snapshot of ts values |
| `Add_Win_Priority_Queue_CRDT` | `(map (e, ts) → v, set (e, ts, ℤ), set (e, ts))` | `Add`, `Inc`, `Rmv e D` snapshots |

The MVR state structurally simplifies OR-Set's `(adds, tombstones)`:
both components live in a single domain (no per-element split), and
the tombstone set is keyed on `ts` alone (since Writes retract by
`ts`, not by tagged-elem).

## Concurrency premise — state-based stand-in

Same convention as `peritext-vs-paper.md`, `or-set-vs-paper.md`,
`aw-crpq-vs-paper.md`:

- "Concurrent" Write means: the new ts is fresh (not in `s.writes`,
  not in `s.removed`) and is not in any other concurrent Write's
  prepare-time snapshot. Both follow from `distinct_ops` for any
  reachable execution.
- "Sequential overwrite" is encoded by the snapshot premise:
  `mem ts₁ O₂ = true` (the second write observed and intends to
  retract `ts₁`).

These premises appear as explicit hypotheses in the headline
theorems; in any actual replica execution they hold structurally,
but the state-based framework requires us to thread them through
the proofs.

## Files at a glance

| Purpose | Path |
|---|---|
| State-based CRDT (24 VCs) | `Sal/CRDTs/Multi_Valued_Register/Multi_Valued_Register_CRDT.lean` |
| State-based MRDT (24 VCs) | `Sal/MRDTs/Multi_Valued_Register/Multi_Valued_Register_MRDT.lean` |
| CRDT read-side | `Sal/CRDTs/Multi_Valued_Register/Multi_Valued_Register_ReadSide.lean` |
| MRDT read-side | `Sal/MRDTs/Multi_Valued_Register/Multi_Valued_Register_ReadSide.lean` |
| Local copy of the paper | `_references/MVR §3.2.2 in INRIA RR-7506` |
