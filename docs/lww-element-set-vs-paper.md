# LWW-Element-Set in Sal vs. the literature

Cross-reference between the Lean formalisation in
`Sal/CRDTs/LWW_Element_Set/LWW_Element_Set_CRDT.lean` and the
canonical LWW-Set reference:

> Marc Shapiro, Nuno Preguiça, Carlos Baquero, Marek Zawirski.
> *A comprehensive study of Convergent and Commutative Replicated
> Data Types.* INRIA Research Report RR-7506, 2011, §3.3.4 (Spec 13).

This document is the LWW-Element-Set counterpart of
`peritext-vs-paper.md`, `or-set-vs-paper.md`, `aw-crpq-vs-paper.md`,
`mvr-vs-paper.md`.

## Formalisation target

The Sal CRDT uses two grow-only `(elem, ts)` maps: `addTs[id]` is
the latest `Add` timestamp seen for `id`, and `remTs[id]` is the
latest `Remove`. Both are joined per-key via `max` on merge. The
read-side `lookup` says `id` is live iff `addTs[id] > remTs[id]`
strictly — ties favour the remove, the conservative
"remove-wins-on-tie" convention noted in the upstream
`LWW_Element_Set_CRDT.lean` docstring (line 32–33).

| Aspect | Paper | Our Lean | Faithful? |
|---|---|---|---|
| Op set | `add(e, ts)`, `remove(e, ts)` | `Add id` and `Remove id` (both stamp the op's `ts` into the corresponding map) | ✅ |
| State | per-element `(addTs, remTs)` | `map ℕ ℕ × map ℕ ℕ` | ✅ |
| `lookup(e)` | "addTs > remTs" or "addTs ≥ remTs" depending on tiebreak choice | `mysel addTs id > mysel remTs id` (strict — remove wins on tie) | ✅ One of the two paper-described variants. The other variant (add-wins-on-tie) would just flip `>` to `≥`. |
| Convergence | Theorem 5.1 (eventual consistency) | 24 RA-linearizability VCs | ✅ All closed. |

## Intent-preservation: paper claims ↔ Lean theorems

| Claim | Lean theorem | Status |
|---|---|---|
| **Lookup convergence.** Equal states give equal `lookup`. | `lookup_convergent` | ✅ |
| **Add at fresh higher ts makes element live.** Adding with `ts > current rem-ts` puts the element in the visible set. | `lookup_after_add_with_fresh_ts` | ✅ |
| **Remove at fresh higher ts extinguishes.** Removing with `ts ≥ current add-ts` removes the element from the visible set. | `remove_at_higher_ts_extinguishes` | ✅ The `≥` (not strict) reflects the remove-wins-on-tie convention. |
| **Latest write wins.** The headline LWW property — liveness depends only on the comparison of the two latest timestamps. | convergence + `lookup_after_add_with_fresh_ts` + `remove_at_higher_ts_extinguishes` | ✅ These are the *independent* content. `lookup_def` (formerly `latest_write_wins`) is only the definitional unfolding of `lookup` (`by rfl`) — it restates the read's definition and certifies no behaviour, so it is **not** the guarantee. |
| **Equal ts → remove wins.** Under tie, element is not live (conservative convention). | `equal_ts_remove_wins` | ✅ |

## Comparison with OR-Set

LWW-Element-Set and OR-Set both implement add-wins-style behaviour
under different mechanisms:

| | OR-Set | LWW-Element-Set |
|---|---|---|
| Add tag | unique `(elem, ts)` per-add | shared latest `addTs[elem]` |
| Remove | tombstones every observed add | stamps latest `remTs[elem]` |
| Read | `∃ tag ∈ adds ∧ tag ∉ tombstones` | `addTs[elem] > remTs[elem]` |
| Concurrent Add+Remove | Add wins (Rem's snapshot misses fresh add) | Whichever has higher ts wins |
| Sequential Add; Remove | Removes the just-added tag | Pushes remTs above addTs |

OR-Set preserves more information (per-add identity) at the cost of
unbounded tag sets; LWW-Element-Set is simpler but coarser.

Both are formalised as Tier-C RDTs in this repo: their 24 VCs prove
state convergence, and the read-side projection lifts the
add-wins/visibility semantics into theorems.

## Why these are non-trivial vs. the 24 VCs

The 24 VCs prove that two `(addTs, remTs)` maps converge under
per-key max — they prove lattice-equivalence on each component
independently. They never mention the cross-component comparison
`addTs > remTs` that defines liveness. The read-side theorems lift
that comparison into Lean explicitly.

## Files at a glance

| Purpose | Path |
|---|---|
| State-based CRDT (24 VCs) | `Sal/CRDTs/LWW_Element_Set/LWW_Element_Set_CRDT.lean` |
| Read-side | `Sal/CRDTs/LWW_Element_Set/LWW_Element_Set_ReadSide.lean` |

(There is no MRDT version of LWW-Element-Set in the suite — only
the CRDT.)
