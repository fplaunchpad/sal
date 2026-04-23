# Merge-case proof strategy for `RA_lin_preserved_merge`

The one real sorry left in `Sal/Emulation/`. This document sketches
the proof plan in enough detail that a focused multi-day mechanization
effort can follow it without re-deriving the Sal paper's strategy.

**Source material:** lin.tex §3.3 ("Bottom-up linearization") and
appendix.tex §A.2–A.4 of the Sal paper (arXiv:2502.19967v1).

## What we are proving

```lean
theorem RA_lin_preserved_merge
    {D : CRDTSig} {C C' : Configuration D} (hVC : SatisfiesVCs D)
    {r₁ r₂ : Replica} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_s₁  : C.N r₁ = some s₁) (h_s₂  : C.N r₂ = some s₂)
    (h_ev₁ : C.L r₁ = some ev₁) (h_ev₂ : C.L r₂ = some ev₂)
    (hN   : C'.N = updateRep C.N r₁ (D.merge s₁ s₂))
    (hL   : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hRA : IsRALinearizable C) :
    IsRALinearizable C'
```

Unwinding: for replica `r₁` at the new state `D.merge s₁ s₂` and new
event set `ev₁ ∪ ev₂`, exhibit a permutation `π` respecting `lo C'`
such that `applySeq D D.init π = D.merge s₁ s₂`. For every other
replica `r ≠ r₁`, the old witness works.

## Witnesses from IH

The IH `hRA` gives us:

- `π₁` — a permutation of `ev₁`, respecting `lo C`, with
  `applySeq D.init π₁ = s₁`.
- `π₂` — a permutation of `ev₂`, respecting `lo C`, with
  `applySeq D.init π₂ = s₂`.

Goal: construct `π` for `merge(s₁, s₂)` at `ev₁ ∪ ev₂`.

## Event decomposition

For any configuration, `ev₁ ∪ ev₂` partitions into three disjoint
sets (paper notation, lin.tex §3.3):

- `L_top = ev₁ ∩ ev₂` — events witnessed at both replicas.
- `L₁    = ev₁ \ ev₂` — events only at `r₁`.
- `L₂    = ev₂ \ ev₁` — events only at `r₂`.

Then `ev₁ = L_top ∪ L₁` and `ev₂ = L_top ∪ L₂` (disjoint unions).

We further decompose each of `π₁, π₂` into the interleaving of their
`L_top`, `L₁`, `L₂` contributions. Formally this is about the
pre-image in π of the subset relations — pick sub-sequences by
filtering:

- `π₁ = π₁|_{L_top}` interleaved with `π₁|_{L₁}` (call these
  `π^top_1` and `π^a_1`).
- Similarly `π₂ = π^top_2` interleaved with `π^b_2`.

## The bottom-up template (paper BottomUpTemplate rule)

Paper §3.3 derives a single rewrite-style lemma from the 24 VCs:

```
⎛ π_j ∈ E ∪ {ε}  ⎞   π ∈ {π_0, π_1, π_2}    π_j' = π_j − π
⎝                ⎠  ─────────────────────────────────────────
   merge(π_0(l), π_1(a), π_2(b)) = π(merge(π_0'(l), π_1'(a), π_2'(b)))
```

Reading: with each `π_j` being either empty or a single event, and
`π` any one of them, we can "pull" `π` *out* of the merge, applying
it to the merge result instead of its originating argument.

In the CRDT setting (2-way merge), this specialises to: given
`merge(π_1(a), π_2(b))` (no LCA argument), we can pull a single event
out if the VC preconditions hold.

**The 24 VCs are instantiations of this template** — each one handles a
different combination of which argument of merge carries `π` and
whether there's an `rc`-ordered context event `o` floating around.

## Inductive structure

The proof is **double induction**: on `|L₁|` and `|L₂|`, pulling events
out of merge one at a time. Skeleton:

1. **Base:** `L₁ = L₂ = ∅`, i.e. `ev₁ = ev₂ = L_top`. Then `s₁ = s₂`
   (both yield `applySeq D.init π_top_1` and `= applySeq D.init π_top_2`,
   but π_top_1 and π_top_2 are both permutations of L_top, respecting
   the common `lo C`, so by convergence, `s₁ = s₂`). Then
   `merge(s₁, s₂) = merge(s₁, s₁) = s₁` by `merge_idem`. Witness `π = π_top_1`.

2. **Inductive step on `|L₂|`:** Pick the last event `e_2` in `π^b_2`.
   We want to rewrite `merge(s₁, s₂) = merge(s₁, D.update s₂' e_2)`
   where `s₂' = applySeq D.init (π_{2} − e_2)`. By the bottom-up
   template (specifically `ind_right_2op` or `ind_right_1op`), this
   equals `D.update (merge s₁ s₂') e_2`, pulling `e_2` outside.

3. **Inductive step on `|L₁|`:** Similarly, using `ind_left_*`.

4. Proceeding through all the `inter_*`, `base_*`, and `lem_0op` cases
   for the different patterns of "which side has the extra event" and
   "is there an `rc`-ordered context", the proof eventually reduces to
   a linearization `π` of `ev₁ ∪ ev₂` that respects `lo C'`.

## Respecting `lo C'`

The witness must respect `lo C'`. Key facts:

- `C'.vis = C.vis` (merge doesn't extend vis).
- Therefore `lo C' = lo C` — no shrink/extend reasoning needed, unlike
  the Apply case.
- The constructed `π` needs to embed the `lo C`-ordering of events
  from both `π₁` and `π₂`. Since both `π₁` and `π₂` already respect
  `lo C`, their interleaved construction preserves it *provided*
  the interleaving doesn't violate any `lo`-edge — guaranteed by
  `rc-non-comm` + `cond-comm`.

The `conditional commutativity` property (`cond_comm`) is what makes
the interleaving possible without ordering ambiguity (lin.tex §3.2,
Lemma `convergence`).

## Concrete Lean strategy

Propose a helper `merge_witness`:

```lean
def merge_witness (D : CRDTSig) (hVC : SatisfiesVCs D)
    (π₁ π₂ : List (Op D.AppOp)) (ev₁ ev₂ : Set (Op D.AppOp)) :
    List (Op D.AppOp) := …
```

Then three supporting lemmas:

1. `merge_witness_perm` — it's a nodup list whose elements are
   `ev₁ ∪ ev₂`.
2. `merge_witness_respects` — respects `lo C` (under the shared-vis
   hypothesis).
3. `merge_witness_state` — `applySeq D.init (merge_witness …)
   = D.merge s₁ s₂`.

The third is the load-bearing one; the first two are bookkeeping.

## Effort estimate

- ~1 week to port the paper's inductive argument into `merge_witness`
  (definitions, base case, the two inductive lemmas).
- ~1–2 weeks to close `merge_witness_state` — the hard case is
  applying the right VC at each step of the induction, which mirrors
  the paper's case analysis on pairs of events.
- Per-CRDT `SatisfiesVCs` instances still need to be plumbed, but the
  smoke test at `Sal/Emulation/Instances/Grow_Only_Set.lean` shows
  the plumbing works.

**Total:** 2–4 focused weeks for Phase 1 completion, realistically.

## Dependencies

- No external dependencies beyond the existing Sal repo and the VCs
  already transcribed in `SatisfiesVCs`.
- The paper's appendix §A.2–A.4 is the authoritative reference for
  the case analysis. Keep it open while working.
