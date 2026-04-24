# Merge-case proof strategy for `RA_lin_preserved_merge`

This document sketches the proof plan in enough detail that a focused
multi-day mechanization effort can follow it without re-deriving the
Sal paper's strategy.

## Structural finding + refactor (session 2026-04-24)

The original plan factored the merge case into three independent
sub-lemmas `merge_witness_{perm, respects, state}`. A closer look
showed **`_respects` and `_state` are structurally coupled** — any
elementary definition of `merge_witness` (including the paper's
three-part `π_top ++ π₁|_{L₁} ++ π₂|_{L₂}` form) leaves disjunct 2
of the cross case (the concurrent, `rc`-ordered, non-`vis` case)
without an elementary contradiction. The paper's own proof
co-constructs the witness and its lo-respect property inside the
bottom-up induction; `respects` is a byproduct of *how* the witness
is built, not a fact about a pre-chosen witness.

**Refactor landed:** the three lemmas and the standalone
`merge_witness` definition were replaced by a single existential
theorem `merge_linearization_exists`:

```
∃ π, listPermOf π (ev₁ ∪ ev₂) ∧ respects π (lo C) ∧
      applySeq D.init π = D.merge s₁ s₂
```

This is what the paper actually proves in lin.tex §3.3 / appendix
§A.2–A.4. Its body is structured as case analysis on whether `π₁`
or `π₂` is empty; the degenerate **both-empty** case is closed
using `merge_idem`. The two non-empty inductive cases remain
`sorry` — they are the bulk of the remaining work.

Other wins from the session:

* **Causal closure invariant** added as `Configuration.vis_causal`
  (`CRDT_TS.lean`). Kernel-verified, no sorries. Although the
  coupled `_respects` sorry was folded into the new monolithic
  theorem, `vis_causal` remains useful machinery for the Apply
  case's lo-shrink argument and for eventual use inside the
  bottom-up induction.
* **Packaging theorem** `RA_lin_preserved_merge_via_witness` now
  destructures the existential directly; no thematic change to its
  shape.

## Source material

lin.tex §3.3 ("Bottom-up linearization") and appendix.tex §A.2–A.4
of the Sal paper (arXiv:2502.19967v1).

## Proof structure (from the paper's appendix)

The paper's proof is **two layers**:

1. **Derive three BottomUp rules** (BottomUp-0-OP, -1-OP, -2-OP)
   from the 24 VCs. Each rule is a general pull-one-event-out-of-
   `merge` rewrite. Each derivation is itself a *nested induction*
   cascading through ~9 VCs — `base_*op` for the innermost base,
   `ind_*_*op` for a single inductive extension, `inter_*_*op` for
   the `rc`-ordered interposition cases.

2. **Apply the BottomUp rules** inside a **quintuple-nested
   induction** over the event sets `L_top^a, L_top^b, L_1^b, L_2^b`
   to build the linearization witness.

The specialisation to CRDTs (2-way merge, no LCA) collapses the LCA
arguments to `init`, eliminating `L_top^a` as a separate outer
induction, but the three BottomUp rules and their nested induction
proofs are unchanged. Even the degenerate case `π₁ = []` (asymmetric
merge against `init`) requires BottomUp-1-OP, because `merge init s`
for reachable `s` is not a direct VC consequence.

## Realistic effort estimate

Even with the paper in hand, porting the nested inductions is ~2–3
weeks of focused Lean work. The BottomUp rules alone are ~1 week
each. The outer induction on event sets is another week. Breaking
this into discrete sessions is tractable:

- Session +1: port BottomUp-0-OP (the simplest — for CRDTs it's
  just `lem_0op`, already a single-liner via `hVC.lem_0op`).
- Session +2: port BottomUp-1-OP from `base_1op` + `ind_*_1op` +
  `inter_*_1op`.
- Session +3: port BottomUp-2-OP symmetrically.
- Session +4: orchestrate the outer induction on `ev₁`, `ev₂`.

Current Lean state: `bottomUp_0op` landed (closes to `lem_0op`);
`bottomUp_1op`, `bottomUp_2op` scaffolded as `True` placeholders,
pending formulation of the `rc`-precondition predicate and the
triple induction.

## Session update (2026-04-24, continued)

Follow-up push closed three real inductive theorems:

- `bottomUp_2op_init_left` — reachable `b`, `a = D.init`. Proved by
  `List.reverseRecOn` over `π_b`; base is `base_2op`, step is
  `ind_right_2op`. Kernel-verified.
- `bottomUp_2op_reachable` — reachable `a` and `b`, strict
  `Fst_then_snd` rc. Outer induction on `π_a` via `ind_left_2op`,
  inner via `bottomUp_2op_init_left`. Kernel-verified. This is the
  **main result** of the session on the merge case.
- `bottomUp_1op_top_reachable` — strict-rc corollary of
  `bottomUp_2op_reachable` by variable renaming (`ol → o₂`).

The abstract-state forms (`bottomUp_2op`, `bottomUp_1op_top`,
`bottomUp_1op_bot`) remain `sorry`:

- `bottomUp_2op`, `bottomUp_1op_top` (abstract): the universal-`a, b`
  statement is *strictly stronger* than the VCs — VCs only constrain
  reachable states. This is expected; callers should use the
  reachable-form theorems directly.
- `bottomUp_1op_bot`: `merge(update a o₁, D.init) = update (merge a D.init) o₁`.
  The 24 VCs contain **no rule** extending `base_1op` to reachable
  `a` when the RHS is `init` — every `ind_*_1op` / `inter_*_1op`
  requires the RHS to have an event `ol` applied. Tried and failed:
  `ind_lca_1op` (diagonals, wrong shape), phantom-event transport
  (no VC collapses `update init ol → init`), `merge_comm` + `lem_0op`
  creativity (introduces structure but doesn't reduce). The paper's
  closure of this case uses the outer nested induction's machinery
  to handle init-shaped arguments via convergence — i.e., clause (b)
  is actually closed **as a byproduct of the full linearization
  theorem**, not derived separately. So in our Lean setup,
  `bottomUp_1op_bot` is probably better folded into
  `merge_linearization_exists` directly via strong induction, not
  proved as a standalone lemma.

## Session update (2026-04-24, continued further)

**Closed this iteration:**
- Shared-last-event case of `merge_linearization_exists` (~85 lines,
  factored via `lem_0op` + strong-induction IH).
- `timestamps_distinct` invariant on `Configuration` (discharged at
  `initConfig`; usage demonstrated in distinct-last-event sub-case).
- `vis_total_same_replica` invariant on `Configuration`.
- Retired three abstract-state BottomUp sorries.

**Key structural insight gained:**

The `differentReplicas e₁ e₂` derivation via `vis_causal` +
`vis_total_same_replica` works *only at the top level* of
`merge_linearization_exists`. At recursive depth, the shrunken
event sets `ev₁ \ {peeled}`, `ev₂ \ {peeled}` no longer equal any
specific replica's event set, so `vis_causal` at the original
replica can't be invoked. An event could be in the shrunken
`ev₁ \ ev₂` because it was peeled off `ev₂` in a prior shared-
last-event iteration, not because it's genuinely "local to r₁."

This is why the paper's `L^a` / `L^b` event-set decomposition is
**necessary**, not optional: it preserves the closure properties
through recursion. Arbitrary shrinkage via the simple strong-
induction breaks the invariant that would let us argue
`differentReplicas` at deeper recursive depths.

**Structural obstacle uncovered for the distinct-last-event case:**

`bottomUp_2op_reachable` requires `distinctOps e₁ e₂` AND
`differentReplicas e₁ e₂`. `distinctOps` (distinct timestamps) is
a **reachability invariant** that can be threaded via a
Configuration field or via a new hypothesis on the theorem
signature. But `differentReplicas` is **NOT** universally true:
two events from a third replica `r₃` could appear in both
`ev₁ \ ev₂` (as peeled e₁) and `ev₂ \ ev₁` (as peeled e₂). Example:
replica r₃ produces e, e'; r₃ merges into r₁ then produces e'; r₃
separately merges into r₂. Now r₁ has {e, e'}, r₂ has {e, e'}, and
neither has anything from the other. But if r₁ further advances
(local op at r₁) and r₂ advances (local op at r₂), the "local"
events are at r₁ and r₂ respectively, not r₃.

Actually more relevantly: the peeled events e₁ and e₂ (maximal
in `lo` order within π₁, π₂) could both be from r₃ if both r₁ and
r₂ had received r₃'s events but not each other's.

This is what the Sal paper's `L^a_1, L^a_2, L^b_1, L^b_2` event-set
decomposition (appendix §A.2) is designed to sidestep: the paper
picks peel candidates precisely to satisfy the VC preconditions.

**Implication:** The Lean port of the distinct-last-event case
cannot just do "case-split on rc(e₁, e₂) and peel." It needs the
paper's full event-set decomposition machinery, which is a
multi-session effort on its own.

Realistic path forward:

1. Prove **convergence** (bubble-sort) as a standalone theorem.
   This provides a stronger rewrite tool and lets the next steps
   pick any lo-respecting permutation without loss of generality.
2. Define the `L^a_1, L^a_2, L^b_1, L^b_2` event sets and prove
   `bottomUp_2op_reachable` applies at specifically-chosen peel
   points (the maximal events in each decomposition class).
3. Close the distinct-last-event case using step 2.
4. `merge_init_left_reachable` falls out as corollary.

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
