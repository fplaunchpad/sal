# Analysis: Closing `merge_linearization_exists` — Distinct-Last-Event Branch

## Status

The sorry at line 1542 of `Sal/Emulation/Merge_Linearization.lean` remains **open**.
After extensive analysis (including multiple automated proof attempts), this sorry
cannot be closed within the current induction structure and VC formalization.

## Root Cause

The current proof uses strong induction on `|π₁| + |π₂|` (total list length). The
distinct-last-event branch (e₁ ≠ e₂) requires peeling an event from the merge
equation via a BottomUp rule, then recursing with a strictly smaller total length.

**Three obstacles** prevent closure:

### 1. The `|π₁| + |π₂|` induction is the wrong measure

The paper (appendix §A.2) uses a quintuple-nested induction over:
- `|L₁ᵃ ∪ L₂ᵃ|` (local events without lo-path to shared layer)
- `|L_topᵃ|` (shared events with lo-predecessors in L^b)  
- `|M₁ᵃ|`, `|M₂ᵃ|` (sub-carving of local events)

This carving-based structure selects peel candidates with **structural**
no-lo-successor guarantees (from the carving definition), not positional
ones (from being last in a list). The `|π₁| + |π₂|` measure doesn't
provide this structural guarantee.

### 2. BottomUp-2-OP only handles `rc = Fst_then_snd`

The theorem `bottomUp_2op_reachable` (line 1011) requires:
```
h_rc : D.rc o₂ o₁ = RcRes.Fst_then_snd
```
When the two candidate events **commute** (rc = Either), this theorem
is inapplicable. Extending the right side of the merge equation for
the `Either` case requires `ind_right_2op`, which also demands strict
`Fst_then_snd`. The `inter_*_2op` VCs could handle this via
interposition, but require (ob, ol) pairs with `rc = Fst_then_snd`,
which may not exist in the all-commuting case.

### 3. The all-commuting case is VC-incomplete

When **all** cross-event pairs commute (e.g., G-Set CRDT where every
op is `add`), none of the 2-op BottomUp VCs fire:
- `ind_right_2op`: requires `Fst_then_snd` ✗
- `inter_right_base_2op`: requires an `(ob, ol)` pair with `rc = Fst` ✗
- `base_2op`: works at `init` base but can't extend the right side ✗

The equation `D.merge (D.update a e₁) s₂ = D.update (D.merge a s₂) e₁`
(the "commuting peel") is **true** for all CRDTs but not derivable from
the current VC set. Proof attempts using `ind_left_2op` (which accepts
`Either`) only extend the left side; extending the right side requires
`ind_right_2op` with `Fst`.

## Cases That ARE Provable

The following sub-cases of the distinct-last branch can be closed with
existing infrastructure:

### Non-commuting, both-local case  
`e₁ ∉ ev₂ ∧ e₂ ∉ ev₁ ∧ ¬commute(e₁, e₂)`

- `rc_non_comm_directional` gives `rc(e₁,e₂) = Fst ∨ rc(e₂,e₁) = Fst`.
- WLOG `rc(e₂,e₁) = Fst`: peel e₁ via `bottomUp_2op_reachable`.
- `no_rc_chain` + closure argument proves e₁ lo-maximal in ev₁ ∪ ev₂.
- `differentReplicas_of_closure` gives the `differentReplicas` premise.
- IH on `(π₁', π₂, ev₁ \ {e₁}, ev₂)` with total size n−1.
- Witness: `π' ++ [e₁]`.

### Shared-last-event (already closed)
`e₁ = e₂` — handled at line ~1407 via `lem_0op`.

### Subset case (`ev₁ ⊆ ev₂`)
When the lo-maximal element of ev₂ is in ev₁, it's lo-maximal in
both (by `no_rc_chain` + subset containment), enabling a shared peel.

## Recommended Path Forward

### Option A: Extend VCs (minimal change)
Add `merge_assoc` or `merge_peel_comm` to `SatisfiesVCs`:
```lean
merge_peel_comm :
  ∀ (a : D.State) (e : Op D.AppOp) (π : List (Op D.AppOp)),
    (∀ x ∈ π, D.commutes e x) →
    D.merge (D.update a e) (applySeq D D.init π)
      = D.update (D.merge a (applySeq D D.init π)) e
```
This is a natural lattice property that all CRDTs satisfy. Adding it
would close the commuting case immediately.

**Caveat**: Requires modifying `RA_Linearizability.lean` and verifying
the new VC for all CRDT instances.

### Option B: Implement carving analysis (no VC change)
Port the paper's full quintuple-nested induction from appendix §A.2.
This is ≈400–600 lines of Lean code covering:
1. Carving layer definitions (L^a/L^b partition) — **already done** (lines 77–253).
2. Lemma 1 ("no lo-edge from L^a to L^b") — needs proof.
3. Inter-VC induction for extending the right side through L^b events.
4. The quintuple induction itself.

This is the paper's intended proof strategy and doesn't need new VCs,
but is a major engineering effort.

### Option C: Restructure the induction (moderate change)
Replace the `|π₁| + |π₂|` strong induction with well-founded induction
on a carving-aware measure. Keep the existing base/asymmetric/shared-last
cases; replace the distinct-last branch with a carving-based reduction.
This is a middle ground between A and B.
