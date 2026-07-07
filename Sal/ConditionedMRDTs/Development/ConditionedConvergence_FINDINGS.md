# ConditionedConvergence — findings (task #9, stage 6)

*Companion to `ConditionedConvergence.lean` and `CONDITIONED_METATHEORY_PLAN.md`
stage 6. Build: `lake build Sal.MRDTs.Metatheory.Development.ConditionedConvergence`
exit 0, 0 sorries; headline decls kernel-clean (`propext, Classical.choice,
Quot.sound`, no `sorryAx`); the 2 pre-existing `Merge_Linearization` sorries are
NOT transitively reached.*

## Net verdict: the general theorem CLOSES, and the residual obstruction is pinned

The conditioned convergence problem **factors cleanly into two independent
halves**, and the factorization is the result:

| half | content | status |
|------|---------|--------|
| **order** | which `loOn` edges does conditioning drop, and does `loOnA` re-add them all? | **SOLVED (closed)** |
| **semantic** | justify the state-algebra swaps using `commutesOn` at applicable states, not `commutes` everywhere | **residue = one located obstruction** |

## Generic definitions chosen

* **`appliesDependsOn D e₂ e₁ := ∃ s, D.applicable e₂ s ≠ D.applicable e₂ (D.update s e₁)`.**
  The `ConditionedMRDTSig`-generic form of the RGA-syntactic
  `G2AppAware.appliesDependsOn` ("`e₂` names `e₁`'s Ins-timestamp"). Chosen because
  it is exactly the negation of "`e₁` never affects `e₂`'s applicability" — which
  is what a *vacuous* `commutesOn` edge witnesses — so it is precisely what the
  order VC needs, and it is strictly more general than the syntactic form (the
  syntactic form ⟹ this one). Dischargeable for the RGA counterexample pair
  (`rga_appliesDependsOn_del_ins`, kernel-clean).
* **`loOnA D C ev e₁ e₂ := loOnC D C ev e₁ e₂ ∨ (C.vis e₁ e₂ ∧ appliesDependsOn D e₂ e₁)`** —
  the direct generalization of `G2AppAware.loOnA`.
* **`noopFeasible`** reused verbatim from `UpdateFeasibility_Gate.lean`.
* **`appOrNoop`, `interleavingFeasible`** — the frontier predicates naming the gap.

## Order half — SOLVED (`loOn ⊆ loOnA`)

Under a **single** order VC

    dependency_covers_vacuity :
      ∀ a b, C.vis a b → ¬commutes a b → commutesOn a b → appliesDependsOn b a

`loOn_imp_loOnA` proves the pointwise inclusion `loOn C ev ⊆ loOnA D C ev`
(vis-edges that `commutesOn` makes vacuous are re-added by the dependency
disjunct; rc-edges promote because `commutes → commutesOn` makes the absorber
clause of `loOn` imply that of `loOnC`). Hence
`respects π (loOnA) → respects π (loOn)` (`respects_loOn_of_loOnA`). This is the
*complete* answer to "which edges must `loOnA` add back": exactly the ones
`dependency_covers_vacuity` names. The free lemmas `commutes_imp_commutesOn`,
`commutesOn_symm` need no VC.

## Headline `conditioned_convergence_on` — CLOSED

Two `loOnA`-respecting, `noopFeasible` enumerations of `ev` fold from `D.init`
to the same state. Proof = `respects_loOn_of_loOnA` (both) then the *existing*
unconditioned `convergence_on_u`. Stated under `UpdateVCs D.toCRDTSig`
(unconditioned semantic VCs) **+** `dependency_covers_vacuity`.

Two findings from the route:

1. **`noopFeasible` is not needed for convergence here.** The two hypotheses are
   carried (stage-6 signature) but never consulted. `noopFeasible`'s role is
   *satisfiability* (existence of admissible enumerations for redundant-concurrent
   versions), and it becomes load-bearing for *convergence* only on the
   `commutesOn`-only route below.
2. The theorem consumes the **unconditioned** `UpdateVCs`. That is honest, not
   incidental: it is exactly the semantic half the reduction cannot condition
   away for free.

## `UpdateVCsC` (the `commutesOn`-only bundle) — what it required

`UpdateVCsC` mirrors `UpdateVCs` with `commutes ↦ commutesOn`
(`rc_non_comm_directional`, `no_rc_chain`, `cond_comm_liftC`); `cond_comm_liftC`
additionally carries `D.Inv s` (the minimal base side condition under which a
per-MRDT observational discharge is expected). Under it, **the conditioned swap
CLOSES**:

* `applySeq_swap_commutesOn` — direct swap, fires `commutesOn` at the one swap
  state given `Inv`+`applicable a`+`applicable b` there;
* `applySeq_swap_via_cond_comm_liftC` — overwriter swap, from the VC given `Inv`
  of the base fold state;
* `applySeq_swap_loOnA_incomparable_C` — the `loOnA`-incomparable swap; all three
  branches close (commute / same-replica-impossible / diff-replica-overwriter).

## The located obstruction (the commutesOn-only bubble)

`applySeq_swap_loOnA_incomparable_C` requires, **at the swap state**
`applySeq init pfx`, the three premises `hInv`, `ha : applicable a …`,
`hb : applicable b …`. In `convergence_on_u`'s bubble the swap state is the
**hybrid**

    applySeq D.init  (peeled-π₁-heads  ++  σ-prefix),   σ ⊆ π₂.

* **`hInv` — dischargeable** (obligation (A), `Inv_transport_generic`), given an
  op-only invariant-step field `∀ s o, o ∈ ev → Inv s → Inv (update s o)`.
* **`ha` / `hb` — the OBSTRUCTION.** `noopFeasible π₁` constrains only
  π₁-prefix states; `noopFeasible π₂` only π₂-prefix states. The hybrid
  interleaves a π₁-prefix with a π₂-prefix, so neither hypothesis says anything
  about `a`/`b` applicability there. This is `G2_Transport_Probe.lean`'s "swaps
  visit states no execution visits", now pinned to the `ha`/`hb` premises of a
  single lemma at the σ-walk of the bubble. What *would* close it is
  `interleavingFeasible` (no-op-feasibility of **every** admissible interleaving),
  which is strictly stronger than `noopFeasible π₁ ∧ noopFeasible π₂` and not
  implied by it.

**Secondary finding — no-op tolerance does not compose through a swap.** A no-op
branch (`update s' a = s'`) does *not* give the swap unless `a` stays a no-op
after `b` (an idempotence-commutation fact not implied by `commutesOn`; the RGA's
`del1_idem`). So the swap lemma requires genuine `applicable` (not `appOrNoop`):
`noopFeasible` absorbs no-ops in the FINAL fold, but the SWAP needs applicability.
In the redundancy case both deletes are genuinely applicable at every actual swap
state (`s₁ = do_ init ins`) — the no-op only surfaces in the final fold — so no
idempotence VC is needed there; the obstruction is solely `ha`/`hb` at hybrids.

## RGA instantiation sketch — status

* Order VC `dependency_covers_vacuity`: **dischargeable** (witness
  `rga_appliesDependsOn_del_ins` proved).
* Headline's `UpdateVCs` (unconditioned): **not available** — `rc = Either` and
  RGA commutation is observational `eq`, not Lean `Eq` (the hosting gap). So the
  headline reduction does not fire for the RGA; the RGA needs the
  `commutesOn`-only route and therefore hits the located obstruction. This is the
  precise sense in which the RGA is the `Inv`-nontrivial frontier case.

## Recommendation

The order half is done and cheap. To close the `Inv`-nontrivial column, the next
move is to supply `interleavingFeasible` (or a weaker, bubble-shaped variant that
only quantifies the interleavings the peel actually produces) as a per-MRDT
obligation, then re-mechanize the bubble+convergence with `commutesOn` and the
oracle threaded. The RGA should satisfy such an oracle wherever its ops are
create-before-use (positive dependencies), because then every peel-produced
interleaving keeps its next op applicable-or-no-op — but this is now a concrete,
bounded obligation, not an open design question.
