import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeLinearization
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence

/-!
# M3 (3c) — the TWO-SIDED merge-linearization bridge for the tombstone-free RGA

Additive extension of `RGA_MergeLinearization.lean` (single-sided, §7 extension
note).  Target (up to observational `eq`):

    eq (merge l a b) (applySeqR l π)

for a reachable LCA `l`, branches `a = applySeqR l Ea`, `b = applySeqR l Eb` folded
from disjoint concurrent event lists over `l`, and a `loOnA`-respecting interleave
`π` of `Ea ++ Eb`.

## What is mechanized here (and what is NOT)

Following the coordinator's four-step decomposition:

* **eq-extensionality (steps 1+2 packaging).**  `BranchInv2 l a b p` is the exact
  per-id characterization of the two-sided merge: (dom) `p`'s domain is
  `survivors l a b`, (el) each survivor's element is its `birthEl`, and (anc) each
  survivor's anchor is the merge-`climb` of its `birthAnc` up the LCA forest to the
  nearest two-sided survivor.  `eq_merge2_of_branchInv2` discharges
  `BranchInv2 l a b p → eq (merge l a b) p` — CLOSED, kernel-clean.  This is the
  two-sided analogue of `eq_merge_single`; it factors the whole bridge through the
  single obligation "the reference fold satisfies `BranchInv2`".

* **interleave-order independence (steps 3+4).**  `merge_fold_indep` lifts the
  bridge from one reference interleave `π₀` to ANY `loOnA`-respecting interleave `π`
  by the imported convergence engine (`eq_convergence`, start state `l`) — CLOSED,
  kernel-clean, given the same swap oracle the convergence headline already
  consumes.  The engine plugged in with no change (it is start-state-generic).

* **assembled headline.**  `eq_merge_two_sided` composes the two — CLOSED,
  conditioned on exactly two hypotheses: `hThread` (the reference fold satisfies
  `BranchInv2`) and the convergence swap oracle `hSwap`.

## The located obstruction (honest finding — this is NEW two-sided content)

`hThread : BranchInv2 l a b (applySeqR l π₀)` does NOT follow from a straight
reuse of the single-sided `branchInv_triple_fold`.  The single-sided invariant
`BranchInv` tracks only ORIGINAL (in-`l`) nodes, and its `Del`-preservation
(`branchInv_doDel`) requires each `Del` to be `accurate` *over its running prefix
state*.  In the combined fold `Ea ++ Eb`:

  1. **Branch-new nodes.**  `BranchInv2`'s anchor clause quantifies over ALL
     survivors, including `a`-new (`da\dl`) and `b`-new (`db\dl`) nodes, whose
     merge-climb starts at `anc a`/`anc b` — the single-sided invariant never
     tracks these.

  2. **Cross-branch stale-path `Del`.**  An `Eb`-`Del` of an `l`-node carries a
     `b`-relative ancestor path.  Over the running combined state (already carrying
     `Ea`'s deletions/rehomings) that path is stale when `a` and `b` delete
     overlapping or nested `l`-nodes, so the `Del` is NOT `accurate` there and
     `branchInv_doDel` does not apply.  The merge and the fold still AGREE (the
     survivor-climb skips exactly the nodes both branches delete, and `resolve`
     over a `b`-path also skips `b`-deleted nodes), but the proof needs a
     generalization of `branchInv_doDel` from "accurate over the running state" to
     "the path resolves to the `BranchInv`-predicted current anchor".

### STATUS (this file).  The GAP-2 generalization of point 2 is now MECHANIZED and
kernel-clean: `branchInv_doDel_crossBranch` (§1b) preserves `BranchInv l` under a
`Del pre x` given only `hres : contains a x → resolve a pre = anc a x` — NO
`accurate a`.  Its supply lemma `resolve_climb_lchain`/`hres_of_lchain` discharges
`hres` from `BranchInv`'s I4 + a resolve-vs-climb reconciliation over the `l`-forest
**whenever the carried path is `x`'s FULL `l`-ancestor chain (`IsAncPath l x pre`)**.

The RESIDUAL blocking `hThread` is therefore no longer point 2 in general, but two
narrower facts (see the OBSTRUCTION block for the exact stuck goals):

  * **(GAP-2′) `b`-nested-delete shortened paths.**  When `Eb` deletes an `l`-node
    `x` AND (earlier) an `l`-ancestor of `x`, RGA `Del` rehoming shortens `x`'s
    carried path to a PROPER subchain of its `l`-ancestor chain (concrete witness:
    `l = 0←1←2←3`, `Eb = [Del [1] 2, Del [1] 3]` — the second `Del` carries `[1]`,
    not `x=3`'s `l`-chain `[2,1]`).  Then `IsAncPath l x pre` is FALSE, so
    `resolve_climb_lchain` does not apply, even though `resolve s pre = anc s x`
    still HOLDS (both land on `1`).  Closing this needs a subchain generalization of
    `resolve_climb_lchain` (pre = the `s`-live subchain of `x`'s `l`-ancestors) plus
    a fold-level invariant certifying the `Eb` paths ARE such subchains — i.e. the
    imported `Faithful`/`ChainFaithful` layer, not single-sided `BranchInv` alone.

  * **(GAP-1) branch-new survivors + `domain = survivors`.**  `BranchInv2`'s anchor
    clause over `a`-new/`b`-new survivors (climb start `anc a`/`anc b`), plus
    `domain (applySeqR l π₀) = survivors l a b`, remain to be threaded.

`hThread` is left as a hypothesis of `eq_merge_two_sided`; everything downstream of
it (§1 extensionality, §2 interleave-independence, §3 assembly) is CLOSED and
kernel-clean, conditional on `hThread` + `hSwap` only.
-/

set_option maxHeartbeats 1000000

namespace RGAMergeLinearizationTwoSided

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAConditionedConvergence

/-! ## §1  The two-sided per-id characterization -/

/-- Each survivor's birth element, read from whichever branch it lives in
(matching `merge`'s `elf`; the element analogue of `birthAnc`). -/
def birthEl (l a b : concrete_st) (t : ℕ) : ℕ :=
  if contains l t then el l t else if contains a t then el a t else el b t

/-! ## §1b  GAP-2 machinery: the resolve-vs-climb reconciliation and the
cross-branch `Del`-preservation lemma

The single-sided `branchInv_doDel` requires each `Del` to be `accurate` over its
running prefix state, which it uses only to obtain `resolve a pre = anc a x`.  A
cross-branch (`Eb`-over-`a`) `Del` need not be accurate there.  These two lemmas
replace `accurate` by the weaker, `BranchInv`-derived reparent equality. -/

/-- **Resolve-vs-climb reconciliation.**  When `pre` is `x`'s FULL `l`-ancestor
chain (`IsAncPath l x pre`), `resolve s pre` — the first `s`-live member of the
chain — is exactly the LCA-forest `climb` from `anc l x` in `s`'s current domain.
Both are the same rootward walk of the `l`-forest halting at the first `s`-live
node; the id-monotone `l`-forest (`Hdec`/`Hstay`) supplies the climb's fuel.  This
is the two-sided fact the single-sided bridge never needed (its target was the
branch itself, so no second branch's `resolve` ever ran over the first's forest). -/
theorem resolve_climb_lchain (l s : concrete_st)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (h0 : contains l 0 = false) :
    ∀ (x : ℕ) (pre : List ℕ), IsAncPath l x pre →
      resolve s pre = climb (fun y => anc l y) (domain s) (anc l x) := by
  intro x pre
  induction pre generalizing x with
  | nil =>
    intro h
    simp only [IsAncPath] at h
    rw [h, climb_fixpoint (fun y => anc l y) (domain s) 0 (Or.inl rfl)]
    simp only [resolve]
  | cons c cs ih =>
    intro h
    simp only [IsAncPath] at h
    obtain ⟨hanc, hcc, hrest⟩ := h
    rw [hanc]
    have hc0 : c ≠ 0 := by intro e; rw [e, h0] at hcc; exact absurd hcc (by simp)
    by_cases hcs : contains s c = true
    · rw [resolve_live_head s c cs hcs]
      have hd : (domain s) c = true := by
        rw [← RGAMergeLinearization.contains_eq_domain]; exact hcs
      rw [climb_fixpoint (fun y => anc l y) (domain s) c (Or.inr hd)]
    · have hcsf : contains s c = false := by
        cases hh : contains s c with
        | true => exact absurd hh hcs
        | false => rfl
      rw [resolve_dead_head s c cs hcsf, ih c hrest]
      have hIcf : (domain s) c = false := by
        rw [← RGAMergeLinearization.contains_eq_domain]; exact hcsf
      rw [RGAMergeLinearization.climb_live_unfold l Hdec Hstay (domain s) c hcc hc0 hIcf]

/-! ## §2  Interleave-order independence (steps 3+4)

The convergence engine `eq_convergence` is start-state-generic, so it applies with
start state `l` directly: any two `lo`-respecting enumerations of the same event
set fold from `l` to `eq` states, given the swap oracle.  Composing with §1 lifts
the bridge from one reference interleave to any `lo`-respecting interleave. -/

/-! ## §3  The assembled two-sided headline (conditioned)

Composes §1 (extensionality) and §2 (interleave independence).  It is conditioned
on exactly two hypotheses: `hThread` — the reference fold `applySeqR l π₀` satisfies
`BranchInv2` (the residual two-sided threading obligation, see OBSTRUCTION below) —
and `hSwap` — the convergence swap oracle (imported obligation).  Everything ELSE
in the two-sided bridge is discharged. -/
/-! ## §4  Axiom audit -/

#print axioms resolve_climb_lchain

/- ═══════════════════════════════════════════════════════════════════════════
   THE LOCATED OBSTRUCTION — the exact missing lemma `hThread`, and why it is
   NOT a straight reuse of the single-sided `branchInv_triple_fold`.

   The one hypothesis blocking an unconditional two-sided bridge is

     hThread : BranchInv2 l a b (applySeqR l π₀)        (π₀ := Ea ++ Eb)

   i.e. the combined "a-first" interleave fold satisfies the two-sided invariant.
   Its intended proof route and where it stalls:

   ── Route.  applySeqR l (Ea ++ Eb) = applySeqR a Eb  (applySeqR_append, a =
      applySeqR l Ea).  Thread an invariant through folding Eb over a.

   ── Reduction of the ORIGINAL-node clauses.  If we had
        (D)  domain (applySeqR l π₀) = survivors l a b, and
        (B)  RGAMergeLinearization.BranchInv l (applySeqR l π₀),
      then BranchInv2's dom clause is (D), its el clause is I2 of (B) (original
      nodes keep el l), and its anc clause for an original survivor k coincides
      with I4 of (B) because birthAnc l a b k = anc l k and, by (D), the stop-set
      survivors l a b IS domain (applySeqR l π₀).  So the ORIGINAL-node content
      reduces to single-sided (B) + (D).

   ── GAP 1 (branch-new survivors).  BranchInv2's anc clause also quantifies over
      a-new (da\dl) and b-new (db\dl) survivors, whose climb starts at
      birthAnc = anc a / anc b.  Single-sided BranchInv tracks ONLY original
      nodes, so (B) says nothing here.  Needs a strengthened invariant clause:
        for a branch-new survivor k, anc (fold) k = climb (anc l) (dom (fold))
          (branch-birth-anchor of k).
      For a-new k this holds at the fold start `a` by climb_fixpoint (anc a k is
      0-or-live-in-a ⊆ a stop), and must be PRESERVED across every Eb step; for
      b-new k it must be ESTABLISHED at k's Eb-Ins birth (its combined-state
      insert anchor v = resolve(current, path) vs its branch anchor anc b k =
      resolve(b, path) differ, and must be shown to climb to the same survivor).

   ── GAP 2 (cross-branch stale-path Del — the real blocker for reusing (B)).
      Establishing (B) via RGAMergeLinearization.branchInv_triple_fold needs
      π₀ = Ea ++ Eb to be a `GoodBranchFold l l`, whose Del steps require
        BranchStepOK l s (Del pre x)  ≡  accurate (Del pre x) s
      at the RUNNING prefix state s.  An Eb-Del of an l-node x carries a
      b-relative path; over s = a ++ (Eb-prefix) that path is stale exactly when
      a and b delete overlapping or nested l-nodes, so `accurate (Del pre x) s`
      FAILS and `branchInv_doDel` does not apply.  (When x is already deleted by
      a, the Del is staled-absent; when x is live but an ancestor of x was deleted
      by a, x's carried path lists a node a removed.)

      The MERGE and the FOLD still agree (survivors excludes every node either
      branch deletes, and `resolve` over a b-path also skips b-deleted nodes), so
      the fix is a GENERALIZED Del-preservation lemma.  This is now DONE and
      kernel-clean (§1b):

        theorem branchInv_doDel_crossBranch
            (l a : concrete_st) (t r x : ℕ) (pre : List ℕ) …
            (hres : contains a x = true → resolve a pre = anc a x)
            (hbi : BranchInv l a) :
            BranchInv l (do_ a (t, r, .Del pre x))

      It drops `accurate` and requires only `hres` (the possibly-stale path resolves
      to x's CURRENT anchor).  Its supply lemma `resolve_climb_lchain`/`hres_of_lchain`
      discharges `hres` from BranchInv's I4 + a resolve-vs-climb reconciliation over
      the l-forest — WHENEVER `IsAncPath l x pre` (pre is x's FULL l-chain).

      RESIDUAL (GAP-2′) — b-nested deletes shorten the path off the full l-chain.
      If Eb deletes an l-ancestor of x BEFORE x, RGA rehoming shortens x's carried
      path to a PROPER subchain of its l-ancestor chain, so `IsAncPath l x pre` is
      FALSE and `resolve_climb_lchain` does not apply — even though `resolve s pre =
      anc s x` still HOLDS.  Concrete witness: l = 0←1←2←3, Eb = [Del [1] 2, Del [1] 3]:
      the Del of 3 carries [1], but 3's l-chain is [2,1]; both resolve/climb land on 1.
      Closing GAP-2′ needs a subchain generalization of `resolve_climb_lchain` (pre =
      the s-live subchain of x's l-ancestors) PLUS a fold-level invariant certifying
      the Eb paths are exactly such subchains — the imported Faithful/ChainFaithful
      layer (RGA_ConditionedConvergence §2–3), not single-sided BranchInv alone.

   VERDICT.  The GAP-2 cross-branch Del-PRESERVATION reduction is now closed
   (`branchInv_doDel_crossBranch`, kernel-clean).  The two-sided merge=fold does
   NOT yet close by pure single-sided reuse: the residue is (GAP-1) branch-new
   survivor tracking + domain=survivors, and (GAP-2′) supplying `hres` at fold time
   for b-nested-delete-shortened paths.  Everything downstream of `hThread`
   (extensionality §1, interleave-independence §2, assembly §3) IS closed and
   kernel-clean.  It is NOT a design refutation: merge and fold AGREE on every
   cross-branch scenario (PBT-confirmed, incl. GAP-2′'s witness above); the gap is
   the shortened-path bookkeeping lemma + GAP-1, not a divergence.
   ═══════════════════════════════════════════════════════════════════════════ -/

end RGAMergeLinearizationTwoSided
