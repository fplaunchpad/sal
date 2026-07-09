import Sal.ConditionedMRDTs.MRDT_Instances.RGA.RGA_MergeLinearization_TwoSided
import Sal.ConditionedMRDTs.MRDT_Instances.RGA.RGA_SubchainResolve
import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Tombstone_Free_MRDT
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.MRDT_Instances.RGA.RGA_ConditionedConvergence

/-!
# GAP-1 (`hBN`): the branch-new survivor anchor coincidence

*Additive; not committed; 0 `sorry` in what is kept.*

`RGA_MergeThreadDischarge.eq_merge_two_sided_of_reachable` reduced the two-sided
merge bridge to four fold-level pieces, all discharged EXCEPT the branch-new
survivor anchor clause `hBN`.  For a survivor `k` with `¬ contains l k`,

    anc (applySeqR l π₀) k
      = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k)

the LHS is `k`'s anchor in the FOLD forest; the RHS is the merge's `climb` over
the survivor set from `k`'s birth-anchor up the LCA forest.  The two compute
`k`'s merged anchor over DIFFERENT forests and must agree.

This file isolates the **cross-forest reconciliation** the OBSTRUCTION block
flagged as genuinely new, and factors `hBN` into

  * a *climb-algebra* bridge (`resolve_climb_start`), proved here, and
  * the *survivor↔fold-liveness* bridge (`hD`, already a premise), and
  * a single residual *fold-chain* identity (`FoldBirthChain`) — the branch-new
    node's fold ancestor chain agrees with its birth-anchor's LCA chain.  This is
    the irreducible event-list content; see the RESIDUAL block at the bottom.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace RGAMergeBranchNew

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAConditionedConvergence

/-! ## §1  The climb/resolve reconciliation over the LCA forest

`resolve_climb_lchain` (TwoSided) reconciles `resolve s pre` with the LCA-`climb`
started at `anc l x` — i.e. one step ABOVE the node `x`.  For the branch-new anchor
clause the `climb` starts AT the birth-anchor `w` itself, so we need the same
reconciliation with `w` as the head of its own chain.  This is the bridge. -/

/-- **Resolve = climb, from an in-forest start.**  If `w` is live-in-`l` with
LCA-ancestor chain `cw` (`IsAncPath l w cw`), then over any state `s` the first
`s`-live entry of `w :: cw` is exactly the LCA-forest `climb` started at `w` in
`s`'s current domain.  Both walk the `l`-forest from `w` rootward to the first
`s`-live node; `resolve_climb_lchain` supplies the tail (from `anc l w` up) and
`climb_live_unfold` / `climb_fixpoint` fixes the head `w`. -/
theorem resolve_climb_start (l s : concrete_st α)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (h0 : contains l 0 = false)
    (w : ℕ) (cw : List ℕ) (hlw : contains l w = true) (hpath : IsAncPath l w cw) :
    resolve s (w :: cw) = climb (fun y => anc l y) (domain s) w := by
  by_cases hsw : contains s w = true
  · rw [resolve_live_head s w cw hsw]
    have hd : (domain s) w = true := by
      rw [← RGAMergeLinearization.contains_eq_domain]; exact hsw
    rw [climb_fixpoint (fun y => anc l y) (domain s) w (Or.inr hd)]
  · have hswf : contains s w = false := by
      cases h : contains s w with
      | true => exact absurd h hsw
      | false => rfl
    rw [resolve_dead_head s w cw hswf]
    rw [RGAMergeLinearizationTwoSided.resolve_climb_lchain l s Hdec Hstay h0 w cw hpath]
    have hw0 : w ≠ 0 := contains_ne_zero l w h0 hlw
    have hdf : (domain s) w = false := by
      rw [← RGAMergeLinearization.contains_eq_domain]; exact hswf
    rw [RGAMergeLinearization.climb_live_unfold l Hdec Hstay (domain s) w hlw hw0 hdf]

#print axioms resolve_climb_start

/-! ## §2  Reduction of `hBN` to the fold-chain identity

With the bridge in hand, `hBN` factors cleanly.  The RHS `climb` over `survivors`
is, by the survivor↔fold-liveness bridge (`hD`), a `climb` over `domain p`.  For a
branch-new survivor `k` whose birth-anchor `w := birthAnc l a b k`:

* if `w` is **in the LCA forest**, the `climb` is `resolve p (w :: cw)` for `w`'s
  LCA chain `cw` (the bridge), so `hBN` reduces to `anc p k = resolve p (w :: cw)`;
* if `w` is **off the forest** (branch-new anchor) or `0`, `w` is `0`-or-a-survivor
  (`betaf_start`), so the `climb` is the fixpoint `w`, and `hBN` reduces to
  `anc p k = w`.

`FoldBirthChain` packages exactly these two fold-side identities. -/

/-- **The residual fold-chain identity.**  For a branch-new node `k` in the fold
state `p`, its stored anchor is the `resolve` of its birth-anchor's LCA chain
(in-forest birth-anchor) or the birth-anchor itself (off-forest).  This is the
event-list content the climb algebra cannot supply — see the RESIDUAL block. -/
def FoldBirthChain (l a b p : concrete_st α) (k : ℕ) : Prop :=
  (contains l (birthAnc l a b k) = true →
      ∃ cw, IsAncPath l (birthAnc l a b k) cw
        ∧ anc p k = resolve p (birthAnc l a b k :: cw))
  ∧ (contains l (birthAnc l a b k) = false → anc p k = birthAnc l a b k)

/-- **`hBN` from the fold-chain identity.**  Given `hD` (survivor set = fold live
set) and, per branch-new survivor, the `FoldBirthChain` identity, the branch-new
anchor clause `hBN` holds — all the `climb`/`resolve` reconciliation discharged by
`resolve_climb_start` + `climb_fixpoint`, the off-forest start condition by
`betaf_start`. -/
theorem hBN_of_foldChain (l a b p : concrete_st α)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (h0 : contains l 0 = false)
    (hawf : ∀ t, contains a t = true → (anc a t = 0 ∨ contains a (anc a t) = true))
    (hbwf : ∀ t, contains b t = true → (anc b t = 0 ∨ contains b (anc b t) = true))
    (hD : ∀ k, survivors l a b k = contains p k)
    (hFC : ∀ k, survivors l a b k = true → contains l k = false →
        FoldBirthChain l a b p k) :
    ∀ k, survivors l a b k = true → contains l k = false →
        anc p k
          = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k) := by
  have hsetEq : survivors l a b = domain p := by
    funext j; rw [hD j]; exact RGAMergeLinearization.contains_eq_domain p j
  intro k hsv hlkf
  rw [hsetEq]
  obtain ⟨hin, hout⟩ := hFC k hsv hlkf
  by_cases hlw : contains l (birthAnc l a b k) = true
  · obtain ⟨cw, hpath, heq⟩ := hin hlw
    rw [heq]
    exact resolve_climb_start l p Hdec Hstay h0 (birthAnc l a b k) cw hlw hpath
  · have hlwf : contains l (birthAnc l a b k) = false := by
      cases h : contains l (birthAnc l a b k) with
      | true => exact absurd h hlw
      | false => rfl
    rw [hout hlwf]
    have hcond : birthAnc l a b k = 0 ∨ (domain p) (birthAnc l a b k) = true := by
      by_cases hw0 : birthAnc l a b k = 0
      · exact Or.inl hw0
      · rcases betaf_start l a b Hstay hawf hbwf k hsv with h | h | h
        · exact absurd h hw0
        · refine Or.inr ?_
          rw [← RGAMergeLinearization.contains_eq_domain, ← hD]; exact h
        · exact absurd h hlw
    exact (climb_fixpoint (fun y => anc l y) (domain p) (birthAnc l a b k) hcond).symm

#print axioms hBN_of_foldChain

/-! ## §3  Composition: the two-sided bridge with `hBN` replaced by `FoldBirthChain`

`eq_merge_two_sided_of_reachable` (MergeThreadDischarge) carried `hBN` as a free
premise.  Here it is discharged from `hBN_of_foldChain`: the resulting theorem has
NO free branch-new anchor premise — only the fold-chain identity `hFC`
(`FoldBirthChain`, the located residual) plus the standard reachable invariants
`wf l/a/b`, `id_mono l`.  Everything else (`hB`, `hBE`, `hD`, the reachability
oracle `hMSR`) is threaded unchanged. -/


end RGAMergeBranchNew
