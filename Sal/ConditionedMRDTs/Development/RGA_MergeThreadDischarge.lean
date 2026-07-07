import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeLinearization_TwoSided
import Sal.ConditionedMRDTs.Development.RGA_InterleavedThreading

/-!
# Discharging the merge-side `hThread` via the proved Key Lemma

*Additive; not committed; 0 `sorry` in what is kept.*

`RGA_MergeLinearization_TwoSided.eq_merge_two_sided` proves the two-sided bridge
`merge l a b ≈ fold l π` CONDITIONAL on `hThread : BranchInv2 l a b (applySeqR l π₀)`
and a restricted swap oracle `hSwap`.  Its residual obstruction was located in two
narrower facts (GAP-2′ and GAP-1, see that file's OBSTRUCTION block).

This file supplies the now-proved subchain-resolution Key Lemma
(`RGA_SubchainResolve.subchain_resolve`, via `RGARecPathFaithful.RecPathFaithful`)
into the cross-branch `Del`-preservation slot, closing GAP-2′.
-/

set_option maxHeartbeats 1000000

namespace RGAMergeThreadDischarge

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAConditionedConvergence
open RGAMergeLinearization (BranchInv)
open RGAMergeLinearizationTwoSided
  (BranchInv2 birthEl eq_merge2_of_branchInv2 branchInv_doDel_crossBranch eq_merge_two_sided)
open RGARecPathFaithful
  (RecPathFaithful target recPath resolve_recPath_of_recPathFaithful
   faithful_of_recPathFaithful)
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful NoFreshClash)

/-! ## §1  GAP-2′ closed: cross-branch `Del` with the CORRECT `hres` supply

The documented GAP-2′.  `branchInv_doDel_crossBranch` (in the TwoSided file) preserves
`BranchInv l` under `Del pre x` given `hres : contains a x → resolve a pre = anc a x`;
its former supply lemma `hres_of_lchain` demanded that `pre` be `x`'s FULL `l`-chain
(`IsAncPath l x pre`), which FAILS when `Eb` deleted an `l`-ancestor of `x` before `x`
and rehoming shortened the carried path to a proper live subchain.

The Key Lemma supplies `hres` directly: if the `Del` event is `RecPathFaithful` at the
running state `a` — its recorded path was the genuine live ancestor chain of `x` at some
capture state, and `a` is reachable from there by `okStep`-conditioned steps — then
`resolve a pre = anc a x` regardless of whether `pre` is the full `l`-chain.  This is
exactly the witness case `l = 0←1←2←3, Eb = [Del [1] 2, Del [1] 3]`: the `Del` of `3`
carries `[1]` (a proper live subchain of `3`'s `l`-chain `[2,1]`), and
`resolve a [1] = anc a 3 = 1`. -/

/-- **GAP-2′ closed.**  Cross-branch `Del`-preservation of `BranchInv l`, with `hres`
re-supplied from the subchain-resolution Key Lemma via `RecPathFaithful` — no full
`l`-chain requirement, no `accurate a`. -/
theorem branchInv_doDel_crossBranch_sub (l a : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (ha0 : contains a 0 = false) (hwfa : wf a)
    (hlwf : wf l) (hlmono : id_mono l) (hamono : id_mono a) (hx0 : x ≠ 0)
    (hrpf : RecPathFaithful (t, r, .Del pre x) a)
    (hbi : BranchInv l a) :
    BranchInv l (do_ a (t, r, .Del pre x)) := by
  apply branchInv_doDel_crossBranch l a t r x pre ha0 hwfa hlwf hlmono hamono hx0 ?_ hbi
  intro _
  exact resolve_recPath_of_recPathFaithful (t, r, .Del pre x) a hrpf

#print axioms branchInv_doDel_crossBranch_sub

/-! ## §2  Reduction of `BranchInv2` — where step 1 lands, and the exact residual

`BranchInv2 l a b p` splits by whether a survivor `k` is ORIGINAL (`contains l k`)
or BRANCH-NEW (`¬ contains l k`).  The reduction below shows precisely:

* the ORIGINAL-node el/anc clauses are exactly the single-sided `BranchInv l p`
  (I2/I4) modulo `domain p = survivors l a b` — and single-sided `BranchInv l p`
  is what step 1 (`branchInv_doDel_crossBranch_sub`) threads across the combined
  `Ea ++ Eb` fold (cross-branch `Del`s now preserved via the Key Lemma);
* the residual is exactly three facts on the fold `p = applySeqR l π₀`:
  `hD` (domain = survivors), `hBE` (branch-new element), and `hBN` (branch-new
  anchor).  `hBN` is GAP-1 — see the OBSTRUCTION block. -/

/-- **`BranchInv2` reduction.**  `BranchInv2 l a b p` follows from the domain
identity `hD`, the single-sided `BranchInv l p` (original-node el+anc, `hB`), and
the branch-new element/anchor clauses `hBE`/`hBN`.  The original-node anc clause is
`BranchInv`'s I4 rewritten by `domain p = survivors l a b`. -/
theorem branchInv2_of_pieces (l a b p : concrete_st)
    (hD : ∀ k, survivors l a b k = contains p k)
    (hB : BranchInv l p)
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el p k = birthEl l a b k)
    (hBN : ∀ k, survivors l a b k = true → contains l k = false →
        anc p k = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k)) :
    BranchInv2 l a b p := by
  obtain ⟨hI2, hI4, _hI3⟩ := hB
  have hdomeq : domain p = survivors l a b := by
    funext k
    rw [← RGAMergeLinearization.contains_eq_domain]; exact (hD k).symm
  refine ⟨hD, ?_, ?_⟩
  · intro k hsv
    have hpk : contains p k = true := by rw [← hD k]; exact hsv
    by_cases hlk : contains l k = true
    · have hbeta : birthEl l a b k = el l k := by
        simp only [birthEl, hlk, if_true]
      rw [hbeta]; exact hI2 k hlk hpk
    · have hlkf : contains l k = false := by
        cases h : contains l k with
        | true => exact absurd h hlk
        | false => rfl
      exact hBE k hsv hlkf
  · intro k hsv
    have hpk : contains p k = true := by rw [← hD k]; exact hsv
    by_cases hlk : contains l k = true
    · have hbeta : birthAnc l a b k = anc l k := by
        simp only [birthAnc, hlk, if_true]
      rw [hbeta]
      have h4 := hI4 k hlk hpk
      rw [hdomeq] at h4
      exact h4.symm
    · have hlkf : contains l k = false := by
        cases h : contains l k with
        | true => exact absurd h hlk
        | false => rfl
      exact hBN k hsv hlkf

#print axioms branchInv2_of_pieces

/-! ## §3  Assembly — `hThread` from the pieces, `hSwap` eliminated

`hThread_of_pieces` packages `branchInv2_of_pieces` at the reference fold.
`eq_merge_two_sided_of_reachable` then feeds it into the imported
`eq_merge_two_sided`, and — mirroring the update side — REPLACES the free swap
oracle by the both-`Faithful` reachability premise `hMSR`, discharged pointwise by
`eqSwap_of_bothFaithful` (NEITHER operand `accurate`).  Unlike the update side,
the merge fold starts at the LCA `l` (not `init_st`), so `faithful_at_interleaved_fold`
does not transport; the per-swap `Faithful`-at-`applySeqR l pre` facts are supplied
by `hMSR` (the merge-fold reachability oracle, the concurrent agent's territory). -/

/-- `BranchInv2` at the reference fold `applySeqR l π₀`, from the four pieces. -/
theorem hThread_of_pieces (l a b : concrete_st) (π₀ : List op_t)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = birthEl l a b k)
    (hBN : ∀ k, survivors l a b k = true → contains l k = false →
        anc (applySeqR l π₀) k
          = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k)) :
    BranchInv2 l a b (applySeqR l π₀) :=
  branchInv2_of_pieces l a b (applySeqR l π₀) hD hB hBE hBN


end RGAMergeThreadDischarge
