import Sal.MRDTs.Metatheory.Conditioned.RGA_MergeLinearization_TwoSided
import Sal.MRDTs.Metatheory.Conditioned.RGA_InterleavedThreading

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
open Sal.Metatheory.RGAConditionedConvergence
open RGAMergeLinearization (BranchInv)
open RGAMergeLinearizationTwoSided
  (BranchInv2 birthEl eq_merge2_of_branchInv2 branchInv_doDel_crossBranch eq_merge_two_sided)
open RGARecPathFaithful
  (RecPathFaithful target recPath resolve_recPath_of_recPathFaithful
   faithful_of_recPathFaithful)
open Sal.Metatheory.RGAGeneralSwap (Faithful NoFreshClash)

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

/-- **Two-sided bridge with `hThread` reduced to pieces and `hSwap` eliminated.**
`merge l a b ≈ fold l π` for any `lo`-respecting `π`, with NO free swap oracle and
NO bare `hThread`: `hThread` is reduced to the four `branchInv2_of_pieces` premises
(`hBN` being the residual GAP-1 branch-new anchor clause, the ONLY non-reachability
premise — see the OBSTRUCTION block) and `hSwap` to the both-`Faithful` merge-fold
reachability oracle `hMSR`. -/
theorem eq_merge_two_sided_of_reachable
    (l a b : concrete_st) (lo : op_t → op_t → Prop) (ev : Set op_t) (π₀ π : List op_t)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = birthEl l a b k)
    (hBN : ∀ k, survivors l a b k = true → contains l k = false →
        anc (applySeqR l π₀) k
          = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k))
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ lo) (hπr : respects π lo)
    (hMSR : ∀ (pre : List op_t) (x y : op_t),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup → respects pre lo →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y → ¬ lo x y → ¬ lo y x →
        (∀ z ∈ ev, z ≠ x → lo z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → lo z y → z ∈ pre) →
        x.1 ≠ y.1 ∧ contains (applySeqR l pre) 0 = false ∧ wf (applySeqR l pre)
        ∧ id_mono (applySeqR l pre)
        ∧ fresh_ts x (applySeqR l pre) ∧ fresh_ts y (applySeqR l pre)
        ∧ Faithful x (applySeqR l pre) ∧ Faithful y (applySeqR l pre)
        ∧ NoFreshClash x y ∧ NoFreshClash y x) :
    eq (merge l a b) (applySeqR l π) := by
  have hThread : BranchInv2 l a b (applySeqR l π₀) :=
    hThread_of_pieces l a b π₀ hD hB hBE hBN
  apply eq_merge_two_sided l a b lo ev π₀ π hThread h₀p hπp h₀r hπr
  intro pre x y hsub hnd hresp hx hy hxp hyp hxy hnxy hnyx henx heny
  obtain ⟨hd, h0, hwf, hmono, hfx, hfy, hFx, hFy, hcxy, hcyx⟩ :=
    hMSR pre x y hsub hnd hresp hx hy hxp hyp hxy hnxy hnyx henx heny
  exact eqSwap_of_bothFaithful (applySeqR l pre) x y hd h0 hwf hmono hfx hfy hFx hFy hcxy hcyx

#print axioms eq_merge_two_sided_of_reachable

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — what the Key Lemma closes, and the exact residual.

   CLOSED here, kernel-clean:

   • GAP-2′ (cross-branch stale-path `Del` preservation).  `branchInv_doDel_crossBranch_sub`
     re-supplies `hres : resolve a pre = anc a x` from the subchain-resolution Key
     Lemma (`RecPathFaithful (Del pre x) a`) — with NO full-`l`-chain requirement and
     NO `accurate a`.  This closes the documented witness `l = 0←1←2←3,
     Eb = [Del [1] 2, Del [1] 3]`: the `Del` of `3` carries `[1]` (a proper live
     subchain of `3`'s `l`-chain `[2,1]`), yet `resolve a [1] = anc a 3 = 1` by the
     Key Lemma, so `branchInv_doDel_crossBranch` applies where `hres_of_lchain` could
     not.  This is the GAP-2′ that the TwoSided file flagged as the residual blocker.

   • The `hSwap` oracle.  `eq_merge_two_sided_of_reachable` carries NO free `EqSwap`
     premise: it is discharged pointwise by `eqSwap_of_bothFaithful` (NEITHER operand
     `accurate`).  The per-swap both-`Faithful` inputs are the reachability oracle
     `hMSR` — the merge-fold analogue of the update side's `hReach`.  NB: the merge
     fold starts at the LCA `l`, not `init_st`, so `faithful_at_interleaved_fold`
     (init-anchored) does NOT transport; `hMSR` is a genuine merge-fold obligation.

   • Reduction of `hThread`.  `branchInv2_of_pieces` splits `BranchInv2` into
       (hD)  domain (applySeqR l π₀) = survivors l a b,
       (hB)  single-sided `BranchInv l (applySeqR l π₀)`  — threadable across Ea++Eb
             by `branchInv_doIns` (fresh ids) + `branchInv_doDel_crossBranch_sub`
             (step 1) for every `Del`, i.e. reachability-only,
       (hBE) branch-new-survivor element clause,
       (hBN) branch-new-survivor ANCHOR clause.

   NOT closed by the Key Lemma — the sharp residual (GAP-1):

   • **(hBN) branch-new survivor anchor coincidence.**  For a survivor `k` with
     `¬ contains l k` (an `a`-new or `b`-new node), `BranchInv2` demands
       anc (applySeqR l π₀) k = climb (anc l) (survivors l a b) (birthAnc l a b k),
     with `birthAnc = anc a k` / `anc b k`.  The subchain-resolution Key Lemma
     resolves a node's OWN recorded chain to its current stored anchor OVER THE
     ACTUAL FOLD FOREST — it does NOT reconcile that with a `climb` over the DISTINCT
     LCA-forest (`anc l`) started at the branch birth-anchor.  Concretely (b-new
     establishment): at `k`'s `Eb`-`Ins` birth over the combined, `a`-carrying state
     `s`, the stored anchor `resolve s (anch :: path)` generally DIFFERS from
     `anc b k = resolve b (anch :: path)` (the combined state already carries `a`'s
     deletions of `k`'s ancestors), and the two must be shown to `climb` to the same
     two-sided survivor over `anc l`.  That cross-forest reconciliation is genuinely
     NEW two-sided content, NOT expressible as a per-event reachability premise, so it
     is left as the explicit premise `hBN` rather than forced or `sorry`d.

   • (hD)/(hBE) are the minor residue: a domain (OR-set = live-set) induction and a
     branch-new birth-element preservation — reachability-flavoured, but not yet
     mechanized here; also left as explicit premises.

   VERDICT.  The Key Lemma DOES unblock the merge side's GAP-2′ (`hThread`'s
   cross-branch `Del` preservation) and eliminates the free swap oracle.  It does
   NOT, on its own, close `hThread`: the residual is GAP-1 (hBN, the branch-new
   survivor cross-forest anchor identity) plus the minor hD/hBE.  This matches — and
   sharpens — the TwoSided file's own OBSTRUCTION reading (GAP-1 branch-new + GAP-2′),
   now with GAP-2′ discharged.  It is not a divergence: `merge` and `fold` still agree
   on branch-new survivors (PBT-confirmed); the gap is the anchor-reconciliation lemma.
   ═══════════════════════════════════════════════════════════════════════════ -/

end RGAMergeThreadDischarge
