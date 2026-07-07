import Sal.MRDTs.Metatheory.Conditioned.RGA_MergeThreadDischarge

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

namespace RGAMergeBranchNew

open Sal.Emulation
open Sal.Metatheory.RGAConditionedConvergence

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
theorem resolve_climb_start (l s : concrete_st)
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
def FoldBirthChain (l a b p : concrete_st) (k : ℕ) : Prop :=
  (contains l (birthAnc l a b k) = true →
      ∃ cw, IsAncPath l (birthAnc l a b k) cw
        ∧ anc p k = resolve p (birthAnc l a b k :: cw))
  ∧ (contains l (birthAnc l a b k) = false → anc p k = birthAnc l a b k)

/-- **`hBN` from the fold-chain identity.**  Given `hD` (survivor set = fold live
set) and, per branch-new survivor, the `FoldBirthChain` identity, the branch-new
anchor clause `hBN` holds — all the `climb`/`resolve` reconciliation discharged by
`resolve_climb_start` + `climb_fixpoint`, the off-forest start condition by
`betaf_start`. -/
theorem hBN_of_foldChain (l a b p : concrete_st)
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

/-- **Two-sided bridge, branch-new anchor discharged.**  `merge l a b ≈ fold l π`
with `hBN` replaced by the fold-chain identity `hFC` (`FoldBirthChain` per
branch-new survivor) together with the reachable invariants.  The free `hBN` of
`eq_merge_two_sided_of_reachable` is gone: it is built by `hBN_of_foldChain`. -/
theorem eq_merge_two_sided_of_foldChain
    (l a b : concrete_st) (lo : op_t → op_t → Prop) (ev : Set op_t) (π₀ π : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hawf : wf a) (hbwf : wf b)
    (h0 : contains l 0 = false)
    (hD : ∀ k, survivors l a b k = contains (applySeqR l π₀) k)
    (hB : RGAMergeLinearization.BranchInv l (applySeqR l π₀))
    (hBE : ∀ k, survivors l a b k = true → contains l k = false →
        el (applySeqR l π₀) k = RGAMergeLinearizationTwoSided.birthEl l a b k)
    (hFC : ∀ k, survivors l a b k = true → contains l k = false →
        FoldBirthChain l a b (applySeqR l π₀) k)
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
        ∧ Sal.Metatheory.RGAGeneralSwap.Faithful x (applySeqR l pre)
        ∧ Sal.Metatheory.RGAGeneralSwap.Faithful y (applySeqR l pre)
        ∧ Sal.Metatheory.RGAGeneralSwap.NoFreshClash x y
        ∧ Sal.Metatheory.RGAGeneralSwap.NoFreshClash y x) :
    eq (merge l a b) (applySeqR l π) := by
  have hHdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y := by
    intro y hy hy0; rcases hlmono y hy with h | h
    · omega
    · exact h
  have hBN : ∀ k, survivors l a b k = true → contains l k = false →
      anc (applySeqR l π₀) k
        = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k) :=
    hBN_of_foldChain l a b (applySeqR l π₀) hHdec hlwf h0 hawf hbwf hD hFC
  exact RGAMergeThreadDischarge.eq_merge_two_sided_of_reachable
    l a b lo ev π₀ π hD hB hBE hBN h₀p hπp h₀r hπr hMSR

#print axioms eq_merge_two_sided_of_foldChain

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — `hBN` (GAP-1), what closed and the exact residual.

   CLOSED here, kernel-clean ([propext, Classical.choice, Quot.sound] only):

   • The CROSS-FOREST RECONCILIATION bridge (`resolve_climb_start`).  The
     OBSTRUCTION block named this as "genuinely NEW two-sided content": the merge's
     `climb` over the LCA forest and the fold's `resolve` of the recorded chain
     compute over DIFFERENT forests.  `resolve_climb_start` proves they agree for an
     in-forest start `w`:  `resolve s (w :: cw) = climb (anc l) (domain s) w`  when
     `IsAncPath l w cw`.  This is the exact climb=resolve identity the branch-new
     anchor clause needs, generalizing `resolve_climb_lchain` (which started one step
     above `w`, at `anc l w`) to start AT the birth-anchor `w`.

   • The SURVIVOR↔FOLD-LIVENESS bridge is exactly `hD`
     (`survivors l a b = contains (applySeqR l π₀)`), already a premise; here it is
     used as the set identity `survivors l a b = domain (applySeqR l π₀)` to swap the
     `climb` stop-set, and (via `betaf_start`) to discharge the off-forest fixpoint.

   • `hBN` REDUCTION (`hBN_of_foldChain`) + COMPOSITION
     (`eq_merge_two_sided_of_foldChain`).  `hBN` now follows from the per-node
     fold-chain identity `FoldBirthChain` alone; the composed two-sided bridge no
     longer carries a free `hBN` — it carries `hFC : FoldBirthChain …` plus the
     standard reachable invariants `wf l/a/b`, `id_mono l`, `contains l 0 = false`.
     All `climb`/`resolve` algebra is discharged.

   NOT closed — the sharp residual (`FoldBirthChain`, the fold-chain identity):

   • For a branch-new survivor `k`, `FoldBirthChain` demands, with `w := birthAnc`:
       (in-forest w)   ∃ cw, IsAncPath l w cw ∧ anc p k = resolve p (w :: cw)
       (off-forest w)  anc p k = w                                    (p = fold)
     This is what `subchain_resolve` (`RGA_SubchainResolve`) yields — `resolve p ck
     = anc p k` — PROVIDED `k`'s genuine fold ancestor chain `ck` equals `w :: cw`,
     i.e. `k`'s rootward chain in the fold coincides with its BIRTH-ANCHOR's LCA
     chain.  It does NOT hold definitionally: `k`'s fold chain is headed by `k`'s
     FOLD-BIRTH resolved anchor, whereas `w = anc a k` / `anc b k` is `k`'s
     BRANCH-FINAL anchor.  Reconciling the two (the mismatch the OBSTRUCTION block
     flagged: "the stored anchor `resolve s (anch::path)` generally DIFFERS from
     `anc b k`") needs the EVENT-LIST fold invariant — a branch-new analogue of
     `BranchInv`'s I4 threaded through `Ea ++ Eb` via `GoodBranchFold`, using
     cross-branch faithfulness (an `Eb`-`Del` never targets an `a`-new node; a
     `b`-new birth over the `a`-carrying combined state climbs to the same survivor).

   EXACT STUCK GOAL (the missing bridge lemma, name it `foldChain_of_goodFold`):
       ⊢ FoldBirthChain l a b (applySeqR l (Ea ++ Eb)) k
     for every branch-new survivor `k`, given `a = applySeqR l Ea`,
     `b = applySeqR l Eb`, and the `GoodBranchFold`/faithfulness data for Ea, Eb.
     This is a genuine event-list induction (branch-new I4 preservation across every
     `Eb` step + establishment at `a` / at each `b`-new `Ins` birth), NOT expressible
     as a per-event reachability premise — matching the OBSTRUCTION's reading that
     the branch-new cross-forest anchor identity is irreducible two-sided content.
   ═══════════════════════════════════════════════════════════════════════════ -/

end RGAMergeBranchNew
