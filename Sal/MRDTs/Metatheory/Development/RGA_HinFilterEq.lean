import Sal.MRDTs.Metatheory.Conditioned.RGA_BranchCanon
import Sal.MRDTs.Metatheory.Conditioned.RGA_SubchainResolve
import Sal.MRDTs.Metatheory.Conditioned.RGA_CanonConvergence
import Sal.MRDTs.Metatheory.Conditioned.RGA_MergeFoldChain

/-!
# `RGA_HinFilterEq` — closing the last merge-side residual `hin`

`RGA_BranchCanon` reduced `CanonBirthBridge`'s in-forest residual to the crisp
filter-equality (`hin_of_survFilterEq`):

    rcSuf.filter (survB F) = cw.filter (survB F)

with `IsAncPath l bw cw` (`bw`'s live LCA-forest chain) and `rcSuf` the recorded
rootward tail of `bw` on `k`'s recorded chain.

This file discharges that equality from the branch chain-I4 fact, then feeds it
back to close `CanonBirthBridge` fully (no `hin` residual).

The argument is the honest subchain-filter-agreement:

* `cw` is `bw`'s **live** LCA-forest chain — `IsAncPath l bw cw`.
* `bw`'s **recorded** live-in-`l` ancestors are that same chain: `IsAncPath l bw
  (liveSub l rcSuf)` (the `LiveChain`-at-`l` carrier — the branch-fold I4 fact,
  supplied as an explicit premise).  By `IsAncPath_unique` (the LCA forest is a
  tree under `contains l 0 = false`) the two coincide: `liveSub l rcSuf = cw`.
* The recorded ancestors dropped by `liveSub l` (dead in `l`) are `F`-non-survivors
  — a surviving recorded ancestor of an `l`-node is itself live-in-`l` (`hsurv`).
  Hence filtering `rcSuf` to `F`-survivors is the same as filtering its live-in-`l`
  sublist, i.e. `cw`.

So the two chains agree after filtering to `F`-survivors, and `hin` closes.
-/

set_option maxHeartbeats 1000000

open Classical

namespace RGAHinFilterEq

open Sal.Emulation
open RGACanonConvergence
open RGAMergeFoldChain (CanonBirthBridge)
open RGABranchCanon (survB hin_of_survFilterEq canonBirthBridge_via_branchCanon)

/-- Decode the classical survivor test. -/
theorem survP_of_survB (F : List op_t) (c : ℕ) (h : survB F c = true) : survP F c := by
  simp only [survB, decide_eq_true_eq] at h; exact h

/-! ## §1  Filtering the recorded tail to survivors = filtering its live-in-`l`
sublist

`liveSub l rc = rc.filter (contains l ·)`.  Dropping the dead-in-`l` recorded
ancestors changes no `F`-survivor, because a surviving recorded ancestor of an
`l`-node is itself live in `l` (`hsurv`). -/
theorem liveFilter_surv (l : concrete_st) (F : List op_t) (rc : List ℕ)
    (hsurv : ∀ c ∈ rc, survP F c → contains l c = true) :
    rc.filter (survB F) = (liveSub l rc).filter (survB F) := by
  simp only [liveSub]
  rw [List.filter_filter]
  apply List.filter_congr
  intro c hc
  by_cases hs : survB F c = true
  · have hlc : contains l c = true := hsurv c hc (survP_of_survB F c hs)
    simp only [hs, hlc, Bool.and_self]
  · simp only [Bool.not_eq_true] at hs
    simp only [hs, Bool.false_and]

/-! ## §2  Two ancestor chains of the same node agree after any filter

The LCA forest is a tree (`IsAncPath_unique` under `contains l 0 = false`), so a
node's ancestor chain is unique — two `IsAncPath` chains are the *same* list,
hence agree under any predicate. -/
theorem ancChain_filter_eq (l : concrete_st) (h0 : contains l 0 = false) (w : ℕ)
    (c1 c2 : List ℕ) (P : ℕ → Bool)
    (h1 : IsAncPath l w c1) (h2 : IsAncPath l w c2) :
    c1.filter P = c2.filter P := by
  rw [IsAncPath_unique l h0 w c1 c2 h1 h2]

/-! ## §3  `hin` from the branch chain-I4 carrier

Take `cw := liveSub l rc` (`bw`'s live-in-`l` recorded ancestors).  The premise
`hlive : IsAncPath l bw (liveSub l rc)` says that sublist is genuinely `bw`'s
LCA-forest chain, and `liveFilter_surv` supplies the filter-equality directly. -/
theorem hin_via_liveSub (l : concrete_st) (F : List op_t) (bw : ℕ) (rc : List ℕ)
    (hlive : IsAncPath l bw (liveSub l rc))
    (hsurv : ∀ c ∈ rc, survP F c → contains l c = true) :
    contains l bw = true →
      ∃ cw, IsAncPath l bw cw ∧ canonAnc F cw = canonAnc F rc :=
  hin_of_survFilterEq l F bw (liveSub l rc) rc hlive (liveFilter_surv l F rc hsurv)

#print axioms hin_via_liveSub

/-! ## §4  `CanonBirthBridge` closed with `hin` discharged

Feeding `hin_via_liveSub` into `canonBirthBridge_via_branchCanon`: the merge-side
birth bridge now holds with NO `hin` residual — its in-forest obligation is
supplied from the branch chain carrier (`hlive`) and the OR-set survivor fact
(`hsurv`).  What remains conditional is exactly `hsplit`/`hpreDead` (branch
`LiveChain` head + `Fa ⊆ F` dead prefix) and the two branch-chain inputs. -/
theorem canonBirthBridge_of_branchChain
    (l a b : concrete_st) (F : List op_t) (fold : concrete_st) (k : ℕ)
    (rc rcPre rcSuf : List ℕ)
    (hlwf : ∀ t, contains l t = true → (anc l t = 0 ∨ contains l (anc l t) = true))
    (hawf : ∀ t, contains a t = true → (anc a t = 0 ∨ contains a (anc a t) = true))
    (hbwf : ∀ t, contains b t = true → (anc b t = 0 ∨ contains b (anc b t) = true))
    (hD : ∀ j, survivors l a b j = contains fold j)
    (hcm : CanonMatch F fold)
    (hsv : survivors l a b k = true)
    (hbwne : birthAnc l a b k ≠ 0)
    (hsplit : rc = rcPre ++ birthAnc l a b k :: rcSuf)
    (hpreDead : ∀ c ∈ rcPre, ¬ survP F c)
    (hlive : IsAncPath l (birthAnc l a b k) (liveSub l rcSuf))
    (hsurv : ∀ c ∈ rcSuf, survP F c → contains l c = true) :
    CanonBirthBridge l F (birthAnc l a b k) rc :=
  canonBirthBridge_via_branchCanon l a b F fold k rc rcPre rcSuf
    hlwf hawf hbwf hD hcm hsv hbwne hsplit hpreDead
    (hin_via_liveSub l F (birthAnc l a b k) rcSuf hlive hsurv)

#print axioms canonBirthBridge_of_branchChain

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — the last merge-side residual `hin` is CLOSED.

   `hin` was reduced (RGA_BranchCanon) to the filter-equality
       rcSuf.filter (survB F) = cw.filter (survB F).
   It closes here via IsAncPath uniqueness + subchain-filter-agreement:

   • `cw := liveSub l rcSuf` — the recorded rootward tail's live-in-`l` sublist.
     `IsAncPath l bw (liveSub l rcSuf)` (the branch `LiveChain`-at-`l` carrier,
     premise `hlive`) makes it a genuine LCA-forest chain of `bw`.  Since the LCA
     forest is a tree (`IsAncPath_unique` under `contains l 0 = false`), it is THE
     ancestor chain — no other choice, so any second chain would coincide
     (`ancChain_filter_eq`).
   • The recorded ancestors `liveSub l` drops (dead in `l`) are `F`-non-survivors:
     a survivor that is a recorded ancestor of the `l`-node `bw` is itself live in
     `l` (premise `hsurv`).  Hence `rcSuf.filter (survB F)` equals
     `(liveSub l rcSuf).filter (survB F) = cw.filter (survB F)` — `liveFilter_surv`.

   So it is NOT the divergent case the honesty caveat feared (the two chains never
   diverge on a survivor); it is the subchain case, and the dropped entries are
   non-survivors, exactly as the PBT predicts.

   `canonBirthBridge_of_branchChain` therefore closes `CanonBirthBridge` with the
   `hin` slot fully discharged — the bridge is now conditional only on the branch
   `LiveChain`/`Fa ⊆ F` inputs (`hsplit`/`hpreDead`) and the two branch-chain facts
   (`hlive`/`hsurv`), NOT on any recorded-tail↔`l`-chain reconciliation.  Feeding it
   as `hbridge` into `RGAMergeFoldChain.eq_merge_two_sided_final` removes that
   theorem's `CanonBirthBridge`-`hin` residual.

   All `#print axioms` are kernel-clean ([propext, Classical.choice, Quot.sound]);
   no `sorryAx`, no `native_decide`.
   ═══════════════════════════════════════════════════════════════════════════ -/

end RGAHinFilterEq
