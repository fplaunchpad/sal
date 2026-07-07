import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonBirthBridge

/-!
# `RGA_BranchCanon` — discharging `CanonBirthBridge`'s merge-side residuals from
the branch/full-fold canonical characterization

`RGA_CanonBirthBridge.canonBirthBridge_holds` closes the last merge-side bridge
`CanonBirthBridge l F bw rc` (`bw = birthAnc l a b k`, `rc = a_k :: p_k`) from
three residual hypotheses — `hsplit`+`hpreDead` (the `F`-climb of the recorded
chain reaches `bw`'s recorded slot), `hout` (an off-forest `bw` survives `F`),
and the biting `hin` (`bw`'s `l`-chain and its recorded rootward tail reach the
same `F`-survivor).

This file supplies those residuals from the *canonical state* of the folds:

* §1 — `survP` set-monotonicity (the `Fa ⊆ F` bridge): a branch-dead recorded
  ancestor is a non-survivor of the two-sided set.  This drives `hpreDead`.
* §2 — `branchCanon_hout`: the off-forest birth-anchor of a survivor survives
  `F`, *straight from the full-fold `CanonMatch F` + `hD` + `betaf_start`* — no
  branch fold needed.  Clean.
* §3 — the composed bridge `canonBirthBridge_via_branchCanon`, feeding
  `canonBirthBridge_holds` with `hout` discharged and `hsplit`/`hpreDead`/`hin`
  reduced to their branch-canonical inputs.

The STATUS block (§4) records exactly which residual closes and which is the
irreducible two-sided content (the `hin` recorded-tail↔`l`-chain reconciliation).
-/

set_option maxHeartbeats 1000000

open Classical

namespace RGABranchCanon

open Sal.Emulation
open RGACanonConvergence
open RGAMergeFoldChain (CanonBirthBridge)
open RGACanonBirthBridge (canonBirthBridge_holds canonAnc_pos canonAnc_neg)

/-! ## §1  `survP` set-monotonicity — the `Fa ⊆ F` bridge -/

/-! ## §2  `hout` — the off-forest birth-anchor survives `F` (clean, full-fold)

`bw = birthAnc l a b k` is `k`'s branch-final anchor.  When `bw` is *off the LCA
forest* (`contains l bw = false`) and nonzero, `betaf_start` forces `bw` to be a
survivor (a branch-new anchor lies in a branch's `difference` set), and the
full-fold `CanonMatch F fold` + `hD` (survivor set = fold live set) turn that into
`survP F bw`.  This uses only the two-sided fold's canonical state — NOT the
branch fold — so no single-vs-two-sided reconciliation is involved. -/

/-- The off-forest branch-final anchor of a survivor survives the two-sided set
`F`.  (`hbwne` is genuinely needed: `birthAnc l a b k = 0` — `k` anchored at the
root in its branch — is off-forest but not a survivor; that degenerate case is
handled by `canonAnc F rc = 0` directly, not by `hout`.) -/
theorem branchCanon_hout
    (l a b : concrete_st) (F : List op_t) (fold : concrete_st) (k : ℕ)
    (hlwf : ∀ t, contains l t = true → (anc l t = 0 ∨ contains l (anc l t) = true))
    (hawf : ∀ t, contains a t = true → (anc a t = 0 ∨ contains a (anc a t) = true))
    (hbwf : ∀ t, contains b t = true → (anc b t = 0 ∨ contains b (anc b t) = true))
    (hD : ∀ j, survivors l a b j = contains fold j)
    (hcm : CanonMatch F fold)
    (hsv : survivors l a b k = true)
    (hbwne : birthAnc l a b k ≠ 0) :
    contains l (birthAnc l a b k) = false → survP F (birthAnc l a b k) := by
  intro hlbw
  rcases betaf_start l a b hlwf hawf hbwf k hsv with h | h | h
  · exact absurd h hbwne
  · have hcf : contains fold (birthAnc l a b k) = true := by rw [← hD]; exact h
    exact (hcm.1 (birthAnc l a b k)).mp hcf
  · rw [hlbw] at h; exact Bool.noConfusion h

/-! ## §3  The composed bridge — `hout` discharged, residual reduced to
`hsplit`/`hpreDead`/`hin`

`canonBirthBridge_via_branchCanon` feeds `canonBirthBridge_holds` with `hout`
built by §2.  The caller supplies only:
* `hsplit` — `bw` sits on the recorded chain (from the branch `LiveChain`: `bw`
  is the head of `k`'s live-filtered recorded chain in its branch fold);
* `hpreDead` — the nearer recorded entries are non-`F`-survivors (§1's
  `hpreDead_of_branchDeleted`, from branch-deletion + `Fa ⊆ F`);
* `hin` — the in-forest recorded-tail↔`l`-chain reconciliation (the located
  two-sided residual; see §4). -/

/-- **`CanonBirthBridge` from the branch-canonical residuals, `hout` discharged.**
For a survivor `k` with branch-final anchor `bw = birthAnc l a b k` and recorded
chain `rc`, the merge-side bridge holds given the recorded-chain split (`hsplit`),
the dead-prefix fact (`hpreDead`), and the in-forest reconciliation (`hin`).
`hout` is supplied internally from the full-fold `CanonMatch F fold` + `hD`. -/
theorem canonBirthBridge_via_branchCanon
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
    (hin : contains l (birthAnc l a b k) = true →
        ∃ cw, IsAncPath l (birthAnc l a b k) cw ∧ canonAnc F cw = canonAnc F rcSuf) :
    CanonBirthBridge l F (birthAnc l a b k) rc :=
  canonBirthBridge_holds l F (birthAnc l a b k) rc rcPre rcSuf hsplit hpreDead
    (branchCanon_hout l a b F fold k hlwf hawf hbwf hD hcm hsv hbwne) hin

#print axioms canonBirthBridge_via_branchCanon

/-! ## §3.5  Pinning `hin` to the survivor-subsequence coincidence

`canonAnc F L` is the head of `L`'s `F`-survivor subsequence (or `0`): it skips
non-survivors and stops at the first survivor.  So it depends on `L` *only through
that subsequence* — inserting or deleting non-survivors is invisible.  This lets us
pin `hin` (`canonAnc F cw = canonAnc F rcSuf`) to a single crisp fact: `bw`'s
`F`-surviving recorded ancestors equal its `F`-surviving `l`-ancestors, in order. -/

/-! ## §4  STATUS — which merge-side residual closed, and the exact residual

**Both `#print axioms` are kernel-clean** (`[propext, Classical.choice,
Quot.sound]`).  The three `CanonBirthBridge` residuals split as follows.

* **`hout` — CLOSED, clean (§2).**  The off-forest branch-final anchor of a
  survivor survives `F` straight from the *two-sided* fold's own canonical state
  (`hcm : CanonMatch F fold` + `hD` + `betaf_start`).  No branch fold, no
  single-vs-two-sided reconciliation.  (Caveat: needs `birthAnc ≠ 0`; the `bw = 0`
  root-anchored case is off-forest but non-surviving and is instead handled by
  `canonAnc F rc = 0` directly.)

* **`hpreDead` — REDUCED, mechanized (§1).**  The nearer recorded entries are
  non-`F`-survivors *because they were deleted in the branch fold*: `notSurv_of_
  branchDeleted` turns `deletedIn Fa c` into `¬ survP F c` via `Fa ⊆ F` (the
  branch's own `Del` events are also in the two-sided `F`).  The input
  `deletedIn Fa c` for the prefix entries is a real branch-fold fact (they sit
  below `bw`, the head of `k`'s live-filtered recorded chain in its branch fold).

* **`hsplit` — branch `LiveChain` fact.**  `bw = birthAnc l a b k = anc(branch) k`
  is the head of `k`'s live-filtered recorded chain in its branch fold
  (`subchain_resolve` / `CanonInv`'s `LiveChain`), hence sits on `rc`.  A real
  execution fact; taken as input to the composed bridge.

* **`hin` — the LOCATED two-sided residual (§3.5).**  Pinned to a single crisp
  fact: `rcSuf.filter (survB F) = cw.filter (survB F)` — `bw`'s `F`-surviving
  recorded ancestors equal its `F`-surviving `l`-ancestors, in order.  ALL climb
  algebra around it is discharged (`canonAnc_filter_surv` + `hin_of_survFilterEq`).

**The exact mismatch (single-sided vs two-sided).**  `canon_fold` on the *branch*
`a = applySeqR l Ea` gives `CanonMatch Fa a`, i.e. `anc a k = canonAnc Fa (rc)` —
`k`'s branch-final anchor is `canonAnc` over the **branch** survivor set `Fa`.  But
`CanonBirthBridge` is stated over `canonAnc F` with `F` the **two-sided** applied
set (`Fa ∪ Fb`).  The reconciliation `canonAnc Fa → canonAnc F` is NOT a corollary
of the branch's canonical state; it needs cross-branch structure that a single
branch fold does not carry:

  1. `Fa ⊆ F` (branch `Del`s ⊆ two-sided `Del`s) — supplied here as an explicit
     set-inclusion premise; drives `hpreDead` (§1).  Clean.
  2. an off-forest `bw = anc a k` (a branch-new node) is not deleted by the *other*
     branch — here obtained via `betaf_start` (a-new ⇒ survivor) + `hD` + `hcm`,
     so `hout` needs no separate faithfulness premise.  Clean.
  3. `bw`'s recorded rootward tail `rcSuf` (captured in *branch-`a`-at-insert*) and
     `bw`'s LCA-forest chain `cw` have the same `F`-surviving subsequence.  This is
     `hin`.  It is TRUE — the entries of `cw` missing from `rcSuf` were deleted in
     `Ea` before `k`'s insert (hence `F`-dead), and `rcSuf` adds no non-`l` entries
     (insertion never splices into an existing ancestor chain) — but establishing
     the subsequence coincidence is a *branch-fold event-list induction*
     (`foldChain_of_goodFold`, the `RGA_MergeBranchNew` OBSTRUCTION), threading a
     chain-level analogue of `BranchInv`'s I4 across `Ea ++ Eb`.  It is exactly the
     "resolve a node's recorded chain over the ACTUAL fold forest vs. climb the
     DISTINCT LCA forest" gap the OBSTRUCTION block named as irreducible two-sided
     content — NOT expressible as, or derivable from, a single branch's
     `CanonMatch`.

**VERDICT.**  `canon_fold` on the branch discharges `hout` (via the full two-sided
`CanonMatch`, not the branch one), and reduces `hpreDead` to `Fa ⊆ F`
monotonicity; `hsplit` is the branch `LiveChain` head.  It does NOT discharge
`hin`: `birthAnc` is `canonAnc Fa` (single-sided) while the bridge is `canonAnc F`
(two-sided), and the recorded-tail↔`l`-chain survivor coincidence they must share
is `foldChain_of_goodFold` — a genuine single-vs-two-sided gap, now pinned (§3.5)
to the crisp subsequence equality `rcSuf.filter (survB F) = cw.filter (survB F)`,
sorry-free, with every surrounding step mechanized. -/

end RGABranchCanon
