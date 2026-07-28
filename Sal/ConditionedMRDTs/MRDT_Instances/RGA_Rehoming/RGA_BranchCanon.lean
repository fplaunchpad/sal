import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonBirthBridge

/-!
# `RGA_BranchCanon`: discharging `CanonBirthBridge`'s merge-side residuals from
the branch/full-fold canonical characterization

`RGA_CanonBirthBridge.canonBirthBridge_holds` closes the last merge-side bridge
`CanonBirthBridge l F bw rc` (`bw = birthAnc l a b k`, `rc = a_k :: p_k`) from
three residual hypotheses, `hsplit`+`hpreDead` (the `F`-climb of the recorded
chain reaches `bw`'s recorded slot), `hout` (an off-forest `bw` survives `F`),
and the biting `hin` (`bw`'s `l`-chain and its recorded rootward tail reach the
same `F`-survivor).

This file supplies those residuals from the *canonical state* of the folds:

* §1, `survP` set-monotonicity (the `Fa ⊆ F` bridge): a branch-dead recorded
  ancestor is a non-survivor of the two-sided set.  This drives `hpreDead`.
* §2, `branchCanon_hout`: the off-forest birth-anchor of a survivor survives
  `F`, *straight from the full-fold `CanonMatch F` + `hD` + `betaf_start`*, no
  branch fold needed.  Clean.
* §3, the composed bridge `canonBirthBridge_via_branchCanon`, feeding
  `canonBirthBridge_holds` with `hout` discharged and `hsplit`/`hpreDead`/`hin`
  reduced to their branch-canonical inputs.

§4 records exactly which residual closes and which is the irreducible two-sided
content (the `hin` recorded-tail↔`l`-chain reconciliation).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Classical

namespace RGABranchCanon

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open RGACanonConvergence
open RGAMergeFoldChain (CanonBirthBridge)
open RGACanonBirthBridge (canonBirthBridge_holds canonAnc_pos canonAnc_neg)

/-! ## §1  `survP` set-monotonicity: the `Fa ⊆ F` bridge -/

/-- `deletedIn` is monotone in the applied set (membership inclusion). -/
theorem deletedIn_mono (F₁ F₂ : List (op_t α)) (hsub : ∀ o, o ∈ F₁ → o ∈ F₂) (c : ℕ)
    (h : deletedIn F₁ c) : deletedIn F₂ c := by
  obtain ⟨t, r, p, hm⟩ := h
  exact ⟨t, r, p, hsub _ hm⟩

/-- A recorded ancestor **deleted in the branch set** `Fa` cannot survive the
two-sided set `F ⊇ Fa`: the branch's own `Del` event is also in `F`.  This is the
OR-set reconciliation `hpreDead` runs on, a branch-dead nearer recorded entry is
a non-`F`-survivor. -/
theorem notSurv_of_branchDeleted (Fa F : List (op_t α)) (hsub : ∀ o, o ∈ Fa → o ∈ F)
    (c : ℕ) (h : deletedIn Fa c) : ¬ survP F c :=
  fun hsv => hsv.2 (deletedIn_mono Fa F hsub c h)

/-- `hpreDead` from the branch-canonical fact: every recorded entry nearer than
`bw` was **deleted in the branch fold** (`Fa`), hence is a non-`F`-survivor. -/
theorem hpreDead_of_branchDeleted (Fa F : List (op_t α)) (hsub : ∀ o, o ∈ Fa → o ∈ F)
    (rcPre : List ℕ) (hdel : ∀ c ∈ rcPre, deletedIn Fa c) :
    ∀ c ∈ rcPre, ¬ survP F c :=
  fun c hc => notSurv_of_branchDeleted Fa F hsub c (hdel c hc)

/-! ## §2  `hout`: the off-forest birth-anchor survives `F` (clean, full-fold)

`bw = birthAnc l a b k` is `k`'s branch-final anchor.  When `bw` is *off the LCA
forest* (`contains l bw = false`) and nonzero, `betaf_start` forces `bw` to be a
survivor (a branch-new anchor lies in a branch's `difference` set), and the
full-fold `CanonMatch F fold` + `hD` (survivor set = fold live set) turn that into
`survP F bw`.  This uses only the two-sided fold's canonical state, NOT the
branch fold, so no single-vs-two-sided reconciliation is involved. -/

/-- The off-forest branch-final anchor of a survivor survives the two-sided set
`F`.  (`hbwne` is genuinely needed: `birthAnc l a b k = 0`, `k` anchored at the
root in its branch, is off-forest but not a survivor; that degenerate case is
handled by `canonAnc F rc = 0` directly, not by `hout`.) -/
theorem branchCanon_hout
    (l a b : concrete_st α) (F : List (op_t α)) (fold : concrete_st α) (k : ℕ)
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

/-! ## §3  The composed bridge: `hout` discharged, residual reduced to
`hsplit`/`hpreDead`/`hin`

`canonBirthBridge_via_branchCanon` feeds `canonBirthBridge_holds` with `hout`
built by §2.  The caller supplies only:
* `hsplit`, `bw` sits on the recorded chain (from the branch `LiveChain`: `bw`
  is the head of `k`'s live-filtered recorded chain in its branch fold);
* `hpreDead`, the nearer recorded entries are non-`F`-survivors (§1's
  `hpreDead_of_branchDeleted`, from branch-deletion + `Fa ⊆ F`);
* `hin`, the in-forest recorded-tail↔`l`-chain reconciliation (the located
  two-sided residual; see §4). -/

/-- **`CanonBirthBridge` from the branch-canonical residuals, `hout` discharged.**
For a survivor `k` with branch-final anchor `bw = birthAnc l a b k` and recorded
chain `rc`, the merge-side bridge holds given the recorded-chain split (`hsplit`),
the dead-prefix fact (`hpreDead`), and the in-forest reconciliation (`hin`).
`hout` is supplied internally from the full-fold `CanonMatch F fold` + `hD`. -/
theorem canonBirthBridge_via_branchCanon
    (l a b : concrete_st α) (F : List (op_t α)) (fold : concrete_st α) (k : ℕ)
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
that subsequence*, inserting or deleting non-survivors is invisible.  This lets us
pin `hin` (`canonAnc F cw = canonAnc F rcSuf`) to a single crisp fact: `bw`'s
`F`-surviving recorded ancestors equal its `F`-surviving `l`-ancestors, in order. -/

/-- Decidable survivorship test (classical). -/
noncomputable def survB (F : List (op_t α)) (c : ℕ) : Bool := decide (survP F c)

/-- `canonAnc F` depends on a chain only through its `F`-survivor subsequence. -/
theorem canonAnc_filter_surv (F : List (op_t α)) :
    ∀ L : List ℕ, canonAnc F L = canonAnc F (L.filter (survB F)) := by
  intro L
  induction L with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : survP F c
    · rw [canonAnc_pos F c cs h, List.filter_cons,
        show survB F c = true from by simp [survB, h],
        if_pos rfl, canonAnc_pos F c _ h]
    · rw [canonAnc_neg F c cs h, List.filter_cons,
        show survB F c = false from by simp [survB, h], if_neg (by simp), ih]

/-- **`hin` from the survivor-subsequence coincidence.**  If `bw`'s recorded
rootward tail `rcSuf` and its LCA-forest chain `cw` have the *same* `F`-surviving
subsequence, they reach the same `F`-survivor, and `hin` holds.  This is the
irreducible two-sided residual, stripped of all climb algebra: everything else in
`canonAnc F cw = canonAnc F rcSuf` is discharged; what remains is that `bw`'s
surviving ancestors are the same whether read off the recorded chain or the LCA
forest. -/
theorem hin_of_survFilterEq (l : concrete_st α) (F : List (op_t α)) (bw : ℕ)
    (cw rcSuf : List ℕ) (hpath : IsAncPath l bw cw)
    (hFiltEq : rcSuf.filter (survB F) = cw.filter (survB F)) :
    contains l bw = true →
      ∃ cw', IsAncPath l bw cw' ∧ canonAnc F cw' = canonAnc F rcSuf := by
  intro _
  refine ⟨cw, hpath, ?_⟩
  rw [canonAnc_filter_surv F cw, canonAnc_filter_surv F rcSuf, hFiltEq]

#print axioms hin_of_survFilterEq

/-! ## §4  Which merge-side residual closes, and the exact remaining content

**Both `#print axioms` are kernel-clean** (`[propext, Classical.choice,
Quot.sound]`).  The three `CanonBirthBridge` residuals split as follows.

* **`hout` (§2).**  The off-forest branch-final anchor of a survivor survives `F`
  straight from the *two-sided* fold's own canonical state (`hcm : CanonMatch F
  fold` + `hD` + `betaf_start`).  No branch fold, no single-vs-two-sided
  reconciliation.  (Caveat: needs `birthAnc ≠ 0`; the `bw = 0` root-anchored case
  is off-forest but non-surviving and is instead handled by `canonAnc F rc = 0`
  directly.)

* **`hpreDead` (§1).**  The nearer recorded entries are non-`F`-survivors
  *because they were deleted in the branch fold*: `notSurv_of_
  branchDeleted` turns `deletedIn Fa c` into `¬ survP F c` via `Fa ⊆ F` (the
  branch's own `Del` events are also in the two-sided `F`).  The input
  `deletedIn Fa c` for the prefix entries is a real branch-fold fact (they sit
  below `bw`, the head of `k`'s live-filtered recorded chain in its branch fold).

* **`hsplit`, branch `LiveChain` fact.**  `bw = birthAnc l a b k = anc(branch) k`
  is the head of `k`'s live-filtered recorded chain in its branch fold
  (`subchain_resolve` / `CanonInv`'s `LiveChain`), hence sits on `rc`.  A real
  execution fact; taken as input to the composed bridge.

* **`hin`, the irreducible two-sided residual (§3.5).**  Pinned to a single crisp
  fact: `rcSuf.filter (survB F) = cw.filter (survB F)`, `bw`'s `F`-surviving
  recorded ancestors equal its `F`-surviving `l`-ancestors, in order.  All climb
  algebra around it is discharged (`canonAnc_filter_surv` + `hin_of_survFilterEq`).

**The exact mismatch (single-sided vs two-sided).**  `canon_fold` on the *branch*
`a = applySeqR l Ea` gives `CanonMatch Fa a`, i.e. `anc a k = canonAnc Fa (rc)`,
`k`'s branch-final anchor is `canonAnc` over the **branch** survivor set `Fa`.  But
`CanonBirthBridge` is stated over `canonAnc F` with `F` the **two-sided** applied
set (`Fa ∪ Fb`).  The reconciliation `canonAnc Fa → canonAnc F` is not a corollary
of the branch's canonical state; it needs cross-branch structure that a single
branch fold does not carry:

  1. `Fa ⊆ F` (branch `Del`s ⊆ two-sided `Del`s): supplied here as an explicit
     set-inclusion premise; drives `hpreDead` (§1).
  2. an off-forest `bw = anc a k` (a branch-new node) is not deleted by the *other*
     branch: obtained via `betaf_start` (a-new ⇒ survivor) + `hD` + `hcm`, so
     `hout` needs no separate faithfulness premise.
  3. `bw`'s recorded rootward tail `rcSuf` (captured in *branch-`a`-at-insert*) and
     `bw`'s LCA-forest chain `cw` have the same `F`-surviving subsequence.  This is
     `hin`.  It is true: the entries of `cw` missing from `rcSuf` were deleted in
     `Ea` before `k`'s insert (hence `F`-dead), and `rcSuf` adds no non-`l` entries
     (insertion never splices into an existing ancestor chain); but establishing
     the subsequence coincidence is a *branch-fold event-list induction*
     (`foldChain_of_goodFold`, the `RGA_MergeBranchNew` OBSTRUCTION), threading a
     chain-level analogue of `BranchInv`'s I4 across `Ea ++ Eb`.  It is exactly the
     gap between resolving a node's recorded chain over the actual fold forest and
     climbing the distinct LCA forest: the OBSTRUCTION block names it as
     irreducible two-sided content, not expressible as, or derivable from, a
     single branch's `CanonMatch`.

**Summary.**  `canon_fold` on the branch discharges `hout` (via the full two-sided
`CanonMatch`, not the branch one), and reduces `hpreDead` to `Fa ⊆ F`
monotonicity; `hsplit` is the branch `LiveChain` head.  It does not discharge
`hin`: `birthAnc` is `canonAnc Fa` (single-sided) while the bridge is `canonAnc F`
(two-sided), and the recorded-tail↔`l`-chain survivor coincidence they must share
is `foldChain_of_goodFold`, a genuine single-vs-two-sided gap pinned (§3.5) to
the crisp subsequence equality `rcSuf.filter (survB F) = cw.filter (survB F)`,
sorry-free, with every surrounding step mechanized. -/

end RGABranchCanon
