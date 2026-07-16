import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeLinearization
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence

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
set_option linter.unusedSectionVars false
namespace RGAMergeLinearizationTwoSided

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAConditionedConvergence

/-! ## §1  The two-sided per-id characterization -/

/-- Each survivor's birth element, read from whichever branch it lives in
(matching `merge`'s `elf`; the element analogue of `birthAnc`). -/
def birthEl (l a b : concrete_st α) (t : ℕ) : α :=
  if contains l t then el l t else if contains a t then el a t else el b t

/-- **Two-sided branch invariant.**  The exact extensional content of the
three-way merge, phrased as a predicate on the reference fold state `p`:

* **dom** — `p`'s domain is the OR-set survivor set `survivors l a b`;
* **el**  — each survivor keeps its `birthEl` (element from its owning branch);
* **anc** — each survivor's anchor is the merge-`climb` of its `birthAnc` up the
  LCA forest to the nearest two-sided survivor.

This is the two-sided generalization of `RGAMergeLinearization.BranchInv`: the
stop-set is `survivors l a b` (not `domain a`) and the climb start is `birthAnc`
(not `anc l k`), so it also constrains the branch-new survivors. -/
def BranchInv2 (l a b p : concrete_st α) : Prop :=
  (∀ k, survivors l a b k = contains p k)
  ∧ (∀ k, survivors l a b k = true → el p k = birthEl l a b k)
  ∧ (∀ k, survivors l a b k = true →
        anc p k = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k))

/-- **eq-extensionality (steps 1+2 packaging).**  `BranchInv2 l a b p` is exactly
`eq (merge l a b) p`.  Pure unfolding of `merge`'s definitional projections
(`contains_merge`/`el_merge`/`anc_merge`), mirroring `eq_merge_single`. -/
theorem eq_merge2_of_branchInv2 (l a b p : concrete_st α) (hbi : BranchInv2 l a b p) :
    eq (merge l a b) p := by
  obtain ⟨hdom, hel, hanc⟩ := hbi
  intro k
  refine ⟨?_, ?_⟩
  · rw [contains_merge]; exact hdom k
  · intro hk
    have hsv : survivors l a b k = true := by rw [contains_merge] at hk; exact hk
    have he : el (merge l a b) k = el p k := by
      have hm : el (merge l a b) k = birthEl l a b k := rfl
      rw [hm, hel k hsv]
    have ha : anc (merge l a b) k = anc p k := by
      have hm : anc (merge l a b) k
          = climb (fun y => anc l y) (survivors l a b) (birthAnc l a b k) := rfl
      rw [hm, hanc k hsv]
    have e1 : sel (merge l a b) k = (el (merge l a b) k, anc (merge l a b) k) := rfl
    have e2 : sel p k = (el p k, anc p k) := rfl
    rw [e1, e2, he, ha]

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
theorem resolve_climb_lchain (l s : concrete_st α)
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

/-- The exact stuck goal `resolve a pre = anc a x`, now DISCHARGED for a `Del`
whose path is `x`'s full `l`-chain: `resolve_climb_lchain` turns `resolve a pre`
into the LCA-climb, which `BranchInv`'s I4 identifies with `anc a x`.  No
`accurate a`-hypothesis. -/
theorem hres_of_lchain (l a : concrete_st α)
    (Hdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y)
    (Hstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true))
    (h0 : contains l 0 = false)
    (x : ℕ) (pre : List ℕ) (hpath : IsAncPath l x pre)
    (hbi : RGAMergeLinearization.BranchInv l a)
    (hxl : contains l x = true) (hxlive : contains a x = true) :
    resolve a pre = anc a x := by
  rw [resolve_climb_lchain l a Hdec Hstay h0 x pre hpath]
  exact hbi.2.1 x hxl hxlive

/-- **Cross-branch `Del`-preservation (GAP 2).**  Single-sided `BranchInv l` is
preserved under a `Del pre x` WITHOUT the `accurate a`-hypothesis: it is enough
that, when `x` is live, the (possibly stale) path resolves to `x`'s CURRENT anchor
(`hres`) — supplied by `hres_of_lchain` for an `l`-accurate path — and that `a` is
well-formed with `x ≠ 0`.  The live branch is the `branchInv_doDel` argument with
`hres` in place of the accuracy-derived reparent equality; the dead branch is a
forest no-op (no live node anchors at an absent `x`, by `wf a`). -/
theorem branchInv_doDel_crossBranch (l a : concrete_st α) (t r x : ℕ) (pre : List ℕ)
    (ha0 : contains a 0 = false) (hwfa : wf a)
    (hlwf : wf l) (hlmono : id_mono l) (hamono : id_mono a) (hx0 : x ≠ 0)
    (hres : contains a x = true → resolve a pre = anc a x)
    (hbi : RGAMergeLinearization.BranchInv l a) :
    RGAMergeLinearization.BranchInv l (do_ a (t, r, .Del pre x)) := by
  obtain ⟨hI2, hI4, hI3⟩ := hbi
  have hHdec : ∀ y, contains l y = true → y ≠ 0 → anc l y < y := by
    intro y hy hy0; rcases hlmono y hy with h | h
    · omega
    · exact h
  have hHstay : ∀ y, contains l y = true → (anc l y = 0 ∨ contains l (anc l y) = true) := hlwf
  have hdomdel : domain (do_ a (t, r, .Del pre x)) = (fun z => domain a z && x != z) :=
    RGAMergeLinearization.domain_doDel a t r x pre
  by_cases hxlive : contains a x = true
  · have hresx : resolve a pre = anc a x := hres hxlive
    refine ⟨?_, ?_, ?_⟩
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [el_doDel a t r x pre k]; exact hI2 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [anc_doDel a t r x pre k, hresx, hdomdel]
      by_cases hax : anc a k = x
      · rw [if_pos hax]
        have hxl : contains l x = true := by
          rcases hI3 k hlk hak with h | h
          · rw [hax] at h; exact absurd h hx0
          · rw [hax] at h; exact h
        have hstepk :
            climb (fun y => anc l y) (fun z => domain a z && x != z) (anc l k)
              = climb (fun y => anc l y) (fun z => domain a z && x != z) (anc l x) := by
          apply RGAMergeLinearization.climb_remove_eq_result l hHdec hHstay (domain a) x hxl hx0
            (anc l k) (hlwf k hlk)
          rw [hI4 k hlk hak]; exact hax
        rw [hstepk]
        have hancax : anc a x ≠ x := by
          rcases hamono x hxlive with h | h
          · rw [h]; exact fun e => hx0 e.symm
          · omega
        have hne : climb (fun y => anc l y) (domain a) (anc l x) ≠ x := by
          rw [hI4 x hxl hxlive]; exact hancax
        rw [RGAMergeLinearization.climb_remove_ne (fun y => anc l y) (domain a) x (anc l x) hne]
        exact hI4 x hxl hxlive
      · rw [if_neg hax]
        have hne : climb (fun y => anc l y) (domain a) (anc l k) ≠ x := by
          rw [hI4 k hlk hak]; exact hax
        rw [RGAMergeLinearization.climb_remove_ne (fun y => anc l y) (domain a) x (anc l k) hne]
        exact hI4 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [anc_doDel a t r x pre k, hresx]
      by_cases hax : anc a k = x
      · rw [if_pos hax]
        have hxl : contains l x = true := by
          rcases hI3 k hlk hak with h | h
          · rw [hax] at h; exact absurd h hx0
          · rw [hax] at h; exact h
        exact hI3 x hxl hxlive
      · rw [if_neg hax]; exact hI3 k hlk hak
  · have hxdom : domain a x = false := by
      cases h : domain a x with
      | false => rfl
      | true => exact absurd (by rw [RGAMergeLinearization.contains_eq_domain]; exact h) hxlive
    have hdomeq : domain (do_ a (t, r, .Del pre x)) = domain a := by
      rw [hdomdel]; funext z
      show (domain a z && (x != z)) = domain a z
      by_cases hzx : z = x
      · subst hzx; simp only [bne_self_eq_false, Bool.and_false, hxdom]
      · have hb : (x != z) = true := by simp [Ne.symm hzx]
        rw [hb, Bool.and_true]
    have hanceq : ∀ k, contains a k = true → anc (do_ a (t, r, .Del pre x)) k = anc a k := by
      intro k hk
      rw [anc_doDel a t r x pre k]
      by_cases hax : anc a k = x
      · exfalso
        rcases hwfa k hk with h | h
        · rw [hax] at h; exact hx0 h
        · rw [hax] at h; exact absurd h hxlive
      · rw [if_neg hax]
    refine ⟨?_, ?_, ?_⟩
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [el_doDel a t r x pre k]; exact hI2 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [hanceq k hak, hdomeq]; exact hI4 k hlk hak
    · intro k hlk hak'
      have hak : contains a k = true := by
        rw [contains_doDel a t r x pre k, Bool.and_eq_true] at hak'; exact hak'.1
      rw [hanceq k hak]; exact hI3 k hlk hak

/-! ## §2  Interleave-order independence (steps 3+4)

The convergence engine `eq_convergence` is start-state-generic, so it applies with
start state `l` directly: any two `lo`-respecting enumerations of the same event
set fold from `l` to `eq` states, given the swap oracle.  Composing with §1 lifts
the bridge from one reference interleave to any `lo`-respecting interleave. -/

/-- **Interleave independence (steps 3+4).**  Given the bridge for ONE reference
interleave `π₀` (`href`), any other `lo`-respecting interleave `π` of the same
event set `ev` also satisfies the bridge — by the imported convergence engine
(fold-order independence up to `eq`) plus `eq`-transitivity.  `hSwap` is the swap
oracle the convergence headline already consumes (the located obstruction of
`RGA_ConditionedConvergence.lean`); it transports unchanged. -/
theorem merge_fold_indep
    (l a b : concrete_st α) (lo : op_t α → op_t α → Prop) (ev : Set (op_t α)) (π₀ π : List (op_t α))
    (href : eq (merge l a b) (applySeqR l π₀))
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ lo) (hπr : respects π lo)
    (hSwap : ∀ (pre : List (op_t α)) (x y : op_t α),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup → respects pre lo →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y → ¬ lo x y → ¬ lo y x →
        (∀ z ∈ ev, z ≠ x → lo z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → lo z y → z ∈ pre) →
        EqSwap x y (applySeqR l pre)) :
    eq (merge l a b) (applySeqR l π) := by
  have hconv : eq (applySeqR l π₀) (applySeqR l π) :=
    eq_convergence lo π₀.length l ev π₀ π rfl h₀p hπp h₀r hπr hSwap
  exact eq_trans _ _ _ href hconv

/-! ## §3  The assembled two-sided headline (conditioned)

Composes §1 (extensionality) and §2 (interleave independence).  It is conditioned
on exactly two hypotheses: `hThread` — the reference fold `applySeqR l π₀` satisfies
`BranchInv2` (the residual two-sided threading obligation, see OBSTRUCTION below) —
and `hSwap` — the convergence swap oracle (imported obligation).  Everything ELSE
in the two-sided bridge is discharged. -/
theorem eq_merge_two_sided
    (l a b : concrete_st α) (lo : op_t α → op_t α → Prop) (ev : Set (op_t α)) (π₀ π : List (op_t α))
    (hThread : BranchInv2 l a b (applySeqR l π₀))
    (h₀p : listPermOf π₀ ev) (hπp : listPermOf π ev)
    (h₀r : respects π₀ lo) (hπr : respects π lo)
    (hSwap : ∀ (pre : List (op_t α)) (x y : op_t α),
        (∀ z ∈ pre, z ∈ ev) → pre.Nodup → respects pre lo →
        x ∈ ev → y ∈ ev → x ∉ pre → y ∉ pre → x ≠ y → ¬ lo x y → ¬ lo y x →
        (∀ z ∈ ev, z ≠ x → lo z x → z ∈ pre) →
        (∀ z ∈ ev, z ≠ y → lo z y → z ∈ pre) →
        EqSwap x y (applySeqR l pre)) :
    eq (merge l a b) (applySeqR l π) := by
  have href : eq (merge l a b) (applySeqR l π₀) :=
    eq_merge2_of_branchInv2 l a b _ hThread
  exact merge_fold_indep l a b lo ev π₀ π href h₀p hπp h₀r hπr hSwap

/-! ## §4  Axiom audit -/

#print axioms eq_merge2_of_branchInv2
#print axioms resolve_climb_lchain
#print axioms hres_of_lchain
#print axioms branchInv_doDel_crossBranch
#print axioms merge_fold_indep
#print axioms eq_merge_two_sided

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
            (l a : concrete_st α) (t r x : ℕ) (pre : List ℕ) …
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
