import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_GenDischarge
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_InterleavedThreading
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.ConditionedMRDTs.Framework.ConditionedExecutionModel
import Sal.ConditionedMRDTs.Refutations.G2_Applicability_Aware
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_BubbleWiring
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_GeneralSwap
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeLinearization
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_RecPathFaithful
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_StaledDel_Gate
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_UpdateConvergence_Final

/-!
# CORRECTED per-event generation discipline: `accurate` at the DEPENDENCY prefix only

*Additive; modifies no existing file; 0 `sorry`.*

## Why `RGA_GenDischarge.GenDisc` is VACUOUS (the bug this file fixes)

`GenDisc` (that file, §4) asserts, per event `o`, that `accurate o (applySeqR init_st
pre)` holds at **every** eligible prefix `pre` — i.e. every `loOnA`-respecting,
backward-saturated (`∀ z, loOnA z o → z ∈ pre`), `o ∉ pre` enumeration.  That premise
is UNSATISFIABLE on the RGA's characteristic case.  `accurate o s` requires
`target o` LIVE in `s`.  A concurrent `Del` of `target o` is `loOnA`-INCOMPARABLE
with `o` (neither below nor above), hence it is NOT a dependency of `o` — yet an
eligible prefix is free to CONTAIN it (eligibility only forces `o`'s dependencies in,
never forbids a concurrent op).  At such a prefix `target o` is dead, so `accurate o`
FAILS.  Requiring it there makes `GenDisc` false exactly on insert-under-concurrently-
deleted-node — the case RGA convergence is about.  So `RGA_update_convergence_genDisc`
is conditional on a premise no real execution satisfies: vacuous.

## The fix: pin `accurate` at the MINIMAL dependency prefix

`GenDisc2` (§1) asserts `accurate o` at the SINGLE dependency prefix `d` = a
`loOnA`-respecting enumeration of exactly `{z ∈ E : z ≠ o ∧ loOnA z o}` (`IsDepPre`).
A concurrent `Del` of `target o` is `loOnA`-incomparable, hence NOT in `d`, so
`target o` is LIVE at `applySeqR init_st d` and `accurate o` there is SATISFIABLE by a
real execution (which folds `o`'s causal past, keeping `target o` live).  This is a
single-prefix assertion, NOT a ∀-over-eligible-prefixes one.

From this base (§2–§4) we thread `ChainFaithful (recList o)` FORWARD through a
concurrent tail — including a `Del` of `target o` (= the head of `recList o`) — via
`chainFaithful_doDel_faithful`, which relates the deleted node to NOTHING in
`recList o`.  That is the target-deletion TOLERANCE the `accurate`-everywhere approach
destroyed by demanding accuracy after the deletion.

## The honest residual (§5)

The forward thread closes when the eligible delivery presents `o`'s dependencies as a
sub-fold `d` followed by a concurrent `GoodFold` tail.  Reducing an ARBITRARY eligible
prefix (deps and concurrents interleaved) to that shape is the genuine hard core; it is
NOT derivable from `GenDisc2 + ReachInv` and is the located stuck point.  See §5.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAGenDischarge2

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful ClimbFaithful NoFreshClash)
open Sal.ConditionedMRDTs.RGABubbleWiring (recList ChainFaithful chainFaithful_doIns climbFaithful_of_chain)
open Sal.ConditionedMRDTs.RGAConditionedConvergence
  (applySeqR applySeqR_append applySeqR_cons applySeqR_nil chainFaithful_of_accurate)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open RGAInterleavedThreading (GoodStep GoodFold chainFaithful_goodStep chainFaithful_goodFold)
open Sal.ConditionedMRDTs.RGAStaledDelGate (chainFaithful_doDel_faithful)
open RGARecPathFaithful (target recPath recList_eq_target_recPath)
open Sal.ConditionedMRDTs.RGAGenDischarge (NonDegen ReachInv)
open Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal (RGA_update_convergence)

/-! ## §1  `IsDepPre` and the corrected per-event discipline `GenDisc2` -/

/-- **`IsDepPre Cfg E o d`** — `d` is a `loOnA`-respecting `Nodup` enumeration of
EXACTLY `o`'s strict `loOnA`-predecessors in `E` (its dependency prefix).  Members are
drawn from `E`, are strictly `loOnA`-below `o`, and every strict predecessor appears.
A concurrent (`loOnA`-incomparable) op is, by the last conjunct's contrapositive, NOT
in `d`. -/
def IsDepPre (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (o : op_t) (d : List op_t) : Prop :=
  (∀ x ∈ d, x ∈ E) ∧ d.Nodup ∧ respects d (loOnA RGACondSig Cfg E) ∧
  (∀ z ∈ E, z ≠ o → loOnA RGACondSig Cfg E z o → z ∈ d) ∧
  (∀ x ∈ d, loOnA RGACondSig Cfg E x o)

/-- **`GenDisc2` — SATISFIABLE per-event discipline.**  For each `o ∈ E`: `NonDegen o`,
and `o`'s recorded path is `o`'s TRUE live chain (`accurate o`) at its DEPENDENCY
prefix `applySeqR init_st d` — the SINGLE minimal prefix, NOT every eligible one.

SATISFIABILITY (why a real execution meets this, unlike the ∀-prefix `GenDisc`):
`d` contains exactly `o`'s `loOnA`-strict-predecessors.  The only op that can kill
`target o` is a `Del` whose deleted node is `target o`; such a `Del` runs
CONCURRENTLY with `o` (it is `loOnA`-incomparable — it neither causes nor is caused by
`o`), so it is NOT a strict predecessor and NOT in `d`.  Hence `target o` is LIVE at
`applySeqR init_st d`, and `o`'s recorded path (fixed at `o`'s generation, over its
causal past) is the genuine chain there: `accurate o` holds.  The prior `GenDisc`
demanded accuracy AFTER such a concurrent `Del` could be appended — impossible; here we
never fold it into `d`. -/
def GenDisc2 (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) : Prop :=
  ∀ o ∈ E, NonDegen o ∧
    ∀ d : List op_t, IsDepPre Cfg E o d → accurate o (applySeqR init_st d)

/-! ## §2  The generation base: dependency-prefix accuracy ⇒ `ChainFaithful` there

`accurate o` at the dependency-prefix state gives `ChainFaithful (recList o)` there,
via the imported generation base `chainFaithful_of_accurate`.  This is the ONLY place
`GenDisc2`'s single-prefix accuracy is consumed; everything downstream threads this
`ChainFaithful` forward WITHOUT re-invoking accuracy. -/
theorem chainFaithful_at_depPre (o : op_t) (d : List op_t)
    (hmono : id_mono (applySeqR init_st d)) (h0 : contains (applySeqR init_st d) 0 = false)
    (hacc : accurate o (applySeqR init_st d)) :
    ChainFaithful (applySeqR init_st d) (recList o) :=
  chainFaithful_of_accurate (applySeqR init_st d) o hmono h0 hacc

/-! ## §3  Forward threading through a concurrent tail — target-deletion TOLERANT

Thread the §2 base `ChainFaithful (recList o)` forward along a concurrent tail `conc`
(each step a `GoodStep` for `recList o`) via the imported `chainFaithful_goodFold`.
The tail's steps are the ops `loOnA`-incomparable with `o`; NONE is an ancestor of `o`
(ancestors are dependencies, already folded into `d`), so no `AncInsLink` step arises
past `d` — the tail is only concurrent-fresh `Ins` (`GoodStep`'s `t ∉ recList o` arm)
and `Del` (`GoodStep`'s `Faithful`-`Del` arm).  Crucially the `Del` arm is
`chainFaithful_doDel_faithful`, which imposes NO relation between the deleted node and
`recList o`; hence it survives deleting `recList o`'s HEAD = `target o`. -/

/-- **Target-deletion tolerance, machine-checked.**  A `Del` whose deleted node is
EXACTLY `target o` (the head of `recList o`) is a `GoodStep` for `recList o` the moment
it is `Faithful`: `GoodStep`'s `Del` arm is `contains 0 = false ∧ wf ∧ Faithful`, with
the deleted node constrained against NOTHING in `recList o`.  This is the tolerance the
`accurate`-everywhere approach could not express (it demanded accuracy AFTER the
deletion, which fails). -/
theorem goodStep_del_target (o : op_t) (t r : ℕ) (pre : List ℕ) (s : concrete_st)
    (h0 : contains s 0 = false) (hwf : wf s)
    (hfaith : Faithful (t, r, .Del pre (target o)) s) :
    GoodStep s (recList o) (t, r, .Del pre (target o)) :=
  ⟨h0, hwf, hfaith⟩

/-- **§3 core — `ChainFaithful (recList o)` at the dep-prefix + concurrent tail fold.**
From dependency-prefix accuracy (§2 base) threaded forward along the concurrent
`GoodFold` tail `conc`.  Includes tails that `Del` `target o`: the head of `recList o`
may be deleted mid-tail and `ChainFaithful` survives. -/
theorem chainFaithful_depPre_concTail (o : op_t) (d conc : List op_t)
    (hmono : id_mono (applySeqR init_st d)) (h0 : contains (applySeqR init_st d) 0 = false)
    (hacc : accurate o (applySeqR init_st d))
    (hgf : GoodFold (recList o) (applySeqR init_st d) conc) :
    ChainFaithful (applySeqR init_st (d ++ conc)) (recList o) := by
  rw [applySeqR_append]
  exact chainFaithful_goodFold (recList o) conc (applySeqR init_st d) hgf
    (chainFaithful_at_depPre o d hmono h0 hacc)

/-! ## §4  Projection to `Faithful` (Ins form — the insert-under-deleted-node case) -/

/-- **`Faithful` of an enabled `Ins` at the dep-prefix + concurrent tail fold.**
The `Ins` `o` whose anchor/path may have been concurrently deleted in `conc` is
`Faithful` there: project the threaded `ChainFaithful (recList o) = ChainFaithful
(a :: p)` through `climbFaithful_of_chain`.  This is the headline case — an insert
whose recorded anchor chain was concurrently deleted stays `Faithful`. -/
theorem faithful_ins_depPre_concTail (t r e a : ℕ) (p : List ℕ) (d conc : List op_t)
    (hmono : id_mono (applySeqR init_st d)) (h0 : contains (applySeqR init_st d) 0 = false)
    (hacc : accurate (t, r, .Ins e p a) (applySeqR init_st d))
    (hgf : GoodFold (recList (t, r, .Ins e p a)) (applySeqR init_st d) conc)
    (h0' : contains (applySeqR init_st (d ++ conc)) 0 = false) :
    Faithful (t, r, .Ins e p a) (applySeqR init_st (d ++ conc)) := by
  have hcf : ChainFaithful (applySeqR init_st (d ++ conc)) (a :: p) :=
    chainFaithful_depPre_concTail (t, r, .Ins e p a) d conc hmono h0 hacc hgf
  exact climbFaithful_of_chain (applySeqR init_st (d ++ conc)) (a :: p) h0' hcf

/-! ## §5  Composing to update convergence — and the HONEST residual `EligibleThread`

To feed `RGA_update_convergence` we need `Faithful a`, `Faithful b` at each eligible
prefix `pre`.  §4 delivers that from dependency-prefix accuracy ONLY when `pre` is
realized as `d ++ conc` (`d` a dependency sub-fold, `conc` a concurrent `GoodFold`).
`FaithSrc2` packages exactly this per-event source; `faithful_of_faithSrc2` consumes
`GenDisc2`'s accuracy (LOAD-BEARING for the `Ins` base) to produce `Faithful`.  The
per-prefix bundle of these sources + `NoFreshClash` is the named residual
`EligibleThread` — the honest structural gap (see the STATUS block). -/

/-- Per-event fold-faithfulness source under the corrected discipline.  `Ins`: `pre`'s
state factors through a dependency sub-fold `d` (`GenDisc2` gives `accurate` at `d`)
followed by a concurrent `GoodFold` tail.  `Del`: the LiveChain `Faithful` fact
directly (as `RGA_ReachDischarge.FoldFaithSource` does — off the target-Del path). -/
def FaithSrc2 (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (o : op_t) (pre : List op_t) : Prop :=
  match o with
  | (_, _, .Ins _ _ _) =>
      ∃ d conc : List op_t, IsDepPre Cfg E o d ∧
        applySeqR init_st pre = applySeqR init_st (d ++ conc) ∧
        GoodFold (recList o) (applySeqR init_st d) conc
  | (_, _, .Del _ _) => Faithful o (applySeqR init_st pre)

/-- `FaithSrc2` yields `Faithful` at the fold.  The `Ins` case is where `GenDisc2`'s
single-dependency-prefix accuracy is CONSUMED: it supplies the §2 base at `d`, which
§4 threads through `conc` (target-Del-tolerant) to `Faithful` at `pre`.  `ReachInv`
supplies `id_mono`/`contains 0 = false` at `d` (eligibility of `d` from `IsDepPre`). -/
theorem faithful_of_faithSrc2 (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (o : op_t) (pre : List op_t)
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E) (ho : o ∈ E)
    (h0pre : contains (applySeqR init_st pre) 0 = false)
    (h : FaithSrc2 Cfg E o pre) : Faithful o (applySeqR init_st pre) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p a =>
    simp only [FaithSrc2] at h
    obtain ⟨d, conc, hdep, hsteq, hgf⟩ := h
    obtain ⟨_, haccf⟩ := hGen (t, r, .Ins e p a) ho
    have hacc := haccf d hdep
    obtain ⟨hsub, hnd, hresp, _, _⟩ := hdep
    obtain ⟨h0d, _hwfd, hmonod⟩ := hInv d hsub hnd hresp
    have h0' : contains (applySeqR init_st (d ++ conc)) 0 = false := by rw [← hsteq]; exact h0pre
    have hf := faithful_ins_depPre_concTail t r e a p d conc hmonod h0d hacc hgf h0'
    rw [hsteq]; exact hf
  | Del p x =>
    simpa only [FaithSrc2] using h

/-- **`EligibleThread` — the honest per-prefix residual.**  At every eligible prefix
and swapped pair: a `FaithSrc2` source for each event and both `NoFreshClash`.  This is
`RGA_ReachDischarge.RGAGenDiscipline` with its `Ins`-`FoldFaithSource` replaced by the
`accurate`-base factorization `FaithSrc2` — i.e. the interleaving-to-deps-first
reduction, the concurrent-`Del` faithfulness, and the causal-freshness `NoFreshClash`
that `GenDisc2 + ReachInv` do NOT supply.  See the STATUS block for why. -/
def EligibleThread (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) : Prop :=
  ∀ (pre : List op_t) (a b : op_t),
    (∀ x ∈ pre, x ∈ E) → pre.Nodup → respects pre (loOnA RGACondSig Cfg E) →
    a ∈ E → b ∈ E → a ∉ pre → b ∉ pre → a ≠ b →
    ¬ loOnA RGACondSig Cfg E a b → ¬ loOnA RGACondSig Cfg E b a →
    (∀ z ∈ E, z ≠ a → loOnA RGACondSig Cfg E z a → z ∈ pre) →
    (∀ z ∈ E, z ≠ b → loOnA RGACondSig Cfg E z b → z ∈ pre) →
    FaithSrc2 Cfg E a pre ∧ FaithSrc2 Cfg E b pre
    ∧ NoFreshClash a b ∧ NoFreshClash b a

/-- **Update convergence under the corrected discipline.**  Conditional on `GenDisc2`
(the SATISFIABLE per-event dependency-prefix accuracy) + `ReachInv` (reachable-state
residual) + `EligibleThread` (the per-prefix structural residual) + the enumeration
hypotheses.  `GenDisc2` is load-bearing: it is the `accurate` base
`faithful_of_faithSrc2` threads for every `Ins`.  It does NOT close on
`GenDisc2 + ReachInv` alone — `EligibleThread` is the located gap. -/
theorem RGA_update_convergence_genDisc2
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnA RGACondSig Cfg E))
    (h₂r : respects π₂ (loOnA RGACondSig Cfg E))
    (hGen : GenDisc2 Cfg E) (hInv : ReachInv Cfg E) (hThr : EligibleThread Cfg E) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  refine RGA_update_convergence C Cfg E hE hids0 π₁ π₂ h₁p h₂p h₁r h₂r ?_
  intro pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  obtain ⟨h0, hwf, hmono⟩ := hInv pre hsub hnd hresp
  obtain ⟨hsa, hsb, hcab, hcba⟩ :=
    hThr pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  exact ⟨h0, hwf, hmono,
    faithful_of_faithSrc2 Cfg E a pre hGen hInv ha h0 hsa,
    faithful_of_faithSrc2 Cfg E b pre hGen hInv hb h0 hsb, hcab, hcba⟩

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — the EXACT stuck goal (honest accounting).

   WHAT CLOSED (0 sorry, kernel axioms only):
   • §1 `GenDisc2` — accurate at the SINGLE dependency prefix `d` (`IsDepPre`), NOT at
     every eligible prefix.  Satisfiable: a concurrent `Del` of `target o` is
     `loOnA`-incomparable, hence ∉ `d`, so `target o` is live at `applySeqR init_st d`.
   • §2 base, §3 forward thread through a concurrent `GoodFold` tail, §4 `Faithful`
     (Ins).  The tail may `Del` `target o` (= head of `recList o`): the `GoodStep`
     `Del` arm is `chainFaithful_doDel_faithful`, which relates the deleted node to
     NOTHING in `recList o` (`goodStep_del_target` machine-checks this).  Target-Del
     TOLERANCE holds — the property the `accurate`-everywhere `GenDisc` destroyed.
   • §5 `RGA_update_convergence_genDisc2` composes, with `GenDisc2` load-bearing (the
     `Ins` accuracy base in `faithful_of_faithSrc2`).

   THE STUCK GOAL (why `GenDisc2 + ReachInv` do NOT suffice; isolated as
   `EligibleThread`):  discharging `hReach` needs `Faithful a (applySeqR init_st pre)`
   at an ARBITRARY eligible `pre`.  §4 anchors the accuracy base at `applySeqR init_st
   d`; that state is a genuine SUB-FOLD of `pre` ONLY when `pre` folds `o`'s
   dependencies first (`pre = d ++ conc`).  An arbitrary `loOnA`-respecting eligible
   `pre` may INTERLEAVE dependencies with concurrents, so there is no `applySeqR
   init_st d` sub-state to seat the base:

       exact stuck goal (Ins branch of `faithful_of_faithSrc2` without `EligibleThread`):
         ⊢ ∃ d conc, IsDepPre Cfg E (t,r,.Ins e p a) d
                     ∧ applySeqR init_st pre = applySeqR init_st (d ++ conc)
                     ∧ GoodFold (recList (t,r,.Ins e p a)) (applySeqR init_st d) conc

   Neither conjunct follows from `GenDisc2 + ReachInv`:
     (1) the state-equality `applySeqR init_st pre = applySeqR init_st (d ++ conc)` is a
         local reorder-to-deps-first fact — a fragment of convergence itself;
     (2) `GoodFold (recList o) (applySeqR init_st d) conc` requires every concurrent
         `Del` in the tail to be `Faithful` at its sub-fold — a fact about OTHER events,
         not derivable from `o`'s own `accurate`; and
     (3) `NoFreshClash a b` needed `accurate a` and `fresh b` at a COMMON prefix (how
         `RGA_GenDischarge` derived it); under the correction `accurate a` lives only at
         `d_a`, where `b`'s freshness is not available.

   CONCLUSION: `GenDisc2` correctly and satisfiably supplies the `ChainFaithful` BASE
   (the fix), and it is load-bearing.  But single-prefix accuracy is load-bearing only
   relative to a deps-first realization of the delivery; the reduction of an arbitrary
   interleaving to that realization, the concurrent-`Del` faithfulness, and the
   causal-freshness bound are the irreducible residual `EligibleThread` — precisely the
   per-step `recList ↔ vis` linkage `RGA_ReachDischarge`'s STATUS block already isolates,
   now with the accuracy base factored out and satisfiable.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## §6  Axiom audit -/

#print axioms chainFaithful_at_depPre
#print axioms chainFaithful_depPre_concTail
#print axioms faithful_ins_depPre_concTail
#print axioms faithful_of_faithSrc2
#print axioms RGA_update_convergence_genDisc2

end Sal.ConditionedMRDTs.RGAGenDischarge2
