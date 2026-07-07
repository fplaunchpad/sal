import Sal.ConditionedMRDTs.Development.RGA_UpdateConvergence_Final
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.ConditionedMRDTs.Framework.ConditionedExecutionModel
import Sal.ConditionedMRDTs.Refutations.G2_Applicability_Aware
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.Development.RGA_BubbleWiring
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.Development.RGA_GeneralSwap
import Sal.ConditionedMRDTs.Development.RGA_InterleavedThreading
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeLinearization
import Sal.ConditionedMRDTs.Development.RGA_SwapRoute_Residuals

/-!
# Discharging `hReach`: update convergence modulo the RGA generation discipline

*Additive; not committed; 0 `sorry` in what is kept.*

`RGA_UpdateConvergence_Final.RGA_update_convergence` proved update-layer
convergence CONDITIONAL on the bundled premise `hReach`, which supplies, at every
eligible delivery prefix `pre` and swapped concurrent pair `a b`, the seven
reachability/linkage conjuncts the abstract `ConditionedConfiguration` cannot
carry: `contains 0 = false`, `wf`, `id_mono`, `Faithful a`, `Faithful b`, and both
`NoFreshClash`.

This file replaces `hReach` by a single **generation-discipline** hypothesis
`RGAGenDiscipline`, and discharges from it the two `Faithful` conjuncts through the
already-proved ORDER layer (`faithful_at_interleaved_fold`), leaving the honest
irreducible core — the `recList ↔ vis` linkage a genuine RGA execution supplies but
`C` provably cannot (STATUS block of `RGA_UpdateConvergence_Final`).

See the closing STATUS block for the exact residual.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAReachDischarge

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful NoFreshClash)
open Sal.ConditionedMRDTs.RGABubbleWiring (recList)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (applySeqR)
open RGAInterleavedThreading (GoodFold faithful_at_interleaved_fold)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal (RGA_update_convergence)

/-! ## §1  The per-event fold-faithfulness source

An event's `Faithful`-at-fold obligation is sourced by op kind: an `Ins`'s is
reduced to the ORDER-layer `GoodFold` (discharged here via
`faithful_at_interleaved_fold`); a `Del`'s is kept as the LiveChain-route
`Faithful` fact the interleaved-threading file deferred. -/
def FoldFaithSource (o : op_t) (pre : List op_t) : Prop :=
  match o with
  | (_, _, .Ins _ _ _) => GoodFold (recList o) init_st pre
  | (_, _, .Del _ _)   => Faithful o (applySeqR init_st pre)

/-- `FoldFaithSource` yields `Faithful` at the fold: the `Ins` case through the
interleaved-threading order layer, the `Del` case directly. -/
theorem faithful_of_foldFaithSource (o : op_t) (pre : List op_t)
    (h0 : contains (applySeqR init_st pre) 0 = false)
    (h : FoldFaithSource o pre) : Faithful o (applySeqR init_st pre) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e p a =>
    simp only [FoldFaithSource] at h
    exact faithful_at_interleaved_fold t r e a p pre h h0
  | Del p x =>
    simpa only [FoldFaithSource] using h

/-! ## §2  The generation-discipline hypothesis -/

/-- **RGA generation discipline on the delivered set `E`.**  At every eligible
(loOnA-respecting, backward-saturated, `E`-drawn, `Nodup`) delivery prefix `pre`
and swapped concurrent pair `a b`: each of `a`, `b` has a fold-faithfulness source
(`GoodFold` for an `Ins`, the LiveChain `Faithful` for a `Del`); the reachable-state
invariant holds at the fold; and `NoFreshClash` holds both ways.  This is exactly
the `recList ↔ vis` linkage + `noopFeasible`-of-eligible-interleaving invariant a
genuine RGA execution supplies but the abstract `ConditionedConfiguration` cannot. -/
def RGAGenDiscipline (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) : Prop :=
  ∀ (pre : List op_t) (a b : op_t),
    (∀ x ∈ pre, x ∈ E) → pre.Nodup → respects pre (loOnA RGACondSig Cfg E) →
    a ∈ E → b ∈ E → a ∉ pre → b ∉ pre → a ≠ b →
    ¬ loOnA RGACondSig Cfg E a b → ¬ loOnA RGACondSig Cfg E b a →
    (∀ z ∈ E, z ≠ a → loOnA RGACondSig Cfg E z a → z ∈ pre) →
    (∀ z ∈ E, z ≠ b → loOnA RGACondSig Cfg E z b → z ∈ pre) →
    FoldFaithSource a pre ∧ FoldFaithSource b pre
    ∧ contains (applySeqR init_st pre) 0 = false ∧ wf (applySeqR init_st pre)
    ∧ id_mono (applySeqR init_st pre)
    ∧ NoFreshClash a b ∧ NoFreshClash b a

/-! ## §3  The unconditional headline (modulo the generation discipline) -/

/-- **Update-layer convergence, `hReach`-free.**  Two `loOnA`-respecting
enumerations of a backward-closed `E` fold from `init_st` to observationally-`eq`
states.  No swap/`EqSwap`/`hReady`/`hReach` premise survives; the only residual is
the irreducible generation discipline `RGAGenDiscipline`. -/
theorem RGA_update_convergence_unconditional
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnA RGACondSig Cfg E))
    (h₂r : respects π₂ (loOnA RGACondSig Cfg E))
    (hGen : RGAGenDiscipline Cfg E) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  refine RGA_update_convergence C Cfg E hE hids0 π₁ π₂ h₁p h₂p h₁r h₂r ?_
  intro pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  obtain ⟨hsa, hsb, h0, hwf, hmono, hcab, hcba⟩ :=
    hGen pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  exact ⟨h0, hwf, hmono,
    faithful_of_foldFaithSource a pre h0 hsa,
    faithful_of_foldFaithSource b pre h0 hsb, hcab, hcba⟩

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — what `RGAGenDiscipline` discharges, and the exact residual.

   DISCHARGED from `RGAGenDiscipline` via the proved ORDER layer:
   • `Faithful a`, `Faithful b` for an `Ins` — reduced to the per-step
     reachability classifier `GoodFold (recList ·) init_st pre` and threaded by
     `faithful_at_interleaved_fold` (`FoldFaithSource`, `faithful_of_foldFaithSource`).

   TARGET-DELETION SUB-CASE — VERDICT: **case (i)** (no new lemma, no gap).
   `target a` (the head of `recList a`) CAN be deleted by a concurrent `Del`
   before `a` in an eligible prefix.  The `Ins`-`Faithful` discharge does NOT go
   through `recPathFaithful_step`/`okStep` (whose `y ≠ x` spares only the head);
   it goes through `faithful_at_interleaved_fold` ⇒ `chainFaithful_goodFold` ⇒
   `chainFaithful_goodStep`, whose `Del` arm is `chainFaithful_doDel_faithful`
   (`RGA_StaledDel_Gate`).  That lemma imposes NO relation between the deleted
   `x` and `L = recList a`, so it tolerates deleting `recList a`'s HEAD.  Hence
   `ChainFaithful (recList a)` — and `Faithful a` — survive head-deletion, and
   `RecPathFaithful`'s spare-target restriction is off the critical path.

   RESIDUAL (irreducible generation discipline `RGAGenDiscipline`, the honest
   final form — the `recList ↔ vis` linkage `C` provably cannot supply):
   • `GoodFold (recList o) init_st pre` (the `AncInsLink` per-step linkage) — this
     is `FoldFaithSource` for an `Ins`; a `Del`'s `FoldFaithSource` keeps the
     LiveChain `Faithful` fact the threading file deferred.
   • `contains 0 = false ∧ wf ∧ id_mono` at the fold — the reachable-state
     invariant (needs `noopFeasible` of the eligible interleaving, absent from `C`).
   • `NoFreshClash a b` / `b a` — the causal-freshness id-bound (`recList a ⊆`
     causal past); un-derivable because `¬ loOnA a b` does NOT give `C.Concurrent`.

   VERDICT: `hReach` is eliminated as a premise; `Faithful a`/`Faithful b` are
   discharged for the `Ins` case; the only surviving hypothesis is the
   generation discipline that DEFINES a genuine reachable RGA execution.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## §4  Axiom audit -/

#print axioms faithful_of_foldFaithSource
#print axioms RGA_update_convergence_unconditional

end Sal.ConditionedMRDTs.RGAReachDischarge
