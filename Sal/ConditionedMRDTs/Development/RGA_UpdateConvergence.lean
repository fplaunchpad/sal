import Sal.ConditionedMRDTs.Development.RGA_EnablementBase
import Sal.ConditionedMRDTs.Framework.ConditionedExecutionModel
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeLinearization
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate

/-!
# Stage-1 capstone attempt: composing M1 + M2 into RGA update-layer convergence

*Roadmap `ROADMAP_END_TO_END.md`, stage-1 capstone.  Additive; modifies no
existing file; introduces no `sorry`.*

The target is the UNCONDITIONAL update-layer convergence theorem

    RGA_update_convergence :
      any two `loOnA`-respecting `noopFeasible` enumerations of a backward-closed
      reachable event set `E` fold from `init_st` to `eq`-equivalent states,

obtained by discharging the residual `hReady` hypothesis of the RGA convergence
engine `RGAConditionedConvergence.RGA_conditioned_convergence_bothFaithful` using
M1 (`RGAEnablementBase.faithful_at_enablement_ins`, the Faithful conjuncts) and
M2 (`ConditionedExecutionModel.ConditionedConfiguration.conditioned_premises`, the
rest), with the RGA instantiated as `RGASig.RGACondSig`
(`Inv := RgaInv`, `applicable := accurate ∧ fresh_ts`, `update := do_`).

## What composes cleanly (mechanized below, 0-sorry, kernel-clean)

* **§0** the fold bridge `applySeqR init_st = applySeq RGACondSig.toCRDTSig init_st`
  (`rfl`: `RGACondSig.update = do_`, `RGACondSig.init = init_st`), so the engine's
  fold and M2's fold are literally the same function.
* **§1** the RGA discharge of M2's configuration discipline fields:
  `rgaCond_inv_init : RgaInv init_st` and
  `rgaCond_inv_step : RgaInv s → RGACondSig.applicable o s → RgaInv (do_ s o)`
  (from `Inv_init` / `Inv_doIns` / `Inv_doDel`).  So an RGA `ConditionedConfiguration`
  is always inhabitable in its `inv_init` / `inv_step` fields.
* **§2** the CLEAN slice of the M2 → RGA `hReady` bridge:
  `hReady_clean_conjuncts` turns `C.conditioned_premises` into the THREE `hReady`
  conjuncts that are `RgaInv`/timestamp-level facts —
  `a.1 ≠ b.1`, `contains (fold pre) 0 = false`, `wf (fold pre)` — for a
  `vis`-concurrent pair pending at a `noopFeasible` `E`-drawn prefix.

## Why the capstone does NOT close (the located interface-gap cluster)

The composition M1 ∘ M2 → engine is blocked; the headline `RGA_update_convergence`
is left as a commented goal (§3).  There is not one obstruction but a cluster, all
precisely located; the first is FATAL and type-level.

**GAP 1 — the engine's oracle over-quantifies `pre` (FATAL, type-level).**
`RGA_conditioned_convergence_bothFaithful`'s `hReady` is
`∀ (pre : List op_t) (a b : op_t), a ∈ ev → b ∈ ev → a ≠ b → ¬lo a b → ¬lo b a → …`
— `pre` ranges over ALL lists, unconstrained.  Several conjuncts are *provably
false* at a bad `pre`, so no total `hReady` function exists:

* `contains (applySeqR init_st pre) 0 = false` fails at `pre = [(0, r, .Ins e p a)]`
  (an `Ins` with id `0` makes the root sentinel live);
* `Faithful a (applySeqR init_st pre)` fails at prefixes where `a`'s causal past is
  not yet folded — this is exactly the PBT's `t1StrongFails ≠ 0` and the
  `RGA_FaithfulThreading_Gate` "KEY REFINEMENT": the *all-events-at-all-prefixes*
  Faithful invariant is genuinely FALSE; it holds only at ENABLEMENT folds.

M1 (`faithful_at_enablement_ins`) and M2 (`conditioned_premises`, which itself needs
`hpre_sub : pre ⊆ E`, `hpre_feas : noopFeasible … pre`, `a ∉ pre`, `b ∉ pre`) supply
their facts ONLY at enabled, `loOnA`-respecting, `E`-drawn, feasible prefixes — never
at an arbitrary `pre`.  The engine (`eq_convergence`) internally only ever *invokes*
the oracle at such prefixes (`peeled-π₁-heads ++ σ-prefix`, both `loOnA`-respecting),
but its *type* demands all prefixes.  **Resolution owned by the coordinator:** restate
`eq_convergence` / `RGA_conditioned_convergence_bothFaithful` with the oracle
restricted to the enabled `loOnA`-respecting prefixes it actually visits (an
interleaving-feasibility-indexed oracle), OR re-derive a restricted engine.  Neither
is possible additively against the frozen engine, and the fix is not a bridging lemma.

**GAP 2 — M1's enablement shape vs. the engine's interleaved prefix.**
`faithful_at_enablement_ins` requires the prefix presented as `foldDo s_c concurrent`
with `HistFaithful s_c w` (`w` accurate at `s_c`) and the tail an `IncompFold (recList w)`.
The engine's swap prefix `applySeqR init_st (peeled ++ α)` is a `loOnA`-respecting
INTERLEAVING in which `w`'s causal past is present (backward-closure) but NOT
contiguous / first, so it does not literally match `foldDo s_c concurrent`.  Bridging
needs either an M1 variant accepting an interleaved prefix (causal past a
sub-multiset, all other steps `IncompStep`s) or a causal-past-to-front reordering,
which is itself a swap/convergence argument.

**GAP 3 — M2's generic id-forms vs. the RGA's state predicates.**
`conditioned_premises` emits timestamp-level forms; three `hReady` conjuncts are RGA
state predicates M2 does not reach:
* `id_mono (fold pre)` is NOT part of `RgaInv` (`= contains 0 = false ∧ wf`), so M2's
  `Inv`-at-fold does not carry it; it is a separate reachable invariant
  (`id_mono_init`/`_doIns`/`_doDel`) whose step needs the RGA `mono_alloc` predicate,
  which M2 holds only in `causal_mono` (vis/id-ordering) form;
* `fresh_ts a (fold pre)` (for an `Ins`, `a.1 ≠ 0 ∧ contains (fold pre) a.1 = false`)
  is *state-absence*; M2's `freshTs` gives only id-distinctness `∀ x ∈ pre, x.1 ≠ a.1`,
  needing a contains-tracking induction ("folding ops whose ids ≠ t keeps t dead");
* `NoFreshClash a b` (RGA form: `b.id ∉ recList a` / `xb ≠ 0`) vs. M2's vis-ancestor
  form needs `recList a = ids of {a} ∪ vis-ancestors(a)` under `HistFaithful`.

VERDICT: `RGA_update_convergence` does NOT close unconditionally.  GAP 1 alone is
decisive and type-level.  Everything that lines up is mechanized below; the headline
is the commented goal in §3.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAUpdateConvergence

open Sal.Emulation
open Sal.ConditionedMRDTs.ConditionedExecutionModel
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (applySeqR)

/-! ## §0  The fold bridge: the engine's `applySeqR` IS M2's `applySeq` at `RGACondSig`

`RGACondSig.update = do_` and `RGACondSig.init = init_st`, so `applySeq` over
`RGACondSig.toCRDTSig` from `init` is definitionally the engine's `applySeqR`. -/

/-- The engine fold and the M2 fold coincide (definitional). -/
theorem fold_bridge (pre : List op_t) :
    applySeqR init_st pre = applySeq RGACondSig.toCRDTSig RGACondSig.init pre := rfl

/-! ## §1  RGA discharge of M2's configuration discipline fields

An RGA `ConditionedConfiguration` (`D := RGACondSig`) needs `inv_init : RgaInv init_st`
and `inv_step : ∀ s o, RgaInv s → (accurate o s ∧ fresh_ts o s) → RgaInv (do_ s o)`.
Both are RGA reachability facts, so the model is always inhabitable in these fields. -/

/-- `RGACondSig.inv_init`, discharged: `RgaInv init_st`. -/
theorem rgaCond_inv_init : RGACondSig.Inv RGACondSig.init := Inv_init

/-- `RGACondSig.inv_step`, discharged: `RgaInv` is preserved by every `applicable`
(`accurate ∧ fresh_ts`) op.  `Ins` via `Inv_doIns`, `Del` via `Inv_doDel`. -/
theorem rgaCond_inv_step (s : concrete_st) (o : op_t)
    (h : RGACondSig.Inv s) (happ : RGACondSig.applicable o s) :
    RGACondSig.Inv (RGACondSig.update s o) := by
  obtain ⟨t, r, op⟩ := o
  obtain ⟨hacc, hfr⟩ := happ
  cases op with
  | Ins e pre a => exact Inv_doIns s t r e a pre h hacc hfr
  | Del pre x => exact Inv_doDel s t r x pre h hacc

/-! ## §2  The clean slice of the M2 → RGA `hReady` bridge

`C.conditioned_premises` (M2) supplies, for a `vis`-concurrent pair pending at a
`noopFeasible` `E`-drawn prefix, the non-`Faithful` conjuncts in generic form.  Its
FIRST two — distinct timestamps and `D.Inv`-at-fold — bridge to the RGA-native forms
`a.1 ≠ b.1`, `contains (fold pre) 0 = false`, `wf (fold pre)` cleanly, since
`RGACondSig.Inv = RgaInv = (contains 0 = false ∧ wf)` and the two folds coincide (§0).
The remaining conjuncts are the GAP-3 cluster (see the header). -/

/-- **Clean `hReady` conjuncts from M2.**  The three timestamp/`RgaInv`-level
conjuncts of `hReady`, discharged from `C.conditioned_premises` for a `vis`-concurrent
pair `a, b` pending at a `noopFeasible` prefix `pre ⊆ E`.  These are exactly the
conjuncts `hReady` shares with `RgaInv`; the rest is the located gap cluster. -/
theorem hReady_clean_conjuncts (C : ConditionedConfiguration RGACondSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (pre : List op_t) (hpre_sub : ∀ x ∈ pre, x ∈ E)
    (hpre_feas : noopFeasible RGACondSig pre RGACondSig.init)
    {a b : op_t} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b)
    (hanp : a ∉ pre) (hbnp : b ∉ pre) (hconc : C.Concurrent a b) :
    a.1 ≠ b.1
    ∧ contains (applySeqR init_st pre) 0 = false
    ∧ wf (applySeqR init_st pre) := by
  have hp := C.conditioned_premises E hE pre hpre_sub hpre_feas ha hb hab hanp hbnp hconc
  obtain ⟨hd, hInv, _, _, _, _⟩ := hp
  -- `hInv : RGACondSig.Inv (applySeq RGACondSig.toCRDTSig RGACondSig.init pre)`
  --       ≡ RgaInv (applySeqR init_st pre) = (contains … 0 = false ∧ wf …)   [defeq, §0]
  obtain ⟨h0, hwf⟩ := hInv
  exact ⟨hd, h0, hwf⟩

/-! ## §3  The headline — the commented goal (blocked by the GAP cluster, esp. GAP 1)

`RGA_update_convergence` cannot be produced by feeding `hReady` to
`RGA_conditioned_convergence_bothFaithful`: `hReady` quantifies `pre` over ALL lists
(GAP 1), and no total discharging function exists (some conjuncts are provably false
at a bad `pre`).  The intended statement is recorded here with its goal; resolving it
requires the coordinator to restate the engine with a prefix-restricted oracle
(GAP 1) and to close GAP 2 / GAP 3.  We do NOT `sorry` it.

```
theorem RGA_update_convergence
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (Sal.ConditionedMRDTs.ConditionedConvergence.loOnA RGACondSig Cfg E))
    (h₂r : respects π₂ (Sal.ConditionedMRDTs.ConditionedConvergence.loOnA RGACondSig Cfg E))
    (hN₁ : noopFeasible RGACondSig π₁ RGACondSig.init)
    (hN₂ : noopFeasible RGACondSig π₂ RGACondSig.init) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂)
-- PROOF would be:
--   apply RGAConditionedConvergence.RGA_conditioned_convergence_bothFaithful
--           (loOnA RGACondSig Cfg E) E π₁ π₂ h₁p h₂p h₁r h₂r
--   intro pre a b ha hb hab hnab hnba
--   ⟨ hReady_clean_conjuncts …            -- 3 conjuncts: OK
--   , id_mono …, fresh_ts a …, fresh_ts b …   -- GAP 3
--   , faithful_at_enablement_ins … a, … b      -- GAP 2 (+ GAP 1: `pre` arbitrary)
--   , NoFreshClash …, NoFreshClash … ⟩         -- GAP 3
-- but `pre` here is UNCONSTRAINED (GAP 1) so this function cannot be total.
```
-/

/-! ## §4  Axiom audit — every mechanized bridge is kernel-clean (no `sorryAx`). -/

#print axioms fold_bridge
#print axioms rgaCond_inv_init
#print axioms rgaCond_inv_step
#print axioms hReady_clean_conjuncts

end Sal.ConditionedMRDTs.RGAUpdateConvergence
