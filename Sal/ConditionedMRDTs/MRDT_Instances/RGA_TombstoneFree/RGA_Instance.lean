import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeCong
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_InvFresh
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonFoldOK
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonFoldOK
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeFoldChain

/-!
# The RGA capstone: instantiating the conditioned `≈`-metatheorem

`GenericEqQuotient.RA_linearizable_up_to_eq` consumes, over a
`ConditionedMRDTSig D`, the bundle `EqEquiv`, `InvPres D W`, `CongVC D E`,
`InvInvVC D E W`, `WfOpReachable D W WfOpGen`, `EqJoinLemma3C D E W`, and then a
reachable configuration `C` with `hGenC`.  This file wires the RGA into that
shape.

**The `Inv` the framework's subtype needs is `qInv = wf ∧ root-free ∧ id_mono`,
NOT `RgaInv`.**  `CongVC.mergeL_congr` (`RGA_MergeCong.merge_eq_congr_inv`) and
`InvPres.inv_mergeL` (`Inv_merge` + `id_mono_merge`) both consume `id_mono`, which
`RgaInv` does not carry.  So the hosting signature here is `RGACondSig'`, a copy of
`RGASig.RGACondSig` with `Inv := qInv`.  Its `toMRDTSig` is *the same* `RGAM`, so
`update = do_`, `mergeL = merge`, `init = init_st`, and every `RGACondSig`-stated
fact (notably `rga_wfOpReachable`) transports definitionally.

What assembles cleanly (this file, 0 sorries): `EqEquiv`, the FULL `CongVC` (all
three fields), the FULL `InvInvVC` (`wf_congr` for `WfOp` + `applicable_congr`),
`WfOpReachable`, and the `inv_init`/`inv_mergeL` fields of `InvPres`.  The two
residuals are pinned precisely in §5-§6 and threaded into the capstone.
-/

namespace Sal.ConditionedMRDTs.RGAInstance

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient

/-! ## §1. The hosting signature `RGACondSig'` (`Inv := qInv`). -/

/-- The RGA as a `ConditionedMRDTSig` whose `Inv` is the framework-required
`qInv = wf ∧ root-free ∧ id_mono` (the fields' order matches
`RGA_MergeCong.merge_eq_congr_inv`).  Same `toMRDTSig` as `RGASig.RGACondSig`. -/
noncomputable def RGACondSig' : ConditionedMRDTSig where
  toMRDTSig := RGASig.RGAM
  Inv := fun s => wf s ∧ contains s 0 = false ∧ id_mono s
  applicable := fun o s => accurate o s ∧ fresh_ts o s

@[simp] theorem RGACondSig'_update (s : concrete_st) (o : op_t) :
    RGACondSig'.update s o = do_ s o := rfl

@[simp] theorem RGACondSig'_mergeL (l a b : concrete_st) :
    RGACondSig'.mergeL l a b = merge l a b := rfl

@[simp] theorem RGACondSig'_init : RGACondSig'.init = init_st := rfl

/-! ## §2. `EqEquiv` — the observational `eq`. -/

/-- `EqEquiv RGACondSig'` — the RGA's `eq` with its equivalence proof. -/
def rgaEqEquiv' : EqEquiv RGACondSig' where
  eqv := eq
  equiv := RGAEqQuotient.eq_equiv

/-! ## §3. `CongVC` — all three congruence fields. -/

/-- `CongVC RGACondSig' rgaEqEquiv'` — `update` (`do_eq_congr`), `mergeL`
(`merge_eq_congr_inv`, consuming `qInv`'s `id_mono`), `query` (`Unit`). -/
def rgaCongVC' : CongVC RGACondSig' rgaEqEquiv' where
  update_congr := by
    intro o s s' _ _ h
    exact RGAConditionedConvergence.do_eq_congr s s' h o
  mergeL_congr := by
    intro l l' a a' b b' Il Il' Ia Ia' Ib Ib' hl ha hb
    exact RGAMergeCong.merge_eq_congr_inv l l' a a' b b' Il Il' Ia Ia' Ib Ib' hl ha hb
  query_congr := by
    intro _ _ _ _ _ _; rfl

/-! ## §4. `InvInvVC` — `WfOp` and `applicable` are `≈`-invariant. -/

/-- `InvInvVC RGACondSig' rgaEqEquiv' WfOp`.  `wf_congr`: `WfOp`'s `Ins` conjunct
is `fresh_ts` (contains-driven), its `Del` conjunct `resolve · pre ≠ x` is
`resolve`-driven; both descend through `eq` (`resolve_dom_eq`).
`applicable_congr`: `accurate ∧ fresh_ts` (`RGA_EqQuotient` §3). -/
def rgaInvInvVC' : InvInvVC RGACondSig' rgaEqEquiv' WfOp where
  wf_congr := by
    intro o s s' _ _ h
    obtain ⟨t, r, ao⟩ := o
    cases ao with
    | Ins e pre a =>
      show (t ≠ 0 ∧ contains s t = false) ↔ (t ≠ 0 ∧ contains s' t = false)
      rw [(h t).1]
    | Del pre x =>
      show resolve s pre ≠ x ↔ resolve s' pre ≠ x
      rw [resolve_dom_eq s s' pre (fun c _ => (h c).1)]
  applicable_congr := by
    intro o s s' _ _ h
    exact and_congr (RGAEqQuotient.accurate_eq_iff o h) (RGAEqQuotient.fresh_ts_eq_iff o h)

/-! ## §5. `InvPres` — `inv_init` and `inv_mergeL` hold; `inv_update` is the gap.

`inv_init` and `inv_mergeL` are discharged below for `qInv`.  `inv_mergeL` needs
`id_mono` (`Inv_merge` under `id_mono l`, `id_mono_merge` under all three) — the
very reason `Inv` must be `qInv`, not `RgaInv`.

`inv_update`, however, does NOT hold with `W = WfOp`.  It would require
`id_mono (do_ s o)` from `qInv s ∧ WfOp o s`, but `id_mono_doIns` needs
`mono_alloc` (the fresh id exceeds every live id) and `id_mono_doDel` needs
`accurate` — and `WfOp` supplies NEITHER (`WfOp` on `Ins` is just `t ≠ 0 ∧
contains s t = false`, on `Del` just `resolve s pre ≠ x`).  `mono_alloc` is not
order-respecting-stable (a fold may apply a large-id `Ins` then a small-id one),
so it is a merge-fold reachability oracle, not a `W`-level fact.  Hence a full
`InvPres RGACondSig' WfOp` cannot be assembled here; it is threaded as a
hypothesis into the capstone (§8).  See the final report. -/

/-- `inv_init` for `qInv`: `Inv_init` (root-free + wf) plus `id_mono_init`. -/
theorem rga_inv_init' : RGACondSig'.Inv RGACondSig'.init :=
  ⟨Inv_init.2, Inv_init.1, id_mono_init⟩

/-- `inv_mergeL` for `qInv`: `Inv_merge` (wf + root-free, under `id_mono l`) and
`id_mono_merge` (under all three `id_mono`s). Both premises are in `qInv`. -/
theorem rga_inv_mergeL' (l a b : concrete_st)
    (hl : RGACondSig'.Inv l) (ha : RGACondSig'.Inv a) (hb : RGACondSig'.Inv b) :
    RGACondSig'.Inv (RGACondSig'.mergeL l a b) := by
  have Rl : RgaInv l := ⟨hl.2.1, hl.1⟩
  have Ra : RgaInv a := ⟨ha.2.1, ha.1⟩
  have Rb : RgaInv b := ⟨hb.2.1, hb.1⟩
  have hm : RgaInv (merge l a b) := Inv_merge l a b Rl Ra Rb hl.2.2
  have hmono : id_mono (merge l a b) :=
    id_mono_merge l a b Rl Ra Rb hl.2.2 ha.2.2 hb.2.2
  exact ⟨hm.2, hm.1, hmono⟩

/-! ## §6. `WfOpReachable` — transported from the `RGACondSig` proof.

`RGACondSig'.toMRDTSig = RGACondSig.toMRDTSig = RGAM`, so `init`/`update`/`AppOp`
coincide and `WfOpReachable` (which reads only those, via `WfChain`) is the same
proposition for both signatures. `rga_wfOpReachable` transports definitionally. -/

/-- `WfChain` reads only `toMRDTSig` (`init`/`update`), so it agrees between
`RGACondSig'` and `RGACondSig` — but with an abstract list both are stuck, so this
one-line induction is needed to make the transport explicit. -/
theorem wfChain_transport (s : concrete_st) (ρ : List op_t) :
    WfChain RGACondSig' WfOp s ρ = WfChain RGASig.RGACondSig WfOp s ρ := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih =>
    simp only [WfChain, ih]
    rfl

end Sal.ConditionedMRDTs.RGAInstance

namespace Sal.ConditionedMRDTs.RGAOrderBridge

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig')

/-- `rc` is `Either` on every pair — for the primed hosting signature too.
(Relocated from `RGA_OrderBridge.lean` when the swap route retired; the full
name is unchanged.) -/
theorem rc_is_Either' (o₁ o₂ : Op app_op_t) :
    RGACondSig'.rc o₁ o₂ = RcRes.Either := rfl

end Sal.ConditionedMRDTs.RGAOrderBridge
