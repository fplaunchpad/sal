import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_InvUpdateQ
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance

/-!
# Born-applicability from the quotient guard — the foundation of the re-base

*Additive; modifies no existing file; 0 `sorry`, kernel-clean.*

The re-base's pivot (`LOONA_VS_LOONEQ_ANALYSIS.md`, and KC's framing that
`applicable` is a first-class field of the extended MRDT definition): the honest
conditioned execution model must guard its updates with **`applicable`**, not a
weaker well-formedness proxy.  This file certifies the two enabling facts.

## §1 (generic).  `appOrNoop_qsig`

For the guarded quotient `QSig E W …`, `update = qdo = doW` is
`if W o s then do_ else s`.  **If the guard implies applicability**
(`W o s → D.applicable o s`), then every quotient step is
`applicable`-or-no-op (`appOrNoop`):

* the guard fires ⟹ `qdo` applies `do_` AND the op is `qapplicable` (applicable
  branch);
* the guard fails ⟹ `qdo` is the identity (`doW = s`), a literal no-op.

So born-applicability is INTRINSIC to a guarded quotient whose guard is at least
`applicable` — no witness decoration, no `GenDisc2CEq`.  This is the generic
engine behind `GoodConfig3NF`'s apply step: the newly-applied op is `appOrNoop`
at the version state FOR FREE.

## §2 (RGA).  The guard `WfOpA := WfOpQ ∧ accurate`

`WfOpQ` (fresh + the monotone `resolve < t` bound) already discharges
`InvPres` (`RGA_InvUpdateQ.rgaInvPresQ` — closing the old `W = WfOp`
`inv_update` gap via `idMono_doIns_wfq` / `idMono_doDel_wfq`), but it is strictly
WEAKER than `applicable` (it never demands `accurate`).  The re-base's guard adds
accuracy back:

* `WfOpA ⟹ WfOpQ` keeps the full `InvPres` (`rgaInvPresA`);
* `WfOpA ⟹ applicable` (`= accurate ∧ fresh_ts`) feeds `appOrNoop_qsig` — born
  applicability.

`WfOpA` is the honest guard: `applicable` for convergence + the `WfOpQ`
monotone bound for `id_mono`.  Under the honest per-op genuineness `WfOpGenQ`
the monotone bound is free, so on genuine ops `WfOpA` coincides with `applicable`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.GenericEqQuotient

open Sal.Emulation
open Sal.ConditionedMRDTs.ConditionedConvergence (appOrNoop)

variable {D : ConditionedMRDTSig}

/-- **Born-applicability of a guarded quotient.**  If the guard `W` implies
`D.applicable`, then every step of `QSig E W hP hC hA` is `applicable`-or-no-op.
The guard firing gives the applicable branch; the guard failing makes `qdo` the
identity (a genuine no-op). -/
theorem appOrNoop_qsig (E : EqEquiv D) (W : Op D.AppOp → D.State → Prop)
    (hP : InvPres D W) (hC : CongVC D E) (hA : InvInvVC D E W)
    (hWapp : ∀ (o : Op D.AppOp) (s : D.State), D.Inv s → W o s → D.applicable o s)
    (o : Op D.AppOp) (q : QState D E) :
    appOrNoop (QSig E W hP hC hA) o q := by
  refine Quotient.inductionOn q (fun sp => ?_)
  obtain ⟨s, hs⟩ := sp
  by_cases hW : W o s
  · -- guard fires: applicable branch
    left
    show D.applicable o s
    exact hWapp o s hs hW
  · -- guard fails: `qdo` is the identity
    right
    show qdo E W hP hC hA (qmk E s hs) o = qmk E s hs
    rw [qdo_qmk, qmk_eq_iff]
    show E.eqv (doW D W o s) s
    have hd : doW D W o s = s := if_neg hW
    rw [hd]
    exact E.equiv.refl s

end Sal.ConditionedMRDTs.GenericEqQuotient

/-! ## §2  The RGA guard `WfOpA := WfOpQ ∧ accurate` -/

namespace Sal.ConditionedMRDTs.RGAInstance

open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ qInv_doOp rgaInvPresQ WfOpGenQ
  wfOpQ_ins_of_genQ wfOpQ_del_of_genQ)

/-- The honest RGA quotient guard: `WfOpQ` (fresh + monotone `resolve < t`) plus
`accurate`.  Strengthens `WfOpQ` with the accuracy that born-applicability needs. -/
def WfOpA (o : op_t) (s : concrete_st) : Prop := WfOpQ o s ∧ accurate o s

/-- `WfOpA ⟹ WfOpQ` — the `InvPres`-carrying part. -/
theorem wfOpQ_of_wfOpA {o : op_t} {s : concrete_st} (h : WfOpA o s) : WfOpQ o s := h.1

/-- **`WfOpA ⟹ applicable`.**  `applicable = accurate ∧ fresh_ts`; `WfOpA`
supplies `accurate` directly and `fresh_ts` from `WfOpQ`. -/
theorem applicable_of_wfOpA {o : op_t} {s : concrete_st} (h : WfOpA o s) :
    RGACondSig'.applicable o s := by
  obtain ⟨hwfq, hacc⟩ := h
  refine ⟨hacc, ?_⟩
  obtain ⟨t, r, ao⟩ := o
  cases ao with
  | Ins e pre a => exact hwfq.1
  | Del pre x => trivial

/-- **`InvPres RGACondSig' WfOpA`** — reuse `rgaInvPresQ`'s components: `inv_update`
is `qInv_doOp` fed `WfOpA.1 : WfOpQ`. -/
def rgaInvPresA : InvPres RGACondSig' WfOpA :=
  ⟨rga_inv_init', fun s o hI hw => qInv_doOp s o hI (wfOpQ_of_wfOpA hw), rga_inv_mergeL'⟩

/-- **`applicable ⟹ WfOpA` on genuine ops** — the `hWA` the exec-side bridge
(`isCanonicalState_of_NF`) needs.  `WfOpA = WfOpQ ∧ accurate`; `accurate` is
`applicable`'s first conjunct, and `WfOpQ` follows from the honest per-op
`WfOpGenQ` (`wfOpQ_ins_of_genQ` at the `applicable`-supplied freshness;
`wfOpQ_del_of_genQ` unconditionally). So for born-applicable delivery of genuine
ops the guard fires exactly when the op is applicable. -/
theorem wfOpA_of_genQ_applicable {o : op_t} {s : concrete_st}
    (hg : WfOpGenQ o) (happ : RGACondSig'.applicable o s) : WfOpA o s := by
  obtain ⟨hacc, hfr⟩ := happ
  obtain ⟨t, r, ao⟩ := o
  cases ao with
  | Ins e pre a => exact ⟨wfOpQ_ins_of_genQ s t r e a pre hg hfr.2, hacc⟩
  | Del pre x => exact ⟨wfOpQ_del_of_genQ s t r x pre hg, hacc⟩

/-- **Born-applicability of the RGA quotient at `WfOpA`.**  `WfOpA ⟹ applicable`,
so `appOrNoop_qsig` applies: every `QSig … WfOpA`-step is `applicable`-or-no-op. -/
theorem rga_appOrNoop_qsig (hC : CongVC RGACondSig' rgaEqEquiv')
    (hA : InvInvVC RGACondSig' rgaEqEquiv' WfOpA)
    (o : op_t) (q : QState RGACondSig' rgaEqEquiv') :
    Sal.ConditionedMRDTs.ConditionedConvergence.appOrNoop
      (QSig rgaEqEquiv' WfOpA rgaInvPresA hC hA) o q :=
  appOrNoop_qsig rgaEqEquiv' WfOpA rgaInvPresA hC hA
    (fun _o _s _ hw => applicable_of_wfOpA hw) o q

/-! ## §3  Axiom audit -/

#print axioms appOrNoop_qsig
#print axioms applicable_of_wfOpA
#print axioms rgaInvPresA
#print axioms rga_appOrNoop_qsig

end Sal.ConditionedMRDTs.RGAInstance
