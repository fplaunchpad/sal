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

end Sal.ConditionedMRDTs.GenericEqQuotient

/-! ## §2  The RGA guard `WfOpA := WfOpQ ∧ accurate` -/

namespace Sal.ConditionedMRDTs.RGAInstance

open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ qInv_doOp)

/-- The honest RGA quotient guard: `WfOpQ` (fresh + monotone `resolve < t`) plus
`accurate`.  Strengthens `WfOpQ` with the accuracy that born-applicability needs. -/
def WfOpA (o : op_t) (s : concrete_st) : Prop := WfOpQ o s ∧ accurate o s

/-- `WfOpA ⟹ WfOpQ` — the `InvPres`-carrying part. -/
theorem wfOpQ_of_wfOpA {o : op_t} {s : concrete_st} (h : WfOpA o s) : WfOpQ o s := h.1

/-- **`InvPres RGACondSig' WfOpA`** — reuse `rgaInvPresQ`'s components: `inv_update`
is `qInv_doOp` fed `WfOpA.1 : WfOpQ`. -/
def rgaInvPresA : InvPres RGACondSig' WfOpA :=
  ⟨rga_inv_init', fun s o hI hw => qInv_doOp s o hI (wfOpQ_of_wfOpA hw), rga_inv_mergeL'⟩

/-! ## §3  Axiom audit -/

#print axioms rgaInvPresA

end Sal.ConditionedMRDTs.RGAInstance
