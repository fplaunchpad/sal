import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Skeleton3_Leaves
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_HcausHdec_Discharge
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_HHext_Discharge

/-!
# FINAL ASSEMBLY: RGA RA-linearizability up to ≈, on the honest-execution residual

*0 `sorry`.*

Every proof-theoretic leaf of the raw-≈ capstone is discharged and instantiated here:

* `hEnum`  := `rga_hEnum_discharged`, the delta enum + K1 discipline continuation;
* `hCanon` := `hCanon_of_leaves3 rgaHonJ rga_hMergeInputs_discharged`, both canonical facts,
  from the fully-discharged merge bundle `{Hdec, hcaus, hbridge}`;
* `hHext`  := `rga_hHext_discharged`, the witness discipline extends at applicable applies.

**The remaining residual is exactly the honest-execution content**, quantified once:

* `hHon`, at every reachable configuration, the join context `rgaHonJ` holds of the core
  (generation discipline from born accuracy, nonzero ids, Lamport clocks, no root deletes;
  the configuration witness is the core itself);
* `hBA`, born-applicable delivery (each applied op is `qapplicable` at its head class, and
  `applicable ⟹ WfOpA` for it).

Both are statements about the EXECUTION MODEL (what an honest RGA implementation delivers),
not about the datatype: the datatype side is closed.
-/

set_option maxHeartbeats 400000

open Classical

namespace Sal.ConditionedMRDTs.RGASkeleton3

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3H
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGAK1Delta (rgaHonJ rga_hEnum_discharged rga_hMergeInputs_discharged)

/-- **THE FINAL THEOREM (datatype side closed).**  The tombstone-free RGA is per-version
RA-linearizable up to observational `≈` at every reachable configuration, given only the
honest-execution residual `hHon` (the join context at reachable cores) and `hBA`
(born-applicable delivery). -/
theorem rga_RA_linearizable_final
    (hHon : ∀ {C₀ : Sal.ConditionedMRDTs.Configuration
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)},
      (labeledTS3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C₀ →
      rgaHonJ (Sal.ConditionedMRDTs.Configuration.core C₀).vis
        (Sal.ConditionedMRDTs.Configuration.core C₀).events)
    (hBA : ∀ {C₀ C₁ : Sal.ConditionedMRDTs.Configuration
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t α}
      {v : Sal.ConditionedMRDTs.Version}
      {sh : QState (RGACondSig' α) (rgaEqEquiv' α)} {evh : Set (Op (app_op_t α))},
      (labeledTS3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C₀ →
      Sal.ConditionedMRDTs.Step3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)
        C₀ (Sal.ConditionedMRDTs.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable (rgaEqEquiv' α) WfOpA rgaInvInvVCA (t, r, o) sh ∧
        (∀ s', (RGACondSig' α).applicable (t, r, o) s' → WfOpA (t, r, o) s'))
    (C : Sal.ConditionedMRDTs.Configuration
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA))
    (hReach : (labeledTS3
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
      (Sal.ConditionedMRDTs.initConfig
        (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C) :
    IsRALinearizable3Eq (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA C :=
  rga_RA_linearizable_skeleton3 rgaHonJ
    (fun hreach => hHon hreach)
    rga_hEnum_discharged
    (hCanon_of_leaves3 rgaHonJ rga_hMergeInputs_discharged)
    (fun hreach hstep hhead hver ρ hρp hH happ =>
      rga_hHext_discharged hreach hstep hhead hver ρ hρp hH happ)
    hBA C hReach

/-! ## Axiom audit -/

#print axioms rga_RA_linearizable_final

end Sal.ConditionedMRDTs.RGASkeleton3
