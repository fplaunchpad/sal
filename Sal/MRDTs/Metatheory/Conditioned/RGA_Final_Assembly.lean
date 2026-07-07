import Sal.MRDTs.Metatheory.Conditioned.RGA_Skeleton3_Leaves
import Sal.MRDTs.Metatheory.Conditioned.RGA_HcausHdec_Discharge
import Sal.MRDTs.Metatheory.Conditioned.RGA_HHext_Discharge

/-!
# FINAL ASSEMBLY — RGA RA-linearizability up to ≈, on the honest-execution residual

*Additive; modifies no existing file; 0 `sorry`.*

Every proof-theoretic leaf of the raw-≈ capstone is now DISCHARGED and instantiated here:

* `hEnum`  := `rga_hEnum_discharged`  — the delta enum + K1 discipline continuation;
* `hCanon` := `hCanon_of_leaves3 rgaHonJ rga_hMergeInputs_discharged` — both canonical facts,
  from the fully-discharged merge bundle `{Hdec, hcaus, hbridge}`;
* `hHext`  := `rga_hHext_discharged`  — the witness discipline extends at applicable applies.

**The remaining residual is exactly the honest-execution content**, quantified once:

* `hHon` — at every reachable configuration, the join context `rgaHonJ` holds of the core
  (generation discipline from born accuracy, nonzero ids, Lamport clocks, no root deletes;
  the configuration witness is the core itself);
* `hBA` — born-applicable delivery (each applied op is `qapplicable` at its head class, and
  `applicable ⟹ WfOpA` for it).

Both are statements about the EXECUTION MODEL (what an honest RGA implementation delivers),
not about the datatype: the datatype side is closed.
-/

set_option maxHeartbeats 400000

open Classical

namespace Sal.Metatheory.RGASkeleton3

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.GoodConfig3H
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.Metatheory.RGAK1Delta (rgaHonJ rga_hEnum_discharged rga_hMergeInputs_discharged)

/-- **THE FINAL THEOREM (datatype side closed).**  The tombstone-free RGA is per-version
RA-linearizable up to observational `≈` at every reachable configuration, given only the
honest-execution residual `hHon` (the join context at reachable cores) and `hBA`
(born-applicable delivery). -/
theorem rga_RA_linearizable_final
    (hHon : ∀ {C₀ : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)},
      (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
      rgaHonJ (Sal.Metatheory.Configuration.core C₀).vis
        (Sal.Metatheory.Configuration.core C₀).events)
    (hBA : ∀ {C₀ C₁ : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
      {v : Sal.Metatheory.Version}
      {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)},
      (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
      Sal.Metatheory.Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
        C₀ (Sal.Metatheory.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable rgaEqEquiv' WfOpA rgaInvInvVCA (t, r, o) sh ∧
        (∀ s', RGACondSig'.applicable (t, r, o) s' → WfOpA (t, r, o) s'))
    (C : Sal.Metatheory.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA))
    (hReach : (labeledTS3
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
      (Sal.Metatheory.initConfig
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C) :
    IsRALinearizable3Eq rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA C :=
  rga_RA_linearizable_skeleton3 rgaHonJ
    (fun hreach => hHon hreach)
    rga_hEnum_discharged
    (hCanon_of_leaves3 rgaHonJ rga_hMergeInputs_discharged)
    (fun hreach hstep hhead hver ρ hρp hH happ =>
      rga_hHext_discharged hreach hstep hhead hver ρ hρp hH happ)
    hBA C hReach

/-! ## Axiom audit -/

#print axioms rga_RA_linearizable_final

end Sal.Metatheory.RGASkeleton3
