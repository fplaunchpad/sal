import Sal.ConditionedMRDTs.Metatheory.GoodConfig3NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_WfOpA_VCs

/-!
# RGA instantiation of the born-applicable `≈`-metatheorem

Plugs the tombstone-free RGA into `GoodConfig3NF.RA_linearizable_up_to_eq_NF` at the
honest guard `W := WfOpA`.  Discharges `hInvCong` (`qInv` is `≈`-invariant) and the
four quotient VCs (`rgaInvPresA`, `(rgaCongVC' α)`, `rgaInvInvVCA`, and the
`GuardNoopChain` guard-transparency).  The result is per-version
RA-linearizability of any reachable RGA configuration under the born-applicable
discipline, gated only on `EqJoinLemma3C_NF` (the merge residual) and the
two honest-execution hypotheses `hBA` (clients apply accurate ops) and `hgenW`
(events genuine).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace Sal.ConditionedMRDTs.RGAInstanceNF

variable {α : Type} [DecidableEq α] [Inhabited α]

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3NF
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC' WfOpA rgaInvPresA
  rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGAEqQuotient (wf_eq_invariant contains_zero_eq_iff id_mono_eq_invariant)

/-- **`qInv` is `≈`-invariant** — the `hInvCong` the datatype apply extension needs.
Each conjunct (`wf`, root-freeness, `id_mono`) descends through `eq`. -/
theorem rga_invCong {s s' : concrete_st α} (h : (rgaEqEquiv' α).eqv s s')
    (hI : (RGACondSig' α).Inv s) : (RGACondSig' α).Inv s' := by
  obtain ⟨hwf, h0, hmono⟩ := hI
  exact ⟨wf_eq_invariant h hwf, (contains_zero_eq_iff h).mp h0, id_mono_eq_invariant h hmono⟩

/-- **RGA per-version RA-linearizability over born-applicable delivery.**  The RGA
instance of `RA_linearizable_up_to_eq_NF` at `W := WfOpA`, with `hInvCong`
discharged by `rga_invCong` and the four VCs plugged in.  Remaining honest inputs:
`hJoinNF` (the RGA merge residual), `hBA` (born-applicable delivery),
`hgenW` (genuine events). -/
theorem rga_RA_linearizable_NF
    (hJoinNF : EqJoinLemma3C_NF (RGACondSig' α) (rgaEqEquiv' α) WfOpA)
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
    (hReach : (labeledTS3 (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA) trivial) C)
    (hgenW : ∀ o ∈ (Sal.ConditionedMRDTs.Configuration.core C).events,
        ∀ s', (RGACondSig' α).applicable o s' → WfOpA o s') :
    Sal.ConditionedMRDTs.IsRALinearizable3 C :=
  RA_linearizable_up_to_eq_NF (rgaEqEquiv' α) WfOpA rgaInvPresA (rgaCongVC' α) rgaInvInvVCA
    (fun {_ _} h hI => rga_invCong h hI) hJoinNF hBA C hReach hgenW

/-! ## Axiom audit -/

#print axioms rga_invCong
#print axioms rga_RA_linearizable_NF

end Sal.ConditionedMRDTs.RGAInstanceNF
