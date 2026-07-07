import Sal.MRDTs.Metatheory.Conditioned.GoodConfig3NF
import Sal.MRDTs.Metatheory.Conditioned.RGA_WfOpA_VCs

/-!
# RGA instantiation of the born-applicable `≈`-metatheorem

*Additive; modifies no existing file; 0 `sorry`.*

Plugs the tombstone-free RGA into `GoodConfig3NF.RA_linearizable_up_to_eq_NF` at the
honest guard `W := WfOpA`.  Discharges `hInvCong` (`qInv` is `≈`-invariant) and the
four quotient VCs (`rgaInvPresA`, `rgaCongVC'`, `rgaInvInvVCA`, and the
`GuardNoopChain` guard-transparency — all done).  The result is per-version
RA-linearizability of any reachable RGA configuration under the born-applicable
discipline — GATED ONLY on `EqJoinLemma3C_NF` (the merge residual, WALL 1) and the
two honest-execution hypotheses `hBA` (clients apply accurate ops) and `hgenW`
(events genuine).  `GenDisc2CEq` is GONE.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAInstanceNF

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.GoodConfig3NF
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC' WfOpA rgaInvPresA
  rgaInvInvVCA)
open Sal.Metatheory.RGAEqQuotient (wf_eq_invariant contains_zero_eq_iff id_mono_eq_invariant)

/-- **`qInv` is `≈`-invariant** — the `hInvCong` the datatype apply extension needs.
Each conjunct (`wf`, root-freeness, `id_mono`) descends through `eq`. -/
theorem rga_invCong {s s' : concrete_st} (h : rgaEqEquiv'.eqv s s')
    (hI : RGACondSig'.Inv s) : RGACondSig'.Inv s' := by
  obtain ⟨hwf, h0, hmono⟩ := hI
  exact ⟨wf_eq_invariant h hwf, (contains_zero_eq_iff h).mp h0, id_mono_eq_invariant h hmono⟩

/-- **RGA per-version RA-linearizability over born-applicable delivery.**  The RGA
instance of `RA_linearizable_up_to_eq_NF` at `W := WfOpA`, with `hInvCong`
discharged by `rga_invCong` and the four VCs plugged in.  Remaining honest inputs:
`hJoinNF` (= the RGA merge residual, WALL 1), `hBA` (born-applicable delivery),
`hgenW` (genuine events). -/
theorem rga_RA_linearizable_NF
    (hJoinNF : EqJoinLemma3C_NF RGACondSig' rgaEqEquiv' WfOpA)
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
    (hReach : (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.Metatheory.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C)
    (hgenW : ∀ o ∈ (Sal.Metatheory.Configuration.core C).events,
        ∀ s', RGACondSig'.applicable o s' → WfOpA o s') :
    Sal.Metatheory.IsRALinearizable3 C :=
  RA_linearizable_up_to_eq_NF rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA
    (fun {_ _} h hI => rga_invCong h hI) hJoinNF hBA C hReach hgenW

/-! ## Axiom audit -/

#print axioms rga_invCong
#print axioms rga_RA_linearizable_NF

end Sal.Metatheory.RGAInstanceNF
