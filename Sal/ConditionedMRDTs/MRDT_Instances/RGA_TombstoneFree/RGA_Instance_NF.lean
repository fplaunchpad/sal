import Sal.ConditionedMRDTs.Metatheory.GoodConfig3NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_WfOpA_VCs

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

namespace Sal.ConditionedMRDTs.RGAInstanceNF

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3NF
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC' WfOpA rgaInvPresA
  rgaInvInvVCA)
open Sal.ConditionedMRDTs.RGAEqQuotient (wf_eq_invariant contains_zero_eq_iff id_mono_eq_invariant)

/-- **`qInv` is `≈`-invariant** — the `hInvCong` the datatype apply extension needs.
Each conjunct (`wf`, root-freeness, `id_mono`) descends through `eq`. -/
theorem rga_invCong {s s' : concrete_st} (h : rgaEqEquiv'.eqv s s')
    (hI : RGACondSig'.Inv s) : RGACondSig'.Inv s' := by
  obtain ⟨hwf, h0, hmono⟩ := hI
  exact ⟨wf_eq_invariant h hwf, (contains_zero_eq_iff h).mp h0, id_mono_eq_invariant h hmono⟩

/-! ## Axiom audit -/

#print axioms rga_invCong

end Sal.ConditionedMRDTs.RGAInstanceNF
