import Sal.Emulation.Conditioned_Emulation

/-!
# Operation-based RA-linearizability transfer: typed endpoint

The transfer project now targets the corrected conditioned metatheory:

`OpCRDTSig → shapiroConditionedG → VerifiedMRDT → trace transfer`.

The old scaffold targeted `SatisfiesVCs` and concluded a predicate defined as
`True`; both have been retired. Priority 4 supplies label-morphic weak
simulations. Priority 5 will define operation-based RA-linearizability as a
genuine weak-trace property and prove the final theorem. This file deliberately
states only the already meaningful typed boundary.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs

/-- All datatype-specific semantic work required before trace transfer: a
conditioned certificate for the Shapiro emulator. -/
structure ConditionedTransferInput (D : OpCRDTSig)
    (hb : D.Msg → D.Msg → Prop) where
  schedule : CausalSchedule D hb
  verified : ShapiroVerified D schedule

namespace ConditionedTransferInput

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

theorem initInv (I : ConditionedTransferInput D hb) :
    (shapiroConditionedG D I.schedule).Inv
      (shapiroConditionedG D I.schedule).init :=
  I.verified.initInv

end ConditionedTransferInput

end Sal.Emulation
