import Sal.MRDTs.Framework.Base.UpdateSignature

/-!
# Mergeable replicated datatype signatures

The raw datatype contains only executable state transitions.  Semantic
invariants, applicability, and conditioned commutation live in the certificate
layer.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

/-- A mergeable replicated datatype with an explicit common-ancestor input to
merge. This is the sole implementer-supplied merge operation. -/
structure MRDTSig where
  State : Type
  dec_state : DecidableEq State
  init : State
  AppOp : Type
  dec_op : DecidableEq AppOp
  Query : Type
  Value : Type
  update : State → Op AppOp → State
  merge : State → State → State → State
  query : State → Query → Value

namespace MRDTSig

attribute [instance] dec_state dec_op

/-- Merge-free update projection used by finite folds and replay invariants. -/
abbrev toUpdateSig (D : MRDTSig) : UpdateSig where
  State := D.State
  dec_state := D.dec_state
  init := D.init
  AppOp := D.AppOp
  dec_op := D.dec_op
  update := D.update

/-- Install the initial-base slice only when a retained historical binary
theorem explicitly asks for a two-way merge capability. -/
instance historicalBinaryMerge (D : MRDTSig) :
    HistoricalBinaryMerge D.toUpdateSig where
  binaryMerge := D.merge D.init

/-- The optional historical binary capability uses exactly the initial-base
slice of the sole MRDT merge operation. It is not a field of `toUpdateSig`. -/
@[simp] theorem historicalBinaryMerge_eq_initialSlice
    (D : MRDTSig) (a b : D.State) :
    D.toUpdateSig.historicalMerge a b = D.merge D.init a b := rfl

@[simp] theorem toUpdateSig_update (D : MRDTSig) (s : D.State)
    (e : Op D.AppOp) :
    D.toUpdateSig.update s e = D.update s e := rfl

end MRDTSig

end Sal.MRDTs
