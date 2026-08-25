import Sal.MRDTs.Metatheory.Join.RA_Linearizability

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

/-- Projection used by the update/replay metatheory inherited from the binary
CRDT development. Binary merge is derived from the initial-base slice; it is
not an independent MRDT field. -/
abbrev toCRDTSig (D : MRDTSig) : CRDTSig where
  State := D.State
  dec_state := D.dec_state
  init := D.init
  AppOp := D.AppOp
  dec_op := D.dec_op
  Query := D.Query
  Value := D.Value
  update := D.update
  merge := D.merge D.init
  query := D.query

/-- Reused binary replay infrastructure sees exactly the initial-base slice of
the sole MRDT merge operation. -/
@[simp] theorem toCRDTSig_merge (D : MRDTSig) (a b : D.State) :
    D.toCRDTSig.merge a b = D.merge D.init a b := rfl

@[simp] theorem toCRDTSig_update (D : MRDTSig) (s : D.State)
    (e : Op D.AppOp) :
    D.toCRDTSig.update s e = D.update s e := rfl

end MRDTSig

end Sal.MRDTs
