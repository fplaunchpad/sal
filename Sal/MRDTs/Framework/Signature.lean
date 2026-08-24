import Sal.MRDTs.Metatheory.Join.RA_Linearizability

/-!
# Mergeable replicated datatype signatures

The raw datatype contains only executable state transitions.  Semantic
invariants, applicability, and conditioned commutation live in the certificate
layer.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

/-- A mergeable replicated datatype with an explicit LCA input to merge. -/
structure MRDTSig extends CRDTSig where
  mergeL : State → State → State → State
  merge_init_slice : ∀ a b, mergeL init a b = merge a b

end Sal.MRDTs
