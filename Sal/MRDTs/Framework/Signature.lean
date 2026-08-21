import Sal.MRDTs.Metatheory.Join.RA_Linearizability

/-!
# Mergeable replicated datatype signatures

The operational datatype contains no client invariant and no operation
applicability predicate.  Those belong to certificates over executions, not
to the raw transition system.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

/-- A mergeable replicated datatype with an explicit LCA input to merge. -/
structure MRDTSig extends CRDTSig where
  mergeL : State → State → State → State
  merge_init_slice : ∀ a b, mergeL init a b = merge a b

/-- Optional proof domain for algorithms whose updates commute only under
additional local hypotheses.  This certificate does not restrict raw
execution and is not required of every datatype. -/
structure LocalCommutationDomain (D : MRDTSig) where
  Domain : D.State → Prop
  Admissible : Op D.AppOp → D.State → Prop
  init : Domain D.init
  update_preserves : ∀ s e,
    Domain s → Admissible e s → Domain (D.update s e)
  commutes : ∀ s a b,
    Domain s → Admissible a s → Admissible b s →
      D.update (D.update s a) b = D.update (D.update s b) a

end Sal.MRDTs
