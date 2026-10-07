import Sal.MRDTs.Paper1.GuardedHistoryBridge

/-! Concrete equality specialization of the guarded history interface.
The identity model forgets no metadata. Specification refinement remains a
separate obligation. -/
namespace Sal.MRDTs.Paper1.Raw
open Foundation

def model (D : MRDTSig) : AbstractMRDT.Model D where
  Abstract := D.State
  abs := id
  step := D.update
  read := D.query
  update_abs _ _ := rfl
  query_abs _ _ := rfl

@[simp] theorem equivalent_iff (D : MRDTSig) (s t : D.State) :
    AbstractMRDT.Equivalent (model D) s t ↔ s = t := Iff.rfl

@[simp] theorem commutes_iff (D : MRDTSig) (a b : Op D.AppOp) :
    AbstractMRDT.Commutes (model D) a b ↔ D.toUpdateSig.commutes a b := Iff.rfl

def laws {D : MRDTSig} {P : OperationPolicy D.AppOp}
    (h : GuardedReplay.Laws D.toUpdateSig P) : AbstractMRDT.Guarded.Laws (model D) P where
  noncomm_exact := h.noncomm_exact
  no_chain := h.no_chain
  conditional_commutation := h.conditional_commutation

@[simp] theorem order_iff (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    AbstractMRDT.order (model D) P C E a b ↔ paperOrder P C E a b := Iff.rfl

@[simp] theorem canonical_iff (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State) :
    AbstractMRDT.Guarded.Canonical (model D) P C E s ↔
      ∃ π, listPermOf π E ∧ respects π (paperOrder P C E) ∧
        applySeq D.toUpdateSig D.init π = s := Iff.rfl

end Sal.MRDTs.Paper1.Raw
