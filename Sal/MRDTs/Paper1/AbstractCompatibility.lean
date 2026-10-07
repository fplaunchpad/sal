import Sal.MRDTs.Paper1.AbstractFormalism
import Sal.MRDTs.Paper1.QueryReplay

/-! Compatibility with the earlier query-relative adapter. Immediate query
separation is used only for this adapter, not required by the primary model. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

def Model.ofQuery (A : QueryReplay.Abstraction D) : Model D where
  Abstract := A.Abstract
  abs := A.abs
  step := A.step
  read := A.read
  update_abs := A.update_abs
  query_abs := A.query_abs

theorem ofQuery_equivalent (A : QueryReplay.Abstraction D) (s t : D.State) :
    Equivalent (Model.ofQuery A) s t ↔ QueryReplay.Equivalent D s t :=
  (A.equivalent_iff s t).symm

theorem ofQuery_complete (A : QueryReplay.Abstraction D) : (Model.ofQuery A).QueryComplete :=
  fun s t h => (ofQuery_equivalent A s t).mpr h

theorem ofQuery_commutes (A : QueryReplay.Abstraction D) (a b : Op D.AppOp) :
    Commutes (Model.ofQuery A) a b ↔ QueryReplay.Commutes D a b := by
  simp only [Commutes,QueryReplay.Commutes,ofQuery_equivalent]

theorem ofQuery_order (A : QueryReplay.Abstraction D) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    order (Model.ofQuery A) P C E a b ↔ QueryReplay.order P C E a b := by
  simp only [order,QueryReplay.order,ofQuery_commutes]

theorem Laws.ofQuery {A : QueryReplay.Abstraction D} {P : OperationPolicy D.AppOp}
    (h : QueryReplay.Laws D P) : Laws (Model.ofQuery A) P := by
  refine ⟨?_,h.no_chain,?_⟩
  · intro a b
    rw [ofQuery_commutes]
    exact h.noncomm_exact a b
  · intro s a b c xs before conflict
    exact (ofQuery_equivalent A _ _).mpr
      (h.conditional_commutation s a b c xs before
        (fun hc => conflict ((ofQuery_commutes A b c).mpr hc)))

theorem canonical_ofQuery {A : QueryReplay.Abstraction D} {P : OperationPolicy D.AppOp}
    (laws : QueryReplay.Laws D P) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) (s : D.State)
    (h : QueryReplay.Canonical D P C E s) : Canonical (Model.ofQuery A) P C E s := by
  obtain ⟨π,hp,hr,hf⟩ := h
  apply (canonical_iff (Laws.ofQuery laws) C E s).mpr
  refine ⟨π,hp,?_,?_⟩
  · exact hr.imp (fun {a b} h edge => h
      ((paperOrder_iff_loOn laws.toRestricted _ _ _ _).mp
        ((QueryReplay.order_eq P C E b a).mp ((ofQuery_order A P C E b a).mp edge))))
  · change applySeq (QueryReplay.algebra D) (QueryReplay.observe D D.init) π =
      QueryReplay.observe D s at hf
    rw [QueryReplay.fold_observe] at hf
    exact (ofQuery_equivalent A _ _).mpr (Quotient.exact hf)

end Sal.MRDTs.Paper1.AbstractMRDT
