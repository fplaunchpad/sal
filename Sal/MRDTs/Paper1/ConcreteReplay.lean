import Sal.MRDTs.Paper1.ConcreteFormalism
import Sal.MRDTs.Paper1.GuardedConvergence
import Sal.MRDTs.Paper1.GuardedOrder

/-! Guarded replay and canonical-state uniqueness in the concrete state space. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT
open Foundation
variable {D : MRDTSig}

theorem replay_equal {P : OperationPolicy D.AppOp}
    (laws : GuardedReplay.Laws D.toUpdateSig P)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : Supported C E) (s : D.State)
    {π₁ π₂ : List (Op D.AppOp)}
    (hp₁ : listPermOf π₁ E) (hp₂ : listPermOf π₂ E)
    (hr₁ : respects π₁ (paperOrder P C E))
    (hr₂ : respects π₂ (paperOrder P C E)) :
    applySeq D.toUpdateSig s π₁ = applySeq D.toUpdateSig s π₂ :=
  convergence_on_guarded laws s supported hp₁ hp₂ hr₁ hr₂

theorem canonical_unique {P : OperationPolicy D.AppOp}
    (laws : GuardedReplay.Laws D.toUpdateSig P)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : Supported C E) {s t : D.State}
    (hs : Canonical P C E s) (ht : Canonical P C E t) : s = t := by
  obtain ⟨π₁,hp₁,hr₁,hf₁⟩ := hs
  obtain ⟨π₂,hp₂,hr₂,hf₂⟩ := ht
  exact hf₁.symm.trans ((replay_equal laws C E supported D.init hp₁ hp₂ hr₁ hr₂).trans hf₂)

theorem canonical_query_unique {P : OperationPolicy D.AppOp}
    (laws : GuardedReplay.Laws D.toUpdateSig P)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (supported : Supported C E) {s t : D.State}
    (hs : Canonical P C E s) (ht : Canonical P C E t) (q : D.Query) :
    D.query s q = D.query t q := congrArg (fun x => D.query x q)
      (canonical_unique laws C E supported hs ht)

theorem canonical_exists {P : OperationPolicy D.AppOp}
    (laws : GuardedReplay.Laws D.toUpdateSig P)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp))
    (finite : E.Finite) (supported : E ⊆ C.events)
    (trans : ∀ {a b c}, C.vis a b → C.vis b c → C.vis a c)
    (irrefl : ∀ a, ¬ C.vis a a) : ∃ s, Canonical P C E s := by
  classical
  have hp : listPermOf finite.toFinset.toList E := by
    refine ⟨Finset.nodup_toList _, ?_⟩
    intro a
    simp
  obtain ⟨π,hp,hr⟩ := GuardedReplay.exists_paperOrder_enumeration laws trans irrefl supported hp
  exact ⟨applySeq D.toUpdateSig D.init π,π,hp,hr,rfl⟩

#print axioms canonical_unique
#print axioms canonical_exists
end Sal.MRDTs.Paper1.ConcreteMRDT
