import Sal.MRDTs.Paper1.AbstractCompatibility

/-! The canonical future-query abstraction is available even when an immediate
read hides information needed by later updates. Datatype ports may replace
this quotient with a more explicit abstract carrier. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation

def Model.future (D : MRDTSig) : Model D where
  Abstract := QueryReplay.State D
  abs := QueryReplay.observe D
  step := QueryReplay.update D
  read s q := Quotient.lift (fun t => D.query t q)
    (fun _ _ h => QueryReplay.equivalent_query h q) s
  update_abs := fun _ _ => rfl
  query_abs := fun _ _ => rfl

theorem future_equivalent (D : MRDTSig) (s t : D.State) :
    Equivalent (Model.future D) s t ↔ QueryReplay.Equivalent D s t :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem future_complete (D : MRDTSig) : (Model.future D).QueryComplete :=
  fun _ _ h => Quotient.sound h

theorem laws_of_all_commute {D : MRDTSig} (A : Model D)
    (commute : ∀ a b, D.toUpdateSig.commutes a b) :
    Laws A (commutingPolicy D.AppOp) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    simp [commutingPolicy, of_state_commutes (A := A) (commute a b)]
  · simp [commutingPolicy]
  · intro _ _ _ _ _ h
    exact h.elim

end Sal.MRDTs.Paper1.AbstractMRDT
