import Sal.MRDTs.Paper1.SequentialSimulation
import Sal.MRDTs.Paper1.SpecificationVisibility

/-! A proof-only projection into an independently supplied sequential machine.
Concrete execution and the merge laws continue to use implementation equality.
The projection is neither an implementation quotient nor a definition of the
sequential specification. -/
namespace Sal.MRDTs.Paper1
open Foundation

structure MachineProjection (D : MRDTSig) {U : Type}
    (M : DeterministicSpec U D.Query D.Value) (label : Op D.AppOp → U) where
  project : D.State → M.State
  initial : project D.init = M.initial
  update : ∀ s e, project (D.update s e) = M.update (project s) (label e)
  observes : ∀ s q, D.query s q = M.query (project s) q

namespace MachineProjection
variable {D : MRDTSig} {U : Type} {M : DeterministicSpec U D.Query D.Value}
    {label : Op D.AppOp → U}

/-- A surjective projection transfers concrete swaps to every abstract state,
and hence to arbitrary query/update contexts in the independent language. -/
theorem language_commutes (H : MachineProjection D M label)
    (onto : Function.Surjective H.project) (a b : Op D.AppOp)
    (commute : D.toUpdateSig.commutes a b) :
    M.toSpec.Commutes (label a) (label b) := by
  apply M.language_commutes
  intro state
  obtain ⟨concrete, rfl⟩ := onto state
  have same := congrArg H.project (commute concrete)
  simpa only [H.update] using same

def simulation {M : DeterministicSpec D.AppOp D.Query D.Value}
    (H : MachineProjection D M Op.op) : SequentialSimulation D M where
  Rel s a := H.project s = a
  initial := H.initial
  update s a h e := by subst a; exact H.update s e
  observes s a h q := by subst a; exact H.observes s q

end MachineProjection
end Sal.MRDTs.Paper1

/-- The same projection equations build operation-only or full-event local
simulations. The expected simulation type determines the label alphabet. -/
macro "derive_projected_simulation " description:term : tactic => `(tactic| (
  refine { Rel := fun s a => ($description).project s = a
           initial := ($description).initial
           update := ?_
           observes := ?_ }
  · intro s a h e; subst a; exact ($description).update s e
  · intro s a h q; subst a; exact ($description).observes s q))
