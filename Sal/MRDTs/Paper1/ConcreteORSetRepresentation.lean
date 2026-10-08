import Sal.MRDTs.Paper1.GuardedORSet
import Sal.MRDTs.Paper1.ConcreteJoin

namespace Sal.MRDTs.Paper1
open Foundation Classical

namespace ORSet.ConcreteRep
variable {α : Type} [DecidableEq α]
/-- Exact history-indexed tag evidence, stronger than equality of views. -/
def representation : ConcreteMRDT.Representation (D α) :=
  fun C E s => @IsCanonicalState (D α).toUpdateSig (conflict α).lift C E s


end ORSet.ConcreteRep

namespace EfficientORSet.ConcreteRep
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
def representation : ConcreteMRDT.Representation (D α) := fun C E s =>
  Represents C.vis E s ∧ (∃ π : List (Event α), listPermOf π E) ∧
  (∀ e ∈ E, e ∈ C.events) ∧ Transitive C.vis ∧
  (∀ a b, C.vis a b → a.time < b.time)


end EfficientORSet.ConcreteRep
end Sal.MRDTs.Paper1
