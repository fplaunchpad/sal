import Sal.MRDTs.Paper1.MetadataJoin
import Sal.MRDTs.Paper1.EfficientMetadataCausal
import Sal.MRDTs.Paper1.MetadataORSet

/-! Both OR-set replay supplies are constructed without merge Join. Exact
set uses its restricted concrete replay laws; efficient set uses represented
tag histories and timestamp monotonicity carried by its input evidence. -/
namespace Sal.MRDTs.Paper1
open Foundation

namespace ORSet.AbstractSpec
variable {α : Type} [DecidableEq α]

theorem replaySupply (C : ReplayContext (D α).toUpdateSig)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    AbstractMRDT.ReplaySupply (model (α := α)) (conflict α) representation
      (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) C := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  refine ⟨?_,?_⟩
  · intro E π perm supported
    exact isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
      (fun {_ _ _} h k => trans h k) irrefl perm supported
  · intro E s rep supported nonempty closed
    exact peel_choice C E s rep nonempty supported closed trans irrefl

end ORSet.AbstractSpec

namespace EfficientORSet.AbstractSpec
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem replaySupply (C : ReplayContext (D α).toUpdateSig)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (mono : ∀ a b, C.vis a b → a.time < b.time) :
    AbstractMRDT.ReplaySupply (model (α := α)) (EventSpec.conflict α) representation
      (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) C := by
  refine ⟨?_,?_⟩
  · intro E π perm supported
    exact representation_exists C E π perm supported trans mono
  · intro E s rep _ nonempty closed
    exact peel_choice C E s rep nonempty closed irrefl

end EfficientORSet.AbstractSpec
end Sal.MRDTs.Paper1
