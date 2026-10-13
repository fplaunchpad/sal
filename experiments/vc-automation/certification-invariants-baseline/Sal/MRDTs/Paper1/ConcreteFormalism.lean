import Sal.MRDTs.Paper1.EventBridge
import Sal.MRDTs.Paper1.GuardedReplay

/-! Concrete implementation semantics. State equality is actual equality,
independently of the language used to specify sequential query answers. -/
namespace Sal.MRDTs.Paper1.ConcreteMRDT
open Foundation
variable {D : MRDTSig}

abbrev Representation (D : MRDTSig) :=
  ReplayContext D.toUpdateSig → Set (Op D.AppOp) → D.State → Prop

def RepresentationJoin (R : Representation D) : Prop :=
  ∀ (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp)) (l a b : D.State),
    Transitive C.vis → (∀ e, ¬ C.vis e e) →
    (∀ e ∈ E₁, e ∈ C.events) → (∀ e ∈ E₂, e ∈ C.events) →
    (∀ e f, C.vis e f → f ∈ E₁ → e ∈ E₁) →
    (∀ e f, C.vis e f → f ∈ E₂ → e ∈ E₂) →
    R C (E₁ ∩ E₂) l → R C E₁ a → R C E₂ b →
    R C (E₁ ∪ E₂) (D.merge l a b)


def Supported (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) : Prop :=
  ∀ e ∈ E, e ∈ C.events

abbrev order (P : OperationPolicy D.AppOp) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) := paperOrder P C E

def Canonical (P : OperationPolicy D.AppOp) (C : ReplayContext D.toUpdateSig)
    (E : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∃ π : List (Op D.AppOp), listPermOf π E ∧ respects π (paperOrder P C E) ∧
    applySeq D.toUpdateSig D.init π = s

abbrev VersionsWitness (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) :=
  EventVersionsSpecificationRA D P S C

end Sal.MRDTs.Paper1.ConcreteMRDT
