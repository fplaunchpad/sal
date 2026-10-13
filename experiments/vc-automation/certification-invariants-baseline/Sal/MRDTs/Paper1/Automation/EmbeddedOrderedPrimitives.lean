import Sal.MRDTs.Instances.EmbedRGA
import Sal.MRDTs.Paper1.Automation.GenericLexOrder

/-! Equation certificates identify the native algorithms with generic list
algorithms. No native correctness lemma is an input. -/
namespace Sal.MRDTs.Paper1.Automation.EmbeddedPrimitives
open Sal.EmbedRGA Sal.MRDTs.Instances.EmbedRGA
open Sal.MRDTs.Paper1.Automation.OrderedLists
variable {α : Type} [DecidableEq α] [Inhabited α]
def order : Order (fun p : ERec α => key p.2.2)
    (fun p q => keyLt (key p.2.2) (key q.2.2)) :=
  orderOfComparator keyLt (by rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (fun p : ERec α => key p.2.2)

theorem insertion (r : ERec α) (s : EState α) :
    eInsert r s = insert (fun p q => keyLt (key p.2.2) (key q.2.2)) r s := by
  apply insert_eq
  · intros; rfl
  · intros; rfl

theorem merging (a b : EState α) :
    eMerge2 a b = merge2 (fun p q => keyLt (key p.2.2) (key q.2.2)) a b := by
  apply merge2_eq
  · intros; rw [eMerge2]
  · intro xs; cases xs <;> simp [eMerge2]
  · intros; rw [eMerge2]
end Sal.MRDTs.Paper1.Automation.EmbeddedPrimitives
