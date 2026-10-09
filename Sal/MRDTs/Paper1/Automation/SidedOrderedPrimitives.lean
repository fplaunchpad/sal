import Sal.MRDTs.Instances.SidedEmbedRGA
import Sal.MRDTs.Paper1.Automation.GenericLexOrder

/-! Equation certificates identify the native algorithms with generic list
algorithms. No native correctness lemma is an input. -/
namespace Sal.MRDTs.Paper1.Automation.SidedPrimitives
open Sal.EmbedRGA Sal.MRDTs.Instances.SidedEmbedRGA
open Sal.MRDTs.Paper1.Automation.OrderedLists
def order : Order (fun p : SRec => sKey p.2.2)
    (fun p q => keyLt (sKey p.2.2) (sKey q.2.2)) :=
  orderOfComparator keyLt (by rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (fun p : SRec => sKey p.2.2)

theorem insertion (r : SRec) (s : SState) :
    sInsert r s = insert (fun p q => keyLt (sKey p.2.2) (sKey q.2.2)) r s := by
  apply insert_eq
  · intros; rfl
  · intros; rfl

theorem merging (a b : SState) :
    sMerge2 a b = merge2 (fun p q => keyLt (sKey p.2.2) (sKey q.2.2)) a b := by
  apply merge2_eq
  · intros; rw [sMerge2]
  · intro xs; cases xs <;> simp [sMerge2]
  · intros; rw [sMerge2]
end Sal.MRDTs.Paper1.Automation.SidedPrimitives
