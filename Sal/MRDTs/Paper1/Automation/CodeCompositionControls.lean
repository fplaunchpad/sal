import Sal.MRDTs.Paper1.Automation.GenericCodeCombinators
import Sal.MRDTs.Paper1.Automation.GenericTerminatedTags

/-! Small independent controls for the code algebra. Negative companions expose
the assumptions whose removal would make decoding invalid. -/
namespace Sal.MRDTs.Paper1.Automation.CodeCompositionControls
open PrefixCodes

def bitCode : Code (fun _ : Bool => True) (fun b => [b]) :=
  Code.fixedWidth _ _ 1 (by decide) (by simp) (by simp)

def pairCode : Code (fun _ : Bool × Bool => True ∧ True)
    (fun p => [p.1] ++ [p.2]) := bitCode.product bitCode

example : encode (fun p : Bool × Bool => [p.1] ++ [p.2])
    [(false, true), (true, false)] = [false, true, true, false] := rfl
example : encode (fun p : Bool × Bool => [p.1] ++ [p.2])
    [(false, true), (true, false)] ≠ [false, true] := by decide

theorem pair_decode (xs ys : List (Bool × Bool))
    (equal : encode (fun p => [p.1] ++ [p.2]) xs =
      encode (fun p => [p.1] ++ [p.2]) ys) : xs = ys :=
  encode_injective pairCode xs ys (by simp) (by simp) equal

example : ¬ Code (fun _ : Bool => True) (fun _ => ([] : List Bool)) := by
  intro code
  exact code.nonempty false trivial rfl

example : ¬ Code (fun _ : Bool => True) (fun _ => [false]) := by
  intro code
  exact code.prefixFree false true trivial trivial (by decide) List.prefix_rfl

/- Separate branch codes do not suffice without disjoint output alphabets. -/
example : ¬ Code (fun _ : Bool ⊕ Bool => True)
    (Sum.elim (fun b => [b]) (fun b => [b])) := by
  intro code
  exact code.prefixFree (.inl false) (.inr false) trivial trivial
    (by simp) List.prefix_rfl

def tagCode : Code (TerminatedTag (0 : Nat) 3 (fun n => n ≤ 5)) id :=
  TerminatedTag.code 0 3 (fun n => n ≤ 5)

example : TerminatedTag (0 : Nat) 3 (fun n => n ≤ 5) [1, 2, 3] := by
  right
  exact ⟨1, [2], rfl, by decide, by decide, by decide, by simp⟩

/- An internal terminator would make this word extend another complete tag. -/
example : ¬ TerminatedTag (0 : Nat) 3 (fun n => n ≤ 5) [1, 3, 2, 3] := by
  intro valid
  have short : TerminatedTag (0 : Nat) 3 (fun n => n ≤ 5) [1, 3] :=
    Or.inr ⟨1, [], rfl, by decide, by decide, by decide, by simp⟩
  exact short.prefixFree valid (by decide) ⟨[2, 3], rfl⟩

#print axioms pair_decode
#print axioms tagCode
end Sal.MRDTs.Paper1.Automation.CodeCompositionControls
