import Sal.MRDTs.Framework.Execution

/-! Trace induction independent of datatype state equality and specification. -/
namespace Sal.MRDTs.Paper1.ExecutionTrace
open Foundation

theorem visited {T : LabeledTS} {Good : T.State → Prop}
    (preserve : ∀ s l t, Good s → T.step s l t → Good t)
    {initial : T.State} {trace : List (T.Label × T.State)}
    (execution : T.Execution initial trace) (start : Good initial) :
    ∀ entry ∈ trace, Good entry.2 := by
  induction execution with
  | nil => simp
  | @cons s t l rest step _ ih =>
    have head := preserve s l t start step
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact head
    · exact ih head entry he

end Sal.MRDTs.Paper1.ExecutionTrace
