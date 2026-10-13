import Mathlib.Data.List.Induction

/-! History induction and causal-prefix transport independent of an MRDT's
carrier, operation constructors, and issuance predicate. -/
namespace Sal.MRDTs.Foundation

/-- Reverse induction restricted to an independently supplied prefix-closed
history language. The invariant may retain semantic facts needed by later steps. -/
theorem legal_snoc_induction {Event : Type} {Legal Inv : List Event → Prop}
    (prefix_closed : ∀ pre e, Legal (pre ++ [e]) → Legal pre)
    (initial : Inv [])
    (step : ∀ pre e, Legal (pre ++ [e]) → Inv pre → Inv (pre ++ [e]))
    {ops : List Event} (legal : Legal ops) : Inv ops := by
  induction ops using List.reverseRecOn with
  | nil => exact initial
  | append_singleton pre e ih =>
      exact step pre e legal (ih (prefix_closed pre e legal))

/-- Two snoc-recursive computations agree after projection when their initial
states and local transitions agree. No completed history theorem is an input. -/
theorem snoc_fold_fusion {Event Concrete Abstract : Type}
    (concrete : List Event → Concrete) (abstract : List Event → Abstract)
    (project : Concrete → Abstract) (step : Abstract → Event → Abstract)
    (initial : project (concrete []) = abstract [])
    (concrete_step : ∀ pre e,
      project (concrete (pre ++ [e])) = step (project (concrete pre)) e)
    (abstract_step : ∀ pre e, abstract (pre ++ [e]) = step (abstract pre) e)
    (ops : List Event) : project (concrete ops) = abstract ops := by
  exact legal_snoc_induction (Legal := fun _ => True)
    (Inv := fun ops => project (concrete ops) = abstract ops)
    (fun _ _ _ => True.intro) initial
    (fun pre e _ ih => by
      change project (concrete (pre ++ [e])) = abstract (pre ++ [e])
      rw [concrete_step, abstract_step, ih]) True.intro

/-- An event's guard only sees its preceding prefix. Appending a suffix cannot
change that prefix, including when the guard existentially selects an origin. -/
theorem split_guard_prefix {Event : Type} {Guard : List Event → Event → Prop}
    {pre suf : List Event}
    (guarded : ∀ before e after, pre ++ suf = before ++ e :: after →
      Guard before e) :
    ∀ before e after, pre = before ++ e :: after → Guard before e := by
  intro before e after split
  apply guarded before e (after ++ suf)
  simp [split, List.append_assoc]

end Sal.MRDTs.Foundation
