import Mathlib.Data.List.Induction

/-! The reusable induction for an independent sequential machine. The legality
predicate is an input; it is never defined through the implementation replay. -/
namespace Sal.MRDTs.Paper1.Automation

theorem guarded_fold_projection {Event Concrete Abstract : Type}
    (concrete : List Event → Concrete) (abstract : List Event → Abstract)
    (project : Concrete → Abstract) (step : Abstract → Event → Abstract)
    (legal : List Event → Prop)
    (initial : project (concrete []) = abstract [])
    (abstract_snoc : ∀ pre e, abstract (pre ++ [e]) = step (abstract pre) e)
    (prefix_closed : ∀ pre e, legal (pre ++ [e]) → legal pre)
    (local_step : ∀ pre e, legal (pre ++ [e]) →
      project (concrete (pre ++ [e])) = step (project (concrete pre)) e)
    {ops : List Event} (hlegal : legal ops) :
    project (concrete ops) = abstract ops := by
  induction ops using List.reverseRecOn with
  | nil => exact initial
  | append_singleton pre e ih =>
    rw [local_step pre e hlegal, abstract_snoc pre e, ih (prefix_closed pre e hlegal)]

/-- Filtering by an observable field commutes with record projection. -/
theorem map_filter_project {Record View : Type} (project : Record → View)
    (keep : View → Bool) (records : List Record) :
    (records.filter (fun r => keep (project r))).map project =
      (records.map project).filter keep := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : keep (project r) = true <;> simp [h, ih]

end Sal.MRDTs.Paper1.Automation
