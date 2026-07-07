import Sal.MRDTs.Metatheory.Conditioned.RGA_LoOnEq_Causal
import Sal.MRDTs.Metatheory.Conditioned.ConditionedExecutionModel

/-!
# δ-B — a `loOnEq`-respecting enumeration of the delta exists

*Additive; modifies no existing file; 0 `sorry`.*

hEnum, step B (the order-existence half).  The generic `exists_respecting`
(`ConditionedExecutionModel`) turns an acyclicity witness (a minimal element in every nonempty
sub-list) into a respecting permutation.  For the RGA, `loOnEq ⊆ vis` (`loOnEq_imp_vis`) and `vis` is a
finite strict order (transitive + irreflexive — the honest-execution hypotheses), so a `vis`-minimal
element is `loOnEq`-minimal: the acyclicity is discharged with NO extra hypotheses.  This yields
`listPermOf π E ∧ respects π (loOnEq … E)` for any finitely-enumerated event set — the `loOnEq`-order
half of hEnum's δ-enum, leaving only `noopFeasible` (step C).
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGADeltaEnum

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient (loOnEq)
open Sal.Metatheory.RGAInstance (rgaEqEquiv')
open Sal.Metatheory.RGALoOnEqCausal (loOnEq_imp_vis)
open Sal.Metatheory.ConditionedExecutionModel.ConditionedConfiguration (exists_respecting)

/-- **A finite list under a strict order has a minimal element in every nonempty sub-list.**
Transitivity + irreflexivity give acyclicity; induction picks the minimum.  The acyclicity witness
`exists_respecting` consumes. -/
theorem exists_min_of_irrefl_trans {α : Type} (R : α → α → Prop)
    (htr : ∀ {a b c : α}, R a b → R b c → R a c) (hirr : ∀ a, ¬ R a a) :
    ∀ (l : List α), l ≠ [] → ∃ m ∈ l, ∀ y ∈ l, ¬ R y m := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _
    by_cases hrest : rest = []
    · subst hrest
      exact ⟨a, by simp, fun y hy => by
        rw [List.mem_singleton] at hy; rw [hy]; exact hirr a⟩
    · obtain ⟨m, hm, hmin⟩ := ih hrest
      by_cases hR : R a m
      · refine ⟨a, by simp, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hyr
        · exact hirr _
        · exact fun hRya => hmin y hyr (htr hRya hR)
      · refine ⟨m, List.mem_cons_of_mem a hm, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hyr
        · exact hR
        · exact hmin y hyr

/-- **δ-B: a `loOnEq`-respecting enumeration exists.**  From any `Nodup` list `lE` enumerating the
event set `E` and `vis` a strict order, `exists_respecting` (with acyclicity discharged via
`exists_min_of_irrefl_trans` on `vis` + `loOnEq_imp_vis`) yields a permutation `π` that `listPermOf E`
and `respects (loOnEq … E)`.  The RGA analog of `exists_loOnA_enum`, for the `loOnEq` order the merge
δ-enum must respect. -/
theorem exists_loOnEq_enum (W : op_t → concrete_st → Prop) (vis : op_t → op_t → Prop)
    (E : Set op_t) (lE : List op_t) (hnd : lE.Nodup) (henum : ∀ a, a ∈ lE ↔ a ∈ E)
    (htr : ∀ {a b c : op_t}, vis a b → vis b c → vis a c) (hirr : ∀ a, ¬ vis a a) :
    ∃ π, listPermOf π E ∧ respects π (loOnEq rgaEqEquiv' W vis E) := by
  obtain ⟨π, hperm, hpw⟩ := exists_respecting (loOnEq rgaEqEquiv' W vis E) lE.length lE rfl
    (fun l' _ hne => by
      obtain ⟨m, hm, hmin⟩ := exists_min_of_irrefl_trans vis (@htr) hirr l' hne
      exact ⟨m, hm, fun y hy hlo => hmin y hy (loOnEq_imp_vis W vis E y m hlo)⟩)
  refine ⟨π, ⟨hperm.nodup_iff.mpr hnd, fun a => ?_⟩, hpw⟩
  rw [hperm.mem_iff]; exact henum a

#print axioms exists_min_of_irrefl_trans
#print axioms exists_loOnEq_enum

end Sal.Metatheory.RGADeltaEnum
