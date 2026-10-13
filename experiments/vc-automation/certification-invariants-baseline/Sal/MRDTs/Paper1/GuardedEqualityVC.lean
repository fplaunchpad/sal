import Sal.MRDTs.Instances.EfficientORSet

/-! Raw add equations require coherent metadata premises, independently of
whether guarded update commutation laws hold. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.GuardedEqualityVC
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

/-- A reconstruction past must contain every old tag that the new add
replaces in the remainder. Freshness alone does not suffice. -/
theorem causal_add_eq (A B : State α) (et er : Nat) (x : α)
    (fresh : (er,et,x) ∉ B)
    (covered : ∀ p ∈ A, p.1 = er → p.2.2 = x → p ∈ B) :
    merge B A (update B (et,er,.add x)) = update A (et,er,.add x) := by
  ext p
  rcases p with ⟨r,t,y⟩
  simp only [merge,update,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,
    Finset.mem_insert,Finset.mem_filter,Prod.mk.injEq]
  have cover := covered (r,t,y)
  simp only at cover
  grind

/-- Raw local add redistribution follows when any killed tag shared by
its past and the other branch is recorded in the merge base. -/
theorem local_add_eq (l B t s : State α) (et er : Nat) (x : α)
    (freshPast : (er,et,x) ∉ B) (freshBase : (er,et,x) ∉ l)
    (shared : ∀ p ∈ B, p ∈ s → p.1 = er → p.2.2 = x → p ∈ l) :
    merge l (merge B t (update B (et,er,.add x))) s =
      merge B (merge l t s) (update B (et,er,.add x)) := by
  ext p
  rcases p with ⟨r,ts,y⟩
  have sharing := shared (r,ts,y)
  simp only at sharing
  simp only [merge,update,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,
    Finset.mem_insert,Finset.mem_filter,Prod.mk.injEq]
  grind

/-- PASS+FAIL: raw causal add differs while ordinary-set observations agree.
The missing older tag in the past is precisely the missing coverage premise. -/
theorem causal_add_freshness_insufficient :
    (0,2,7) ∉ (∅ : State Nat) ∧
    merge ∅ {(0,1,7)} (update ∅ (2,0,.add 7)) = {(0,1,7),(0,2,7)} ∧
    merge ∅ {(0,1,7)} (update ∅ (2,0,.add 7)) ≠
      update {(0,1,7)} (2,0,.add 7) ∧
    elements (merge ∅ {(0,1,7)} (update ∅ (2,0,.add 7))) =
      elements (update {(0,1,7)} (2,0,.add 7)) := by decide

/-- PASS+FAIL: local redistribution needs coherent base metadata. Here the
old tag shared by the past and other side is absent from the base. -/
theorem local_add_incoherent_base :
    merge ∅ (merge {(0,1,7)} ∅ (update {(0,1,7)} (2,0,.add 7))) {(0,1,7)} =
      ({(0,1,7),(0,2,7)} : State Nat) ∧
    merge ∅ (merge {(0,1,7)} ∅ (update {(0,1,7)} (2,0,.add 7))) {(0,1,7)} ≠
      merge {(0,1,7)} (merge ∅ ∅ {(0,1,7)}) (update {(0,1,7)} (2,0,.add 7)) ∧
    elements (merge ∅ (merge {(0,1,7)} ∅ (update {(0,1,7)} (2,0,.add 7))) {(0,1,7)}) =
      elements (merge {(0,1,7)} (merge ∅ ∅ {(0,1,7)}) (update {(0,1,7)} (2,0,.add 7))) := by decide

#print axioms causal_add_eq
#print axioms local_add_eq
#print axioms causal_add_freshness_insufficient
#print axioms local_add_incoherent_base

end Sal.MRDTs.Paper1.EfficientORSet.GuardedEqualityVC
