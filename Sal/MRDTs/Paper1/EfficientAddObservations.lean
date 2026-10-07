import Sal.MRDTs.Paper1.ORSetVCJoin

namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

/-- A common witness for the inserted element and equality on all other
records suffice for equality of the ordinary-set abstraction. -/
theorem elements_eq_of_inserted_witness (a b : State α) (r t : Nat) (x : α)
    (left : (r,t,x) ∈ a) (right : (r,t,x) ∈ b)
    (other : ∀ p : Record α, p.2.2 ≠ x → (p ∈ a ↔ p ∈ b)) : elements a = elements b := by
  apply Finset.ext
  intro y
  simp only [elements,Finset.mem_image]
  constructor
  · rintro ⟨p,hp,rfl⟩
    by_cases same : p.2.2 = x
    · exact ⟨(r,t,x),right,same.symm⟩
    · exact ⟨p,(other p same).mp hp,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    by_cases same : p.2.2 = x
    · exact ⟨(r,t,x),left,same.symm⟩
    · exact ⟨p,(other p same).mpr hp,rfl⟩

theorem causal_add_observation (A B : State α) (et er : Nat) (x : α)
    (fresh : (er,et,x) ∉ B) :
    elements (merge B A (update B (et,er,.add x))) = elements (update A (et,er,.add x)) := by
  apply elements_eq_of_inserted_witness _ _ er et x
  · simp [merge,update,fresh]
  · simp [update]
  · intro p ne
    have left : p ∈ update B (et,er,.add x) ↔ p ∈ B := by
      simp [update,ne]
      intro equal
      exact False.elim (ne (congrArg (fun p : Record α => p.2.2) equal))
    have right : p ∈ update A (et,er,.add x) ↔ p ∈ A := by
      simp [update,ne]
      intro equal
      exact False.elim (ne (congrArg (fun p : Record α => p.2.2) equal))
    simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,left,right]
    tauto

theorem local_add_observation (l B t s : State α) (et er : Nat) (x : α)
    (freshPast : (er,et,x) ∉ B) (freshBase : (er,et,x) ∉ l) :
    elements (merge l (merge B t (update B (et,er,.add x))) s) =
      elements (merge B (merge l t s) (update B (et,er,.add x))) := by
  apply elements_eq_of_inserted_witness _ _ er et x
  · simp [merge,update,freshPast,freshBase]
  · simp [merge,update,freshPast]
  · intro p ne
    have unchanged : p ∈ update B (et,er,.add x) ↔ p ∈ B := by
      simp [update,ne]
      intro equal
      exact False.elim (ne (congrArg (fun p : Record α => p.2.2) equal))
    simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,unchanged]
    tauto

theorem fresh_past_record (C : ReplayContext (D α).toUpdateSig)
    (B : State α) (et er : Nat) (x : α)
    (rep : Represents C.vis
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past (et,er,.add x) \
        {(et,er,.add x)}) B) : (er,et,x) ∉ B := by
  intro member
  exact ((rep (er,et,x)).mp member).1.2 rfl

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
