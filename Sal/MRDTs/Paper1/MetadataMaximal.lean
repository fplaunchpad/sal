import Sal.MRDTs.Paper1.MetadataDependencies

/-! A common linear extension supplies a maximum for both semantic order and
metadata dependencies. Efficient OR-set's existing sorted history is such an
extension, independently of representation Join. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation

private theorem exists_last {β : Type} (xs : List β) (nonempty : xs ≠ []) :
    ∃ pre e, xs = pre ++ [e] := by
  induction xs using List.reverseRecOn with
  | nil => exact False.elim (nonempty rfl)
  | append_singleton xs e _ => exact ⟨xs,e,rfl⟩

theorem joint_maximal_of_enumeration {β : Type} {R M : β → β → Prop}
    {E : Set β} (π : List β) (perm : listPermOf π E) (nonempty : E.Nonempty)
    (semantic : respects π R) (metadata : respects π M) :
    ∃ e ∈ E, (∀ x ∈ E, x ≠ e → ¬ R e x) ∧ (∀ x ∈ E, x ≠ e → ¬ M e x) := by
  have hn : π ≠ [] := by
    intro h
    obtain ⟨e,he⟩ := nonempty
    have mem := (perm.2 e).mpr he
    simp [h] at mem
  obtain ⟨pre,e,hπ⟩ := exists_last π hn
  subst π
  refine ⟨e,(perm.2 e).mp (by simp),?_,?_⟩
  · intro x hx ne
    have mem : x ∈ pre := by
      simpa [ne] using (perm.2 x).mpr hx
    exact (List.pairwise_append.mp semantic).2.2 x mem e (by simp)
  · intro x hx ne
    have mem : x ∈ pre := by
      simpa [ne] using (perm.2 x).mpr hx
    exact (List.pairwise_append.mp metadata).2.2 x mem e (by simp)

end Sal.MRDTs.Paper1.AbstractMRDT

namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem joint_maximal (C : ReplayContext (D α).toUpdateSig) (E : Set (Event α))
    (π : List (Event α)) (perm : listPermOf π E) (nonempty : E.Nonempty)
    (trans : Transitive C.vis) (mono : ∀ a b, C.vis a b → a.time < b.time) :
    ∃ e ∈ E,
      (∀ x ∈ E, x ≠ e → ¬ AbstractMRDT.order (model (α := α)) (EventSpec.conflict α) C E e x) ∧
      (∀ x ∈ E, x ≠ e → ¬ (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).before e x) := by
  obtain ⟨sorted,hperm,hsort⟩ := exists_sorted C.vis E π perm
  apply AbstractMRDT.joint_maximal_of_enumeration sorted hperm nonempty
  · have ordered := QuerySpec.sorted_respects_order C E sorted hperm trans mono hsort
    exact ordered.imp (fun {a b} h edge => h
      ((AbstractMRDT.ofQuery_order QuerySpec.abstraction (EventSpec.conflict α) C E b a).mp edge))
  · apply hsort.imp_of_mem
    intro a b ha hb no edge
    exact no (before_of_vis C.vis E trans mono ((hperm.2 a).mp ha) edge.1
      (EventSpec.noncomm_same_element b a edge.2))

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec

namespace Sal.MRDTs.Paper1.ORSet.AbstractSpec
open Foundation
variable {α : Type} [DecidableEq α]

theorem joint_maximal (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α)))
    (s : (D α).State) (rep : representation C E s) (nonempty : E.Nonempty) :
    ∃ e ∈ E,
      (∀ x ∈ E, x ≠ e → ¬ AbstractMRDT.order (model (α := α)) (conflict α) C E e x) ∧
      (∀ x ∈ E, x ≠ e → ¬ (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).before e x) := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  obtain ⟨π,hp,hr,_⟩ := rep
  have commutation : ∀ a b, AbstractMRDT.Commutes (model (α := α)) a b ↔
      (D α).toUpdateSig.commutes a b := by
    intro a b
    exact (AbstractMRDT.ofQuery_commutes QuerySpec.abstraction a b).trans
      (QuerySpec.commutes_iff_concrete a b)
  have ordered : respects π (AbstractMRDT.order (model (α := α)) (conflict α) C E) := by
    apply hr.imp
    intro a b h edge
    apply h
    apply (paperOrder_iff_loOn restrictedLaws C E b a).mp
    simpa only [AbstractMRDT.order,paperOrder,commutation] using edge
  have metadata : respects π (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).before := by
    apply hr.imp
    intro a b h edge
    exact h ((paperOrder_iff_loOn restrictedLaws C E b a).mp (Or.inl edge))
  exact AbstractMRDT.joint_maximal_of_enumeration π hp nonempty ordered metadata

end Sal.MRDTs.Paper1.ORSet.AbstractSpec
