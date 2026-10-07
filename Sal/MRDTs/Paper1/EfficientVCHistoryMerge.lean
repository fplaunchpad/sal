import Sal.MRDTs.Paper1.EfficientORSetVCJoin

namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]
local instance : ReplayPolicy (D α).toUpdateSig := rc

theorem version_enumerated {C : Configuration (D α)} (good : CanonicalConfig C)
    {v : Version} {s : State α} {E : Set (Event α)} (hv : C.ver v = some (s,E)) :
    ∃ π, listPermOf π E := by
  obtain ⟨π,hp,_,_⟩ := good.canonical v s E hv
  exact ⟨π,hp⟩

theorem union_enumerated {C : Configuration (D α)} (good : CanonicalConfig C)
    (S : Finset Version) (allocated : ∀ v ∈ S, (C.ver v).isSome) :
    ∃ π, listPermOf π (unionEvents C S) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨[],by simp [unionEvents_empty,listPermOf]⟩
  | @insert v S _ ih =>
    obtain ⟨⟨s,E⟩,hv⟩ := Option.isSome_iff_exists.mp (allocated v (by simp))
    obtain ⟨π,hp⟩ := version_enumerated good hv
    obtain ⟨xs,hxs⟩ := ih (fun w hw => allocated w (Finset.mem_insert_of_mem hw))
    have union : unionEvents C (insert v S) = E ∪ unionEvents C S := by
      rw [Finset.insert_eq,unionEvents_union,unionEvents_singleton hv]
    rw [union]
    exact ⟨_,listPermOf_union (D := (D α).toUpdateSig) hp hxs⟩

/-- Adapts the VC-derived represented Join to execution scratch states.
Enumeration and support remain explicit, including for virtual-base folds. -/
theorem vcHistoryMerge {C : Configuration (D α)} (good : CanonicalConfig C)
    (E₁ E₂ : Set (Event α)) (l a b : State α)
    (enum₁ : ∃ π, listPermOf π E₁) (enum₂ : ∃ π, listPermOf π E₂)
    (sup₁ : AbstractMRDT.Supported C.replayContext E₁)
    (sup₂ : AbstractMRDT.Supported C.replayContext E₂)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (base : Represents C.vis (E₁ ∩ E₂) l)
    (side₁ : Represents C.vis E₁ a) (side₂ : Represents C.vis E₂ b) :
    Represents C.vis (E₁ ∪ E₂) (merge l a b) := by
  obtain ⟨π,hp⟩ := enum₁
  obtain ⟨xs,hxs⟩ := enum₂
  obtain ⟨intersection,hint⟩ := AbstractMRDT.enumeration_subset hp Set.inter_subset_left
  have trans : Transitive C.vis := fun _ _ _ h k => good.vis_trans h k
  have mono : ∀ x y, C.vis x y → x.time < y.time := fun _ _ h => C.causal_mono h
  have result := vcRepresentationJoin C.replayContext E₁ E₂ l a b trans good.vis_irrefl sup₁ sup₂
    closed₁ closed₂
    ⟨base,⟨intersection,hint⟩,(fun x h => sup₁ x h.1),trans,mono⟩
    ⟨side₁,⟨π,hp⟩,sup₁,trans,mono⟩ ⟨side₂,⟨xs,hxs⟩,sup₂,trans,mono⟩
  exact result.1

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
