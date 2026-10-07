import Sal.MRDTs.Paper1.EfficientMetadataReconstruction
import Sal.MRDTs.Paper1.MetadataRewrite

namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

/-- Concrete set algebra needs only coverage of records killed by the step.
No ancestor/branch Join theorem is used. -/
theorem merge_update_eq (a b : State α) (e : Event α)
    (fresh : ∀ p : Record α, e = (p.2.1,p.1,SetOp.add p.2.2) → p ∉ b)
    (covered : ∀ p : Record α, p ∈ a → kills p.1 p.2.2 e → p ∈ b) :
    merge b a (update b e) = update a e := by
  apply Finset.ext
  intro p
  have hf := fresh p
  have hc := covered p
  simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,mem_update_iff]
  tauto

theorem causal_replay_eq (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (a b : State α) (e : Event α)
    (member : e ∈ U) (supported : AbstractMRDT.Supported C U)
    (closed : (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Closed U)
    (semantic : ∀ x ∈ U, x ≠ e →
      ¬ AbstractMRDT.order (model (α := α)) (EventSpec.conflict α) C U e x)
    (metadata : ∀ x ∈ U, x ≠ e →
      ¬ (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).before e x)
    (ha : Represents C.vis (U \ {e}) a)
    (hb : Represents C.vis
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past e \ {e}) b) :
    merge b a (update b e) = update a e := by
  let M := AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C
  have pastSub := M.past_subset U e closed member
  apply merge_update_eq a b e
  · intro p birth mem
    have history := (hb p).mp mem
    exact history.1.2 birth.symm
  · intro p mem kill
    have living := (ha p).mp mem
    have vis := live_killed_before C U e member supported semantic metadata p living kill
    have dependency : M.before (p.2.1,p.1,SetOp.add p.2.2) e :=
      ⟨vis,kills_noncomm p e kill living.1.2⟩
    apply (hb p).mpr
    refine ⟨⟨Or.inr (.single dependency),living.1.2⟩,?_⟩
    intro deadPast
    have subset : M.Past e \ {e} ⊆ U \ {e} := fun x hx => ⟨pastSub hx.1,hx.2⟩
    exact living.2 (dead_mono C.vis subset deadPast)

theorem causalMetadata : AbstractMRDT.CausalMetadata (model (α := α))
    (EventSpec.conflict α) representation
    (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  intro C U a b e _ _ supported closed member semantic metadata ha hb target
  have equation := causal_replay_eq C U a b e member supported closed semantic metadata ha.2.1 hb.2.1
  change representation C U (merge b a (update b e))
  rw [equation]
  exact target

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
