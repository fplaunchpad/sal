import Sal.MRDTs.Paper1.ORSetRedistribution

/-! Local redistribution uses two membership facts: a record in the causal
base and the other branch belongs to the intersection, and a newly created
record cannot already belong to that intersection. Neither fact uses Join. -/
namespace Sal.MRDTs.Paper1
open Foundation
open Classical

namespace SetMergeAlgebra
def merge {β : Type} [DecidableEq β] (l a b : Finset β) : Finset β :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

theorem local_redistribute {β : Type} [DecidableEq β] (l B t s d : Finset β)
    (common : ∀ p, p ∈ B → p ∉ d → p ∈ s → p ∈ l)
    (newborn : ∀ p, p ∉ B → p ∈ d → p ∉ l) :
    merge l (merge B t d) s = merge B (merge l t s) d := by
  apply Finset.ext
  intro p
  have commonP := common p
  have newbornP := newborn p
  by_cases base : p ∈ B <;> by_cases delta : p ∈ d
  all_goals
    simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,base,delta,
      and_true,true_and,false_and,and_false,false_or,or_false,or_true,
      not_true_eq_false,not_false_eq_true] <;> tauto
end SetMergeAlgebra

namespace EfficientORSet.AbstractSpec
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem local_replay_eq (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Event α)) (l B t s : State α) (e : Event α)
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (closed : (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Closed E₁)
    (base : Represents C.vis (E₁ ∩ E₂) l)
    (past : Represents C.vis
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past e \ {e}) B)
    (other : Represents C.vis E₂ s) :
    merge l (merge B t (update B e)) s = merge B (merge l t s) (update B e) := by
  have pastSub := (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).past_subset
    E₁ e closed member
  apply SetMergeAlgebra.local_redistribute
  · intro p inPast _ inOther
    have hp := (past p).mp inPast
    have hs := (other p).mp inOther
    apply (base p).mpr
    refine ⟨⟨pastSub hp.1.1,hs.1⟩,?_⟩
    intro killed
    exact hs.2 (dead_mono C.vis Set.inter_subset_right killed)
  · intro p notPast newRecord inBase
    have birth : e = (p.2.1,p.1,SetOp.add p.2.2) := by
      rcases (mem_update_iff p B e).mp newRecord with birth | old
      · exact birth
      · exact False.elim (notPast old.1)
    exact absent (birth.symm ▸ ((base p).mp inBase).1.2)

theorem localMetadata : AbstractMRDT.LocalMetadata (model (α := α)) (EventSpec.conflict α)
    representation (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  intro C E₁ E₂ l B t s e ctx member absent base past _ other target
  have equation := local_replay_eq C E₁ E₂ l B t s e member absent ctx.closed₁
    base.2.1 past.2.1 other.2.1
  change representation C (E₁ ∪ E₂) (merge l (merge B t (update B e)) s)
  rw [equation]
  exact target

end EfficientORSet.AbstractSpec

namespace ORSet.AbstractSpec
variable {α : Type} [DecidableEq α]

theorem local_replay_eq (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Op (Update α))) (l B t s : State α) (e : Op (Update α))
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (sup₁ : AbstractMRDT.Supported C E₁) (sup₂ : AbstractMRDT.Supported C E₂)
    (closed : (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Closed E₁)
    (base : representation C (E₁ ∩ E₂) l)
    (past : representation C
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past e \ {e}) B)
    (other : representation C E₂ s) :
    merge l (merge B t (step B e)) s = merge B (merge l t s) (step B e) := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  have pastSub := (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).past_subset
    E₁ e closed member
  have rawBase : @IsCanonicalState (D α).toUpdateSig policy C (E₁ ∩ E₂) l := by
    simpa only [representation,conflict_lift_eq] using base
  have rawPast : @IsCanonicalState (D α).toUpdateSig policy C
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past e \ {e}) B := by
    simpa only [representation,conflict_lift_eq] using past
  have rawOther : @IsCanonicalState (D α).toUpdateSig policy C E₂ s := by
    simpa only [representation,conflict_lift_eq] using other
  apply SetMergeAlgebra.local_redistribute
  · intro p inPast _ inOther
    obtain ⟨a,ha,add,time,_⟩ := (canonical_mem_iff rawPast p).mp inPast
    have ha₁ := pastSub ha.1
    have hs := (live_iff_fixed_add (C := C) (p := p) (a := a)
      sup₂ (sup₁ a ha₁) add time).mp ((canonical_mem_iff rawOther p).mp inOther)
    apply (canonical_mem_iff rawBase p).mpr
    refine ⟨a,⟨ha₁,hs.1⟩,add,time,?_⟩
    rintro ⟨r,hr,vis,remove⟩
    exact hs.2 ⟨r,hr.2,vis,remove⟩
  · intro p notPast newRecord inBase
    obtain ⟨a,ha,add,time,_⟩ := (canonical_mem_iff rawBase p).mp inBase
    rcases e with ⟨et,er,op⟩
    cases op with
    | remove x =>
      have old := (mem_step B (et,er,.remove x) p).mp newRecord
      exact notPast old.1
    | add x =>
      have generated : p = (x,et) := by
        exact ((mem_step B (et,er,.add x) p).mp newRecord).resolve_right notPast
      have same : a = (et,er,Update.add x) := C.ts_unique (sup₁ a ha.1)
        (sup₁ _ member) (time.trans (congrArg Prod.snd generated))
      exact absent (same ▸ ha.2)

theorem localMetadata : AbstractMRDT.LocalMetadata (model (α := α)) (conflict α)
    representation (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  intro C E₁ E₂ l B t s e ctx member absent base past _ other target
  have equation := local_replay_eq C E₁ E₂ l B t s e member absent ctx.supported₁ ctx.supported₂
    ctx.closed₁ base.2 past.2 other.2
  change representation C (E₁ ∪ E₂) (merge l (merge B t (step B e)) s)
  rw [equation]
  exact target

end ORSet.AbstractSpec
end Sal.MRDTs.Paper1
