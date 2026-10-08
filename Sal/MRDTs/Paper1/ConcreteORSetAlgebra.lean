import Sal.MRDTs.Paper1.ConcreteORSetRepresentation

namespace Sal.MRDTs.Paper1
open Foundation

private def setMerge {β : Type} [DecidableEq β] (l a b : Finset β) : Finset β :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

private theorem setMerge_shared {β : Type} [DecidableEq β]
    (t₀ t₁ t₂ B d : Finset β) :
    setMerge (setMerge B t₀ d) (setMerge B t₁ d) (setMerge B t₂ d) =
      setMerge B (setMerge t₀ t₁ t₂) d := by
  apply Finset.ext
  intro p
  by_cases base : p ∈ B <;> by_cases delta : p ∈ d
  all_goals
    simp only [setMerge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,base,delta,
      and_true,true_and,false_and,and_false,false_or,or_false,or_true,
      not_true_eq_false,not_false_eq_true]

namespace ORSet.ConcreteRep
variable {α : Type} [DecidableEq α]

theorem shared_replay_eq (t₀ t₁ t₂ B : (D α).State) (e : Op (Update α)) :
    (D α).merge ((D α).merge B t₀ ((D α).update B e))
      ((D α).merge B t₁ ((D α).update B e))
      ((D α).merge B t₂ ((D α).update B e)) =
    (D α).merge B ((D α).merge t₀ t₁ t₂) ((D α).update B e) :=
  setMerge_shared t₀ t₁ t₂ B ((D α).update B e)

end ORSet.ConcreteRep

namespace EfficientORSet.ConcreteRep
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem shared_replay_eq (t₀ t₁ t₂ B : (D α).State) (e : Event α) :
    (D α).merge ((D α).merge B t₀ ((D α).update B e))
      ((D α).merge B t₁ ((D α).update B e))
      ((D α).merge B t₂ ((D α).update B e)) =
    (D α).merge B ((D α).merge t₀ t₁ t₂) ((D α).update B e) :=
  setMerge_shared t₀ t₁ t₂ B ((D α).update B e)

end EfficientORSet.ConcreteRep
end Sal.MRDTs.Paper1

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

namespace EfficientORSet.ConcreteRep
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem local_replay_eq (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Event α)) (l B t s : State α) (e : Event α)
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed E₁)
    (base : Represents C.vis (E₁ ∩ E₂) l)
    (past : Represents C.vis
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past e \ {e}) B)
    (other : Represents C.vis E₂ s) :
    merge l (merge B t (update B e)) s = merge B (merge l t s) (update B e) := by
  have pastSub := (ConcreteMRDT.MetadataDependencies.ofConcrete C).past_subset
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

end EfficientORSet.ConcreteRep

namespace ORSet.ConcreteRep
variable {α : Type} [DecidableEq α]

theorem local_replay_eq (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Op (Update α))) (l B t s : State α) (e : Op (Update α))
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (sup₁ : ConcreteMRDT.Supported C E₁) (sup₂ : ConcreteMRDT.Supported C E₂)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed E₁)
    (base : representation C (E₁ ∩ E₂) l)
    (past : representation C
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past e \ {e}) B)
    (other : representation C E₂ s) :
    merge l (merge B t (step B e)) s = merge B (merge l t s) (step B e) := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  have pastSub := (ConcreteMRDT.MetadataDependencies.ofConcrete C).past_subset
    E₁ e closed member
  have rawBase : @IsCanonicalState (D α).toUpdateSig policy C (E₁ ∩ E₂) l := by
    simpa only [representation,conflict_lift_eq] using base
  have rawPast : @IsCanonicalState (D α).toUpdateSig policy C
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past e \ {e}) B := by
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

end ORSet.ConcreteRep
end Sal.MRDTs.Paper1

namespace Sal.MRDTs.Paper1.ORSet.ConcreteRep
open Foundation
open Classical
variable {α : Type} [DecidableEq α]

private theorem removed_before (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (e a : Op (Update α)) (x : α)
    (remove : e.op = .remove x) (add : a.op = .add x)
    (member : a ∈ U \ {e}) (alive : Survives C (U \ {e}) a x)
    (maximal : ∀ z ∈ U, z ≠ e → ¬ paperOrder (conflict α) C U e z) :
    C.vis a e := by
  have noncomm : ¬ (D α).toUpdateSig.commutes e a :=
    (restrictedLaws.noncomm_exact e a).mpr (Or.inl ⟨x,remove,add⟩)
  have forward : ¬ C.vis e a := fun vis => maximal a member.1 member.2 (Or.inl ⟨vis,noncomm⟩)
  by_contra backward
  apply maximal a member.1 member.2
  refine Or.inr ⟨forward,backward,⟨x,remove,add⟩,?_⟩
  rintro ⟨z,hz,vis,nc⟩
  have policy := (restrictedLaws.noncomm_exact a z).mp nc
  have killed : z.op = .remove x := by
    rcases policy with ⟨y,impossible,_⟩ | ⟨y,rem,elem⟩
    · rw [add] at impossible
      cases impossible
    · rw [add] at elem
      cases elem
      exact rem
  exact alive ⟨z,⟨hz,fun equal => backward (equal ▸ vis)⟩,vis,killed⟩

/-- The exact-set causal equation is established by individual tag survival,
without invoking representation Join. -/
theorem causal_replay_eq (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (A B : State α) (e : Op (Update α))
    (member : e ∈ U) (supported : ConcreteMRDT.Supported C U)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed U)
    (maximal : ∀ z ∈ U, z ≠ e → ¬ paperOrder (conflict α) C U e z)
    (pre : representation C (U \ {e}) A)
    (past : representation C
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past e \ {e}) B) :
    merge B A (step B e) = step A e := by
  have rawPre : @IsCanonicalState (D α).toUpdateSig policy C (U \ {e}) A := by
    simpa only [representation,conflict_lift_eq] using pre
  have rawPast : @IsCanonicalState (D α).toUpdateSig policy C
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past e \ {e}) B := by
    simpa only [representation,conflict_lift_eq] using past
  let M := ConcreteMRDT.MetadataDependencies.ofConcrete C
  have pastSub := M.past_subset U e closed member
  rcases e with ⟨et,er,op⟩
  cases op with
  | add x =>
    have fresh : (x,et) ∉ B := by
      intro mem
      obtain ⟨a,ha,_,time,_⟩ := (canonical_mem_iff rawPast (x,et)).mp mem
      have equal : a = (et,er,Update.add x) := C.ts_unique
        (supported a (pastSub ha.1)) (supported _ member) time
      exact ha.2 equal
    apply Finset.ext
    intro p
    have notOld : p = (x,et) → p ∉ B := fun equal => equal ▸ fresh
    simp only [merge,step,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_insert]
    tauto
  | remove x =>
    have covered : ∀ p : α × Timestamp, p ∈ A → p.1 = x → p ∈ B := by
      intro p mem elem
      obtain ⟨a,ha,add,time,alive⟩ := (canonical_mem_iff rawPre p).mp mem
      have vis := removed_before C U (et,er,.remove x) a x rfl
        (by simpa only [Op.op,elem] using add) ha (by simpa only [elem] using alive) maximal
      have nc : ¬ (D α).toUpdateSig.commutes a (et,er,.remove x) :=
        (noncomm_iff_rc a (et,er,.remove x)).mpr
          (Or.inr ((rc_iff (et,er,.remove x) a).mpr ⟨x,rfl,by simpa [elem] using add⟩))
      apply (canonical_mem_iff rawPast p).mpr
      refine ⟨a,⟨Or.inr (.single ⟨vis,nc⟩),ha.2⟩,add,time,?_⟩
      rintro ⟨r,hr,visibility,remove⟩
      exact alive ⟨r,⟨pastSub hr.1,hr.2⟩,visibility,remove⟩
    apply Finset.ext
    intro p
    have coverage := covered p
    simp only [merge,step,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_filter]
    tauto

end Sal.MRDTs.Paper1.ORSet.ConcreteRep

namespace Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep
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


end Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep
