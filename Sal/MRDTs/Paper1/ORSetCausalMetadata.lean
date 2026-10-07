import Sal.MRDTs.Paper1.ORSetLocalMetadata

namespace Sal.MRDTs.Paper1.ORSet.AbstractSpec
open Foundation
open Classical
variable {α : Type} [DecidableEq α]

private theorem removed_before (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (e a : Op (Update α)) (x : α)
    (remove : e.op = .remove x) (add : a.op = .add x)
    (member : a ∈ U \ {e}) (alive : Survives C (U \ {e}) a x)
    (maximal : ∀ z ∈ U, z ≠ e → ¬ AbstractMRDT.order (model (α := α)) (conflict α) C U e z) :
    C.vis a e := by
  have noncomm : ¬ AbstractMRDT.Commutes (model (α := α)) e a :=
    (laws.noncomm_exact e a).mpr (Or.inl ⟨x,remove,add⟩)
  have forward : ¬ C.vis e a := fun vis => maximal a member.1 member.2 (Or.inl ⟨vis,noncomm⟩)
  by_contra backward
  apply maximal a member.1 member.2
  refine Or.inr ⟨forward,backward,⟨x,remove,add⟩,?_⟩
  rintro ⟨z,hz,vis,nc⟩
  have policy := (laws.noncomm_exact a z).mp nc
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
    (member : e ∈ U) (supported : AbstractMRDT.Supported C U)
    (closed : (AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Closed U)
    (maximal : ∀ z ∈ U, z ≠ e → ¬ AbstractMRDT.order (model (α := α)) (conflict α) C U e z)
    (pre : representation C (U \ {e}) A)
    (past : representation C
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past e \ {e}) B) :
    merge B A (step B e) = step A e := by
  have rawPre : @IsCanonicalState (D α).toUpdateSig policy C (U \ {e}) A := by
    simpa only [representation,conflict_lift_eq] using pre
  have rawPast : @IsCanonicalState (D α).toUpdateSig policy C
      ((AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C).Past e \ {e}) B := by
    simpa only [representation,conflict_lift_eq] using past
  let M := AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C
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

theorem causalMetadata : AbstractMRDT.CausalMetadata (model (α := α)) (conflict α)
    representation (fun C => AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C) := by
  intro C U A B e _ _ supported closed member maximal _ pre past target
  have equation := causal_replay_eq C U A B e member supported closed maximal pre.2 past.2
  change representation C U (merge B A (step B e))
  rw [equation]
  exact target

end Sal.MRDTs.Paper1.ORSet.AbstractSpec
