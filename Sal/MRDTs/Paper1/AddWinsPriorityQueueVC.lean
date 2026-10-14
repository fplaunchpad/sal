import Sal.MRDTs.Paper1.AddWinsPriorityQueueReplay
import Sal.MRDTs.Paper1.ConcreteORSetAlgebra

/-! The five equations, proved from individual Add survival and immutable
increments. The common finite event-set induction derives Join afterward. -/
namespace Sal.MRDTs.Paper1.AddWinsPriorityQueue
open Foundation Instances.AddWinsPriorityQueue
open Classical
variable {α : Type} [DecidableEq α]
noncomputable local instance : EventOrder (D α).toUpdateSig := (conflict α).lift

private theorem represented_adds (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (s : State α) (h : representation C E s)
    (p : AddRecord α) : p ∈ s.1 ↔ Live C E p := by
  apply canonical_mem_iff
  have hc : @IsCanonicalState (D α).toUpdateSig (conflict α).lift C E s := h.1
  rw [conflict_lift_eq] at hc
  exact hc

private theorem represented_incs (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (s : State α) (h : representation C E s)
    (p : IncRecord α) : p ∈ s.2 ↔ IncLive E p := by
  apply canonical_incs
  have hc : @IsCanonicalState (D α).toUpdateSig (conflict α).lift C E s := h.1
  rw [conflict_lift_eq] at hc
  exact hc

private theorem removed_before (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (e a : Op (Update α)) (x : α) (v : Nat)
    (remove : e.op = .remove x) (add : a.op = .add x v)
    (member : a ∈ U \ {e}) (alive : Survives C (U \ {e}) a x)
    (maximal : ∀ z ∈ U, z ≠ e → ¬ paperOrder (conflict α) C U e z) :
    C.vis a e := by
  have noncomm : ¬ (D α).toUpdateSig.commutes e a :=
    (restrictedLaws.noncomm_exact e a).mpr (Or.inl ⟨x,v,remove,add⟩)
  have forward : ¬ C.vis e a := fun vis => maximal a member.1 member.2 (Or.inl ⟨vis,noncomm⟩)
  by_contra backward
  apply maximal a member.1 member.2
  refine Or.inr ⟨forward,backward,⟨x,v,remove,add⟩,?_⟩
  rintro ⟨z,hz,vis,nc⟩
  have pol := (restrictedLaws.noncomm_exact a z).mp nc
  have killed : z.op = .remove x := by
    rcases pol with ⟨y,w,impossible,_⟩ | ⟨y,w,rem,elem⟩
    · rw [add] at impossible; cases impossible
    · rw [add] at elem; cases elem; exact rem
  exact alive ⟨z,⟨hz,fun equal => backward (equal ▸ vis)⟩,vis,killed⟩

theorem causal_equation (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (A B : State α) (e : Op (Update α))
    (member : e ∈ U) (supported : ConcreteMRDT.Supported C U)
    (closed : (scheme C).Closed U)
    (maximal : ∀ z ∈ U, z ≠ e → ¬ paperOrder (conflict α) C U e z)
    (pre : representation C (U \ {e}) A)
    (past : representation C ((scheme C).Past e \ {e}) B) :
    merge B A (step B e) = step A e := by
  let M := scheme C
  have pastSub : M.Past e ⊆ U := M.past_subset U e closed member
  have incSub : B.2 ⊆ A.2 := by
    intro p hp
    obtain ⟨a,ha,inc,time⟩ := (represented_incs C _ B past p).mp hp
    exact (represented_incs C _ A pre p).mpr ⟨a,⟨pastSub ha.1,ha.2⟩,inc,time⟩
  rcases e with ⟨et,er,op⟩
  cases op with
  | add x v =>
    have fresh : (x,et,v) ∉ B.1 := by
      intro mem
      obtain ⟨a,ha,_,time,_⟩ := (represented_adds C _ B past (x,et,v)).mp mem
      have equal : a = (et,er,Update.add x v) := C.ts_unique
        (supported a (pastSub ha.1)) (supported _ member) time
      exact ha.2 equal
    apply Prod.ext
    · ext p
      have notOld : p = (x,et,v) → p ∉ B.1 := fun equal => equal ▸ fresh
      simp only [merge,step,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_insert]
      tauto
    · simpa only [merge,step] using Finset.union_eq_left.mpr incSub
  | inc x n =>
    apply Prod.ext
    · ext p
      simp only [merge,step,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      tauto
    · ext p
      have sub := incSub
      simp only [merge,step,Finset.mem_union,Finset.mem_insert]
      have subP : p ∈ B.2 → p ∈ A.2 := fun h => incSub h
      tauto
  | remove x =>
    have covered : ∀ p : AddRecord α, p ∈ A.1 → p.1 = x → p ∈ B.1 := by
      intro p mem elem
      obtain ⟨a,ha,add,time,alive⟩ := (represented_adds C _ A pre p).mp mem
      have vis := removed_before C U (et,er,.remove x) a x p.2.2 rfl
        (by simpa only [Op.op,elem] using add) ha (by simpa only [elem] using alive) maximal
      have nc : ¬ (D α).toUpdateSig.commutes a (et,er,.remove x) :=
        (restrictedLaws.noncomm_exact a (et,er,.remove x)).mpr
          (Or.inr ⟨x,p.2.2,rfl,by simpa only [Op.op,elem] using add⟩)
      apply (represented_adds C _ B past p).mpr
      refine ⟨a,⟨Or.inr (.single ⟨vis,nc⟩),ha.2⟩,add,time,?_⟩
      rintro ⟨r,hr,visibility,remove⟩
      exact alive ⟨r,⟨pastSub hr.1,hr.2⟩,visibility,remove⟩
    apply Prod.ext
    · ext p
      have coverage := covered p
      simp only [merge,step,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_filter]
      tauto
    · simpa only [merge,step] using Finset.union_eq_left.mpr incSub

/-- Raw local redistribution requires only common old Add records and fresh
newborn timestamps. Increment union redistributes unconditionally. -/
theorem local_equation (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Op (Update α))) (l B t s : State α) (e : Op (Update α))
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (sup₁ : ConcreteMRDT.Supported C E₁) (sup₂ : ConcreteMRDT.Supported C E₂)
    (closed : (scheme C).Closed E₁)
    (base : representation C (E₁ ∩ E₂) l)
    (past : representation C ((scheme C).Past e \ {e}) B)
    (other : representation C E₂ s) :
    merge l (merge B t (step B e)) s = merge B (merge l t s) (step B e) := by
  have pastSub := (scheme C).past_subset E₁ e closed member
  apply Prod.ext
  · apply SetMergeAlgebra.local_redistribute
    · intro p inPast _ inOther
      obtain ⟨a,ha,add,time,_⟩ := (represented_adds C _ B past p).mp inPast
      have ha₁ := pastSub ha.1
      have hs := (live_iff_fixed_add (C := C) (p := p) (a := a)
        sup₂ (sup₁ a ha₁) add time).mp ((represented_adds C _ s other p).mp inOther)
      apply (represented_adds C _ l base p).mpr
      refine ⟨a,⟨ha₁,hs.1⟩,add,time,?_⟩
      rintro ⟨r,hr,vis,remove⟩
      exact hs.2 ⟨r,hr.2,vis,remove⟩
    · intro p notPast newRecord inBase
      obtain ⟨a,ha,add,time,_⟩ := (represented_adds C _ l base p).mp inBase
      rcases e with ⟨et,er,op⟩
      cases op with
      | remove x => exact notPast ((mem_step_adds B (et,er,.remove x) p).mp newRecord).1
      | inc x n => exact notPast ((mem_step_adds B (et,er,.inc x n) p).mp newRecord)
      | add x v =>
        have generated : p = (x,et,v) :=
          ((mem_step_adds B (et,er,.add x v) p).mp newRecord).resolve_right notPast
        have same : a = (et,er,Update.add x v) := C.ts_unique (sup₁ a ha.1)
          (sup₁ _ member) (time.trans (congrArg (fun p : AddRecord α => p.2.1) generated))
        exact absent (same ▸ ha.2)
  · ext p
    simp only [merge,Finset.mem_union]
    tauto

private theorem shared_equation (t₀ t₁ t₂ B d : State α) :
    merge (merge B t₀ d) (merge B t₁ d) (merge B t₂ d) =
      merge B (merge t₀ t₁ t₂) d := by
  apply Prod.ext
  · ext p
    by_cases base : p ∈ B.1 <;> by_cases delta : p ∈ d.1
    all_goals simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,base,delta,
      and_true,true_and,false_and,and_false,false_or,or_false,or_true,
      not_true_eq_false,not_false_eq_true]
  · ext p; simp only [merge,Finset.mem_union]; tauto

theorem fiveVC : ConcreteMRDT.Raw.MergeVCs (conflict α)
    representation (scheme (α := α)) := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    change merge l a b = merge l b a
    apply Prod.ext <;> ext p <;>
      simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff] <;> tauto
  · intro C E s _ _ _
    change merge (∅,∅) (∅,∅) s = s
    simp [merge]
  · intro C U s B e _ _ sup closed member semantic _ hs hB _ _
    exact causal_equation C U s B e member sup closed semantic hs hB
  · intro C E₁ E₂ l B t b e ctx member absent hl hB _ hb _ _ _
    exact local_equation C E₁ E₂ l B t b e member absent ctx.supported₁ ctx.supported₂ ctx.closed₁ hl hB hb
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _
    exact shared_equation t₀ t₁ t₂ B (step B e)

theorem representationJoin : ConcreteMRDT.RepresentationJoin (representation (α := α)) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs fiveVC unique
    (fun C _ _ _ => initial_rep C) finite
  intro C _ _ _ _ trans irr _ _ _ _
  exact replaySupply C trans irr

#print axioms fiveVC
#print axioms representationJoin
end Sal.MRDTs.Paper1.AddWinsPriorityQueue
