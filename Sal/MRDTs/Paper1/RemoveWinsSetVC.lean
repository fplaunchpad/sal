import Sal.MRDTs.Paper1.RemoveWinsSetReplay
import Sal.MRDTs.Paper1.ConcreteORSetAlgebra

/-! The five raw equations for Neem's removal-tag survivor merge. Initial
zero tags are handled separately from event-born tags; no Join is assumed. -/
namespace Sal.MRDTs.Paper1.RemoveWinsSet
open Foundation Instances.RemoveWinsSet
open Classical
variable {α : Type} [DecidableEq α] [Fintype α]
noncomputable local instance : EventOrder (D α).toUpdateSig := (conflict α).lift

private theorem represented_tags (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (s : State α) (h : representation C E s)
    (p : α × Timestamp) : p ∈ s ↔ Tags C E p := by
  apply canonical_mem_iff
  have hc : @IsCanonicalState (D α).toUpdateSig (conflict α).lift C E s := h.1
  rw [conflict_lift_eq] at hc
  exact hc

private theorem seed_mono {C : ReplayContext (D α).toUpdateSig}
    {A B : Set (Op (Update α))} (sub : A ⊆ B) {p : α × Timestamp}
    (h : Seed C B p) : Seed C A p := ⟨h.1,fun e he => h.2 e (sub he)⟩

private theorem birth_positive {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} (sup : ConcreteMRDT.Supported C E) (pos : Positive C)
    {p : α × Timestamp} (h : Live C E p) : 0 < p.2 := by
  obtain ⟨a,ha,_,ht,_⟩ := h
  exact ht ▸ pos a (sup a ha)

private theorem tags_zero {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} (sup : ConcreteMRDT.Supported C E) (pos : Positive C)
    {p : α × Timestamp} (zero : p.2 = 0) (h : Tags C E p) : Seed C E p := by
  rcases h with seed | live
  · exact seed
  · have impossible := birth_positive sup pos live
    exact False.elim (Nat.not_lt_zero _ (zero ▸ impossible))

private theorem tags_nonzero {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Op (Update α))} {p : α × Timestamp} (nonzero : p.2 ≠ 0)
    (h : Tags C E p) : Live C E p := h.resolve_left (fun seed => nonzero seed.1)

private theorem cleared_before (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (e a : Op (Update α)) (x : α)
    (remove : e.op = .add x) (add : a.op = .remove x)
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
  have killed : z.op = .add x := by
    rcases policy with ⟨y,impossible,_⟩ | ⟨y,rem,elem⟩
    · rw [add] at impossible; cases impossible
    · rw [add] at elem; cases elem; exact rem
  exact alive ⟨z,⟨hz,fun equal => backward (equal ▸ vis)⟩,vis,killed⟩

/-- A maximal Add clears seed tags and all causally prior live Rem tags. -/
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
  rcases e with ⟨et,er,op⟩
  cases op with
  | remove x =>
    have fresh : (x,et) ∉ B := by
      intro mem
      have tags := (represented_tags C _ B past (x,et)).mp mem
      have positive : 0 < et := past.2.2 _ (supported _ member)
      have live := tags_nonzero (Nat.ne_of_gt positive) tags
      obtain ⟨a,ha,_,time,_⟩ := live
      have equal : a = (et,er,Update.remove x) := C.ts_unique
        (supported a (pastSub ha.1)) (supported _ member) time
      exact ha.2 equal
    apply Finset.ext
    intro p
    have notOld : p = (x,et) → p ∉ B := fun equal => equal ▸ fresh
    simp only [merge,step,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_insert]
    tauto
  | add x =>
    have covered : ∀ p : α × Timestamp, p ∈ A → p.1 = x → p ∈ B := by
      intro p mem elem
      rcases (represented_tags C _ A pre p).mp mem with seed | birth
      · apply (represented_tags C _ B past p).mpr
        exact Or.inl (seed_mono (A := M.Past (et,er,.add x) \ {(et,er,.add x)})
          (B := U \ {(et,er,.add x)}) (fun z hz => ⟨pastSub hz.1,hz.2⟩) seed)
      · obtain ⟨a,ha,add,time,alive⟩ := birth
        have vis := cleared_before C U (et,er,.add x) a x rfl
          (by simpa only [Op.op,elem] using add) ha (by simpa only [elem] using alive) maximal
        have nc : ¬ (D α).toUpdateSig.commutes a (et,er,.add x) :=
          (restrictedLaws.noncomm_exact a (et,er,.add x)).mpr
            (Or.inr ⟨x,rfl,by simpa only [Op.op,elem] using add⟩)
        apply (represented_tags C _ B past p).mpr
        refine Or.inr ⟨a,⟨Or.inr (.single ⟨vis,nc⟩),ha.2⟩,add,time,?_⟩
        rintro ⟨r,hr,visibility,remove⟩
        exact alive ⟨r,⟨pastSub hr.1,hr.2⟩,visibility,remove⟩
    apply Finset.ext
    intro p
    have coverage := covered p
    simp only [merge,step,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_filter]
    tauto

/-- Common live tags and fresh newborn tags discharge redistribution. -/
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
  apply SetMergeAlgebra.local_redistribute
  · intro p inPast _ inOther
    have pastTags := (represented_tags C _ B past p).mp inPast
    have otherTags := (represented_tags C _ s other p).mp inOther
    apply (represented_tags C _ l base p).mpr
    rcases pastTags with seed | birth
    · have otherSeed := tags_zero sup₂ other.2.2 seed.1 otherTags
      exact Or.inl (seed_mono Set.inter_subset_right otherSeed)
    · have positive := birth_positive past.2.1 past.2.2 birth
      obtain ⟨a,ha,add,time,_⟩ := birth
      have ha₁ := pastSub ha.1
      have otherBirth := tags_nonzero (Nat.ne_of_gt positive) otherTags
      have hs := (live_iff_fixed_remove (C := C) (p := p) (a := a)
        sup₂ (sup₁ a ha₁) add time).mp otherBirth
      refine Or.inr ⟨a,⟨ha₁,hs.1⟩,add,time,?_⟩
      rintro ⟨r,hr,vis,remove⟩
      exact hs.2 ⟨r,hr.2,vis,remove⟩
  · intro p notPast newRecord inBase
    rcases e with ⟨et,er,op⟩
    cases op with
    | add x => exact notPast ((mem_step B (et,er,.add x) p).mp newRecord).1
    | remove x =>
      have generated : p = (x,et) :=
        ((mem_step B (et,er,.remove x) p).mp newRecord).resolve_right notPast
      have positive : 0 < p.2 := generated ▸ base.2.2 _ (sup₁ _ member)
      have tags := (represented_tags C _ l base p).mp inBase
      obtain ⟨a,ha,add,time,_⟩ := tags_nonzero (Nat.ne_of_gt positive) tags
      have same : a = (et,er,Update.remove x) := C.ts_unique (sup₁ a ha.1)
        (sup₁ _ member) (time.trans (congrArg Prod.snd generated))
      exact absent (same ▸ ha.2)

private theorem shared_equation (t₀ t₁ t₂ B d : State α) :
    merge (merge B t₀ d) (merge B t₁ d) (merge B t₂ d) =
      merge B (merge t₀ t₁ t₂) d := by
  apply Finset.ext
  intro p
  by_cases base : p ∈ B <;> by_cases delta : p ∈ d
  all_goals simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,base,delta,
    and_true,true_and,false_and,and_false,false_or,or_false,or_true,
    not_true_eq_false,not_false_eq_true]

theorem fiveVC : ConcreteMRDT.Raw.MergeVCs (conflict α)
    representation (scheme (α := α)) := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    change merge l a b = merge l b a
    ext p; simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]; tauto
  · intro C E s _ _ _
    change merge (initial α) (initial α) s = s
    ext p; simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]; tauto
  · intro C U s B e _ _ sup closed member semantic _ hs hB _ _
    exact causal_equation C U s B e member sup closed semantic hs hB
  · intro C E₁ E₂ l B t b e ctx member absent hl hB _ hb _ _ _
    exact local_equation C E₁ E₂ l B t b e member absent ctx.supported₁ ctx.supported₂ ctx.closed₁ hl hB hb
  · intro C E₁ E₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _
    exact shared_equation t₀ t₁ t₂ B (step B e)

theorem representationJoin : ConcreteMRDT.RepresentationJoin (representation (α := α)) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs fiveVC unique
    (fun C E s h => initial_rep C h.2.2) finite
  intro C _ _ _ _ trans irr _ _ ha _
  exact replaySupply C ha.2.2 trans irr

#print axioms fiveVC
#print axioms representationJoin
end Sal.MRDTs.Paper1.RemoveWinsSet
