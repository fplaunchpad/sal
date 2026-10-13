import Sal.MRDTs.Paper1.NeemFlagEvent
import Sal.MRDTs.Paper1.EnableWinsFlagCausal
import Sal.MRDTs.Paper1.EnableWinsFlagReplay
import Sal.MRDTs.Paper1.EnableWinsFlagAlgebra
import Sal.MRDTs.Paper1.EnableWinsFlagCounts

namespace Sal.MRDTs.Paper1.NeemFlagVC
open Foundation ConcreteMRDT Instances.NeemFlag NeemFlagReplay NeemFlagCounts NeemFlagAlgebra
open Classical

variable {initialFlag : Bool}

private theorem finset_subset {F G : Finset (Op Action)} {A B : Set (Op Action)}
    (hF : (↑F : Set (Op Action)) = A) (hG : (↑G : Set (Op Action)) = B)
    (sub : A ⊆ B) : F ⊆ G := by
  intro e he
  have hx : e ∈ A := by rw [← hF]; exact he
  have hy := sub hx
  rw [← hG] at hy
  exact hy

theorem intersection_counts (C : ReplayContext (D initialFlag).toUpdateSig)
    (E₁ E₂ : Set (Op Action)) (l a b : State)
    (closed₁ : (scheme initialFlag C).Closed E₁)
    (closed₂ : (scheme initialFlag C).Closed E₂)
    (hl : representation initialFlag C (E₁ ∩ E₂) l)
    (ha : representation initialFlag C E₁ a) (hb : representation initialFlag C E₂ b) :
    ∀ r, (l r).1 = min (a r).1 (b r).1 := by
  obtain ⟨_,L,hL,cL,_⟩ := hl
  obtain ⟨sup₁,F,hF,cF,_⟩ := ha
  obtain ⟨sup₂,G,hG,cG,_⟩ := hb
  have same : L = F ∩ G := by
    apply Finset.coe_injective
    simp only [Finset.coe_inter,hF,hG,hL]
  subst L
  intro r
  rw [cL,cF,cG]
  exact count_min_of_comparable F G r
    (prefixes_comparable C E₁ E₂ F G hF hG sup₁ sup₂ closed₁ closed₂ r)

/-- Metadata retains commuting same-issuer winning predecessors. -/
theorem past_count_facts (C : ReplayContext (D initialFlag).toUpdateSig)
    (U : Set (Op Action)) (s B : State) (e : Op Action)
    (supported : Supported C U) (closed : (scheme initialFlag C).Closed U) (member : e ∈ U)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ (scheme initialFlag C).before e x)
    (hs : representation initialFlag C (U \ {e}) s)
    (hB : representation initialFlag C ((scheme initialFlag C).Past e \ {e}) B) :
    (∀ r, (B r).1 ≤ (s r).1) ∧ (s e.rep).1 = (B e.rep).1 := by
  obtain ⟨_,F,hF,cF,_⟩ := hs
  obtain ⟨_,G,hG,cG,_⟩ := hB
  have pastSub := (scheme initialFlag C).past_subset U e closed member
  have sub : G ⊆ F := finset_subset hG hF (fun x hx => ⟨pastSub hx.1,hx.2⟩)
  refine ⟨?_,?_⟩
  · intro r; rw [cG,cF]; exact count_mono G F sub r
  · rw [cF,cG]
    apply congrArg (fun A : Finset (Op Action) => (A.card : Int))
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxF,own⟩ := Finset.mem_filter.mp hx
      have hxU : x ∈ U \ {e} := by rw [← hF]; exact hxF
      obtain ⟨rx,Sx,hLx,hxS⟩ := supported x hxU.1
      obtain ⟨re,Se,hLe,heS⟩ := supported e member
      have same := own.1
      have ne : x ≠ e := hxU.2
      have vis := (C.vis_total_same_replica hLx hxS hLe heS ne same).resolve_right
        (maximal x hxU.1 ne)
      have hxG : x ∈ G := by
        change x ∈ (↑G : Set (Op Action))
        rw [hG]
        exact ⟨Or.inr (.single vis),hxU.2⟩
      exact Finset.mem_filter.mpr ⟨hxG,own⟩
    · exact Finset.filter_subset_filter _ sub

theorem past_min_counts (C : ReplayContext (D initialFlag).toUpdateSig)
    (U : Set (Op Action)) (s B : State) (e : Op Action)
    (supported : Supported C U) (closed : (scheme initialFlag C).Closed U) (member : e ∈ U)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ (scheme initialFlag C).before e x)
    (hs : representation initialFlag C (U \ {e}) s)
    (hB : representation initialFlag C ((scheme initialFlag C).Past e \ {e}) B) :
    ∀ r, (B r).1 = min (s r).1 ((update B e) r).1 := by
  obtain ⟨lower,same⟩ := past_count_facts C U s B e supported closed member maximal hs hB
  obtain ⟨ts,issuer,action⟩ := e
  intro r
  cases action
  all_goals simp only [update,Op.op,Op.rep] at *
  all_goals (try split_ifs) <;> simp_all <;> omega

theorem merge_join_represented (C : ReplayContext (D initialFlag).toUpdateSig)
    (E₁ E₂ : Set (Op Action)) (l a b : State)
    (closed₁ : (scheme initialFlag C).Closed E₁)
    (closed₂ : (scheme initialFlag C).Closed E₂)
    (hl : representation initialFlag C (E₁ ∩ E₂) l)
    (ha : representation initialFlag C E₁ a) (hb : representation initialFlag C E₂ b) :
    merge l a b = NeemFlagAlgebra.join a b :=
  source_as_join l a b (intersection_counts C E₁ E₂ l a b closed₁ closed₂ hl ha hb)

theorem local_equation (C : ReplayContext (D initialFlag).toUpdateSig)
    (E₁ E₂ : Set (Op Action)) (l B t b : State) (e : Op Action)
    (ctx : Raw.Context policy (scheme initialFlag) C E₁ E₂ e)
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (hl : representation initialFlag C (E₁ ∩ E₂) l)
    (hB : representation initialFlag C ((scheme initialFlag C).Past e \ {e}) B)
    (ht : representation initialFlag C (E₁ \ {e}) t)
    (hb : representation initialFlag C E₂ b)
    (_hc : representation initialFlag C ((scheme initialFlag C).Past e) (update B e))
    (ha : representation initialFlag C E₁ (merge B t (update B e)))
    (hm : representation initialFlag C ((E₁ ∪ E₂) \ {e}) (merge l t b)) :
    merge l (merge B t (update B e)) b = merge B (merge l t b) (update B e) := by
  have preClosed := (scheme initialFlag C).closed_diff_of_max (E₁ ∪ E₂) E₁ e
    Set.subset_union_left ctx.closed₁ ctx.metadata
  have eq : (E₁ \ {e}) ∩ E₂ = E₁ ∩ E₂ := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,fun same => absent (same ▸ h.2)⟩,h.2⟩
  have base : representation initialFlag C ((E₁ \ {e}) ∩ E₂) l := by rw [eq]; exact hl
  have outer := merge_join_represented C E₁ E₂ l _ b ctx.closed₁ ctx.closed₂ hl ha hb
  have inner := source_as_join B t (update B e)
    (past_min_counts C E₁ t B e ctx.supported₁ ctx.closed₁ member
      (fun x hx ne => ctx.metadata x (Or.inl hx) ne) ht hB)
  have middle := merge_join_represented C (E₁ \ {e}) E₂ l t b preClosed ctx.closed₂ base ht hb
  have right := source_as_join B (merge l t b) (update B e)
    (past_min_counts C (E₁ ∪ E₂) (merge l t b) B e
      (fun x hx => hx.elim (ctx.supported₁ x) (ctx.supported₂ x))
      (fun a b edge hx => hx.elim
        (fun hx => Or.inl (ctx.closed₁ a b edge hx))
        (fun hx => Or.inr (ctx.closed₂ a b edge hx)))
      (Or.inl member) ctx.metadata hm hB)
  rw [outer,inner,right,middle]
  exact join_local t b (update B e)

theorem shared_equation (C : ReplayContext (D initialFlag).toUpdateSig)
    (E₁ E₂ : Set (Op Action)) (t₀ t₁ t₂ B : State) (e : Op Action)
    (ctx : Raw.Context policy (scheme initialFlag) C E₁ E₂ e)
    (member₁ : e ∈ E₁) (member₂ : e ∈ E₂)
    (h₀ : representation initialFlag C ((E₁ ∩ E₂) \ {e}) t₀)
    (hB : representation initialFlag C ((scheme initialFlag C).Past e \ {e}) B)
    (h₁ : representation initialFlag C (E₁ \ {e}) t₁)
    (h₂ : representation initialFlag C (E₂ \ {e}) t₂)
    (_hc : representation initialFlag C ((scheme initialFlag C).Past e) (update B e))
    (ha₀ : representation initialFlag C (E₁ ∩ E₂) (merge B t₀ (update B e)))
    (ha₁ : representation initialFlag C E₁ (merge B t₁ (update B e)))
    (ha₂ : representation initialFlag C E₂ (merge B t₂ (update B e)))
    (hm : representation initialFlag C ((E₁ ∪ E₂) \ {e}) (merge t₀ t₁ t₂)) :
    merge (merge B t₀ (update B e)) (merge B t₁ (update B e))
      (merge B t₂ (update B e)) = merge B (merge t₀ t₁ t₂) (update B e) := by
  have pre₁ := (scheme initialFlag C).closed_diff_of_max (E₁ ∪ E₂) E₁ e
    Set.subset_union_left ctx.closed₁ ctx.metadata
  have pre₂ := (scheme initialFlag C).closed_diff_of_max (E₁ ∪ E₂) E₂ e
    Set.subset_union_right ctx.closed₂ ctx.metadata
  have eq : (E₁ \ {e}) ∩ (E₂ \ {e}) = (E₁ ∩ E₂) \ {e} := by ext x; simp; tauto
  have base : representation initialFlag C ((E₁ \ {e}) ∩ (E₂ \ {e})) t₀ := by
    rw [eq]; exact h₀
  have outer := merge_join_represented C E₁ E₂ _ _ _ ctx.closed₁ ctx.closed₂ ha₀ ha₁ ha₂
  have inner₁ := source_as_join B t₁ (update B e)
    (past_min_counts C E₁ t₁ B e ctx.supported₁ ctx.closed₁ member₁
      (fun x hx ne => ctx.metadata x (Or.inl hx) ne) h₁ hB)
  have inner₂ := source_as_join B t₂ (update B e)
    (past_min_counts C E₂ t₂ B e ctx.supported₂ ctx.closed₂ member₂
      (fun x hx ne => ctx.metadata x (Or.inr hx) ne) h₂ hB)
  have middle := merge_join_represented C (E₁ \ {e}) (E₂ \ {e}) t₀ t₁ t₂ pre₁ pre₂ base h₁ h₂
  have right := source_as_join B (merge t₀ t₁ t₂) (update B e)
    (past_min_counts C (E₁ ∪ E₂) (merge t₀ t₁ t₂) B e
      (fun x hx => hx.elim (ctx.supported₁ x) (ctx.supported₂ x))
      (fun a b edge hx => hx.elim
        (fun hx => Or.inl (ctx.closed₁ a b edge hx))
        (fun hx => Or.inr (ctx.closed₂ a b edge hx)))
      (Or.inl member₁) ctx.metadata hm hB)
  rw [outer,inner₁,inner₂,right,middle]
  exact join_shared t₁ t₂ (update B e)

theorem true_count_positive (C : ReplayContext (D false).toUpdateSig)
    (E : Set (Op Action)) (s : State) (h : representation false C E s)
    (r : Nat) (bit : (s r).2 = true) : 0 < (s r).1 := by
  obtain ⟨_,F,hF,cF,bF⟩ := h
  have living := (bF r).mp bit
  rcases living with ⟨w,hw,own,win,_⟩ | impossible
  · have hwF : w ∈ F := by rw [← hF] at hw; exact hw
    have hwW : w ∈ winners F r := Finset.mem_filter.mpr ⟨hwF,own,win⟩
    have positive := Finset.card_pos.mpr (show (winners F r).Nonempty from ⟨w,hwW⟩)
    rw [cF]
    unfold NeemFlagReplay.count NeemFlagCounts.count
    exact_mod_cast positive
  · simp at impossible

theorem initial_equation (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (E : Set (Op Action)) (s : State) (h : representation initialFlag C E s) :
    merge (initial initialFlag) (initial initialFlag) s = s := by
  funext r
  apply Prod.ext
  · simp [merge,mergeCell,initial]
  · cases initialFlag <;> cases hb : (s r).2
    all_goals simp [merge,mergeCell,mergeFlag,initial,hb]
    exact true_count_positive C E s h r hb

/-- The source merge's five equations follow from represented count-prefix
facts and live-winning/reset semantics. No final Join is assumed. -/
theorem fiveVC (initialFlag : Bool) :
    Raw.MergeVCs policy (representation initialFlag) (scheme initialFlag) := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    exact source_comm l a b
  · intro C E s _ _ h
    exact initial_equation initialFlag C E s h
  · intro C U s B e trans irr sup closed member semantic metadata hs hB _ _
    obtain ⟨lower,same⟩ := past_count_facts C U s B e sup closed member metadata hs hB
    exact NeemFlagCausal.causal_delta initialFlag C U s B e trans irr sup closed member
      semantic metadata hs hB lower same
  · exact local_equation
  · exact shared_equation

/-- The common metadata induction consumes all five source merge VCs. -/
theorem join (initialFlag : Bool) : RepresentationJoin (representation initialFlag) := by
  exact Raw.representationJoin_of_vcs (fiveVC initialFlag) (unique initialFlag)
    (fun C _ _ _ => initial_rep initialFlag C) (finite_rep initialFlag)
    (fun C _ _ _ _ trans irr _ _ _ _ => replaySupply initialFlag C trans irr)

/-- Context invariants are bundled for the unconditional canonical field of
VCReplayConditions. Real execution supplies both invariants independently. -/
def certifiedRepresentation (initialFlag : Bool) : Representation (D initialFlag) :=
  fun C E s => Transitive C.vis ∧ (∀ x, ¬ C.vis x x) ∧ representation initialFlag C E s

theorem certifiedFiveVC (initialFlag : Bool) :
    Raw.MergeVCs policy (certifiedRepresentation initialFlag) (scheme initialFlag) := by
  constructor
  · intro C E₁ E₂ l a b sup₁ sup₂ closed₁ closed₂ hl ha hb
    exact (fiveVC initialFlag).merge_comm C E₁ E₂ l a b sup₁ sup₂ closed₁ closed₂
      hl.2.2 ha.2.2 hb.2.2
  · intro C E s sup closed hs
    exact (fiveVC initialFlag).init C E s sup closed hs.2.2
  · intro C U s B e trans irr sup closed member semantic metadata hs hB hc hu
    exact (fiveVC initialFlag).causal_delta C U s B e trans irr sup closed member semantic metadata
      hs.2.2 hB.2.2 hc.2.2 hu.2.2
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hc ha hm
    exact (fiveVC initialFlag).local_redistribute C E₁ E₂ l B t b e ctx member absent
      hl.2.2 hB.2.2 ht.2.2 hb.2.2 hc.2.2 ha.2.2 hm.2.2
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx member₁ member₂ h₀ hB h₁ h₂ hc ha₀ ha₁ ha₂ hm
    exact (fiveVC initialFlag).shared C E₁ E₂ t₀ t₁ t₂ B e ctx member₁ member₂
      h₀.2.2 hB.2.2 h₁.2.2 h₂.2.2 hc.2.2 ha₀.2.2 ha₁.2.2 ha₂.2.2 hm.2.2

theorem certifiedSupply (initialFlag : Bool) (C : ReplayContext (D initialFlag).toUpdateSig)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x) :
    Raw.ReplaySupply policy (certifiedRepresentation initialFlag) (scheme initialFlag) C := by
  have supply := replaySupply initialFlag C trans irr
  refine ⟨?_,?_⟩
  · intro E π hp sup
    obtain ⟨s,hs⟩ := supply.represented E π hp sup
    exact ⟨s,trans,irr,hs⟩
  · intro E s hs sup nonempty closed
    obtain ⟨choice⟩ := supply.peel E s hs.2.2 sup nonempty closed
    exact ⟨{ choice with
      remainder_rep := ⟨trans,irr,choice.remainder_rep⟩
      past_rep := ⟨trans,irr,choice.past_rep⟩
      reconstructed_past := ⟨trans,irr,choice.reconstructed_past⟩
      reconstructed_union := ⟨trans,irr,choice.reconstructed_union⟩ }⟩

theorem uniform_noncomm_exact (initialFlag invert : Bool) (a b : Op Action) :
    ¬ (D initialFlag invert).toUpdateSig.commutes a b ↔
      policy.before a.op b.op ∨ policy.before b.op a.op := by
  by_cases same : a.op = b.op
  · have comm := NeemFlagEvent.same_action_commutes initialFlag invert a b same
    cases hop : a.op <;> simp [policy,← same,hop,comm]
  · have noncomm := NeemFlagEvent.different_action_noncommutes initialFlag invert a b same
    cases ha : a.op <;> cases hb : b.op <;> simp [ha,hb] at same
    all_goals simp [policy,ha,hb,noncomm]

theorem order_iff (initialFlag invert : Bool) (C : ReplayContext (D initialFlag invert).toUpdateSig)
    (E : Set (Op Action)) (a b : Op Action) :
    paperOrder policy C E a b ↔ @loOn (D initialFlag invert).toUpdateSig policy.lift C E a b := by
  simp only [paperOrder,loOn,OperationPolicy.lift_replayOrder_iff,
    ← uniform_noncomm_exact initialFlag invert]

theorem of_canonical (initialFlag invert : Bool)
    (C : ReplayContext (D initialFlag invert).toUpdateSig) (E : Set (Op Action)) (s : State)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x) (sup : Supported C E)
    (h : @IsCanonicalState (D initialFlag invert).toUpdateSig policy.lift C E s) :
    representation initialFlag C E s := by
  classical
  obtain ⟨π,hp,ordered,fold⟩ := h
  have paper : respects π (paperOrder policy C E) :=
    ordered.imp (fun {_ _} h => h ∘ (order_iff initialFlag invert C E _ _).mp)
  obtain ⟨t,ht⟩ := represented initialFlag C E π hp sup
  have ct := canonical initialFlag C trans irr E t ht
  have cs : Canonical policy C E s := ⟨π,hp,paper,fold⟩
  have eq := ConcreteMRDT.canonical_unique (NeemFlagEvent.laws initialFlag invert) C E sup cs ct
  simpa only [eq] using ht

theorem causalJoin (initialFlag invert : Bool) :
    @CausalJoin (D initialFlag invert) policy.lift := by
  intro C E₁ E₂ l a b trans irr sup₁ sup₂ closed₁ closed₂ hl ha hb
  have tr : Transitive C.vis := fun _ _ _ => trans
  have joined := join initialFlag C E₁ E₂ l a b tr irr sup₁ sup₂ closed₁ closed₂
    (of_canonical initialFlag invert C _ l tr irr (fun e he => sup₁ e he.1) hl)
    (of_canonical initialFlag invert C _ a tr irr sup₁ ha)
    (of_canonical initialFlag invert C _ b tr irr sup₂ hb)
  obtain ⟨π,hp,ho,hf⟩ := canonical initialFlag C tr irr _ _ joined
  exact ⟨π,hp,ho.imp (fun {_ _} h => h ∘ (order_iff initialFlag invert C _ _ _).mpr),hf⟩

theorem canonicalConfig (initialFlag invert : Bool) {I : Issuance (D initialFlag invert)}
    {C : Configuration (D initialFlag invert)}
    (reach : MintCertifiedReachV (D initialFlag invert)
      (canonicalVirtualMergeBase (D initialFlag invert)) I C) :
    @CanonicalConfig (D initialFlag invert) policy.lift C := by
  letI : EventOrder (D initialFlag invert).toUpdateSig := policy.lift
  exact CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C _ => causalJoin initialFlag invert C.replayContext) reach

theorem representedVersions (initialFlag invert : Bool) {I : Issuance (D initialFlag invert)}
    {C : Configuration (D initialFlag invert)}
    (reach : MintCertifiedReachV (D initialFlag invert)
      (canonicalVirtualMergeBase (D initialFlag invert)) I C)
    (v : Version) (s : State) (E : Set (Op Action)) (hv : C.ver v = some (s,E)) :
    certifiedRepresentation initialFlag C.replayContext E s := by
  letI : EventOrder (D initialFlag invert).toUpdateSig := policy.lift
  have good := canonicalConfig initialFlag invert reach
  refine ⟨fun _ _ _ => good.vis_trans,good.vis_irrefl,?_⟩
  exact of_canonical initialFlag invert C.replayContext E s
    (fun _ _ _ => good.vis_trans) good.vis_irrefl
    (good.version_events_supported v s E hv) (good.canonical v s E hv)

/-- The query polarity changes no state equations or metadata relation. This
rebuilds the nominal MRDTSig-indexed structures at that exact query signature. -/
def schemeFor (initialFlag invert : Bool) (C : ReplayContext (D initialFlag invert).toUpdateSig) :
    @MetadataDependencies (D initialFlag invert) C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

theorem certifiedFiveVCFor (initialFlag invert : Bool) :
    @Raw.MergeVCs (D initialFlag invert) policy (certifiedRepresentation initialFlag)
      (schemeFor initialFlag invert) := by
  constructor
  · intro C E₁ E₂ l a b sup₁ sup₂ closed₁ closed₂ hl ha hb
    exact (certifiedFiveVC initialFlag).merge_comm C E₁ E₂ l a b sup₁ sup₂ closed₁ closed₂ hl ha hb
  · intro C E s sup closed hs
    exact (certifiedFiveVC initialFlag).init C E s sup closed hs
  · intro C U s B e trans irr sup closed member semantic metadata hs hB hc hu
    exact (certifiedFiveVC initialFlag).causal_delta C U s B e trans irr sup closed member semantic metadata hs hB hc hu
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hc ha hm
    let old : Raw.Context policy (scheme initialFlag) C E₁ E₂ e :=
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩
    exact (certifiedFiveVC initialFlag).local_redistribute C E₁ E₂ l B t b e old member absent hl hB ht hb hc ha hm
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx member₁ member₂ h₀ hB h₁ h₂ hc ha₀ ha₁ ha₂ hm
    let old : Raw.Context policy (scheme initialFlag) C E₁ E₂ e :=
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩
    exact (certifiedFiveVC initialFlag).shared C E₁ E₂ t₀ t₁ t₂ B e old member₁ member₂ h₀ hB h₁ h₂ hc ha₀ ha₁ ha₂ hm

theorem certifiedSupplyFor (initialFlag invert : Bool)
    (C : ReplayContext (D initialFlag invert).toUpdateSig)
    (trans : Transitive C.vis) (irr : ∀ x, ¬ C.vis x x) :
    @Raw.ReplaySupply (D initialFlag invert) policy (certifiedRepresentation initialFlag)
      (schemeFor initialFlag invert) C := by
  have supply := certifiedSupply initialFlag C trans irr
  refine ⟨supply.represented,?_⟩
  intro E s hs sup nonempty closed
  obtain ⟨choice⟩ := supply.peel E s hs sup nonempty closed
  exact ⟨⟨choice.event,choice.member,choice.semantic_maximal,choice.metadata_maximal,
    choice.remainder,choice.past,choice.remainder_rep,choice.past_rep,
    choice.reconstructed_past,choice.reconstructed_union⟩⟩

def replayConditions (initialFlag invert : Bool) :
    VCReplayConditions policy (generation initialFlag invert) where
  representation := certifiedRepresentation initialFlag
  scheme := schemeFor initialFlag invert
  laws := NeemFlagEvent.laws initialFlag invert
  vcs := certifiedFiveVCFor initialFlag invert
  unique := fun C E a b ha hb => unique initialFlag C E a b ha.2.2 hb.2.2
  initial := fun C E s h => ⟨h.1,h.2.1,initial_rep initialFlag C⟩
  finite := fun C E s h => finite_rep initialFlag C E s h.2.2
  canonical := fun C E s h => canonical initialFlag C h.1 h.2.1 E s h.2.2
  supported := fun _ _ _ h => h.2.2.1
  replaySupply := fun C _ _ _ _ trans irr _ _ _ _ => certifiedSupplyFor initialFlag invert C trans irr
  representedVersions := fun C reach v s E hv => representedVersions initialFlag invert reach v s E hv

#print axioms replayConditions
#print axioms causalJoin

#print axioms fiveVC
#print axioms join

end Sal.MRDTs.Paper1.NeemFlagVC
