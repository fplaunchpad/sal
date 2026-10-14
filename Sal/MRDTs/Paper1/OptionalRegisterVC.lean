import Sal.MRDTs.Paper1.OptionalRegisterCoherence

namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation ConcreteMRDT Instances.OptionalRegister OptionalRegisterCounts
open Classical

private theorem finset_subset {F G : Finset Event} {A B : Set Event}
    (hF : (↑F : Set Event) = A) (hG : (↑G : Set Event) = B) (sub : A ⊆ B) : F ⊆ G := by
  intro e he
  have hx : e ∈ A := by rw [← hF]; exact he
  have hy := sub hx
  rw [← hG] at hy; exact hy

private theorem domain_subset {C : ReplayContext D.toUpdateSig} {A B : Set Event}
    {a b : State} (ha : representation C A a) (hb : representation C B b) (sub : A ⊆ B) :
    a.domain ⊆ b.domain := by
  obtain ⟨F,hF⟩ := ha.finite
  obtain ⟨G,hG⟩ := hb.finite
  rw [ha.domain F hF,hb.domain G hG]
  unfold rows
  exact Finset.image_subset_image (Finset.filter_subset_filter _ (finset_subset hF hG sub))

theorem past_count_facts (C : ReplayContext D.toUpdateSig)
    (U : Set Event) (s B : State) (e : Event)
    (supported : Supported C U) (closed : (scheme C).Closed U) (member : e ∈ U)
    (maximal : ∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x)
    (hs : representation C (U \ {e}) s)
    (hB : representation C ((scheme C).Past e \ {e}) B) :
    (∀ r, (B.cells r).1.1 ≤ (s.cells r).1.1) ∧
      (s.cells e.rep).1.1 = (B.cells e.rep).1.1 := by
  obtain ⟨F,hF⟩ := hs.finite
  obtain ⟨G,hG⟩ := hB.finite
  have pastSub := (scheme C).past_subset U e closed member
  have sub : G ⊆ F := finset_subset hG hF (fun x hx => ⟨pastSub hx.1,hx.2⟩)
  refine ⟨?_,?_⟩
  · intro r; rw [hB.counts G hG,hs.counts F hF]; exact count_mono G F sub r
  · rw [hs.counts F hF,hB.counts G hG]
    apply congrArg (fun A : Finset Event => (A.card : Int))
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxF,own⟩ := Finset.mem_filter.mp hx
      have hxU : x ∈ U \ {e} := by rw [← hF]; exact hxF
      obtain ⟨rx,Sx,hLx,hxS⟩ := supported x hxU.1
      obtain ⟨re,Se,hLe,heS⟩ := supported e member
      have vis := (C.vis_total_same_replica hLx hxS hLe heS hxU.2 own.1).resolve_right
        (maximal x hxU.1 hxU.2)
      have hxG : x ∈ G := by
        change x ∈ (↑G : Set Event)
        rw [hG]; exact ⟨Or.inr (.single vis),hxU.2⟩
      exact Finset.mem_filter.mpr ⟨hxG,own⟩
    · exact Finset.filter_subset_filter _ sub

private theorem true_of_equal_count_subset {C : ReplayContext D.toUpdateSig}
    {E F : Set Event} {a b : State}
    (ha : representation C E a) (hb : representation C F b)
    (sub : E ⊆ F) (r : Nat) (same : (a.cells r).1.1 = (b.cells r).1.1)
    (bit : (b.cells r).1.2 = true) : (a.cells r).1.2 = true := by
  obtain ⟨A,hA⟩ := ha.finite
  obtain ⟨B,hB⟩ := hb.finite
  have subset : winners A r ⊆ winners B r := Finset.filter_subset_filter _ (finset_subset hA hB sub)
  have cardeq : (winners A r).card = (winners B r).card := by
    rw [ha.counts A hA,hb.counts B hB] at same
    unfold count at same; exact_mod_cast same
  have eqsets := Finset.eq_of_subset_of_card_le subset (Nat.le_of_eq cardeq.symm)
  obtain ⟨w,hw,own,live⟩ := (hb.active r).mp bit
  have hwB : w ∈ winners B r := by
    apply Finset.mem_filter.mpr; refine ⟨?_,own,live.1⟩
    rw [← hB] at hw; exact hw
  rw [← eqsets] at hwB
  have hwE : w ∈ E := by rw [← hA]; exact (Finset.mem_filter.mp hwB).1
  exact (ha.active r).mpr ⟨w,hwE,own,live.1,fun d hd => live.2 d (sub hd)⟩

private theorem winners_before_reset {C : ReplayContext D.toUpdateSig}
    {E : Set Event} {e : Event} (good : GoodContext C) (sup : Supported C E)
    (reset : e.op = .unset) (r : Nat) (bit : Live C E r)
    (killed : ¬ Live C (insert e E) r) :
    ∀ w ∈ E, w.rep = r → w.op.isSet = true → C.vis w e := by
  have before {w : Event} (hw : w ∈ E) (own : w.rep = r) (live : LiveEvent C E w) : C.vis w e := by
    by_contra hn
    apply killed
    refine ⟨w,Or.inr hw,own,live.1,?_⟩
    intro d hd hop
    rcases hd with rfl | hd
    · exact hn
    · exact live.2 d hd hop
  intro w hw own win
  obtain ⟨u,hu,uown,ulive⟩ := bit
  have ue := before hu uown ulive
  by_cases same : w = u
  · exact same ▸ ue
  obtain ⟨rw,Sw,hLw,hwS⟩ := sup w hw
  obtain ⟨ru,Su,hLu,huS⟩ := sup u hu
  rcases C.vis_total_same_replica hLw hwS hLu huS same (own.trans uown.symm) with wu | uw
  · exact good.trans wu ue
  · apply before hw own
    exact ⟨win,fun d hd hop wd => ulive.2 d hd hop (good.trans uw wd)⟩

private theorem joinCell_of_past (s B : Cell) (lower : B.1.1 ≤ s.1.1)
    (coherent : CoherentCells s B)
    (tied : s.1.1 = B.1.1 → s.1.2 = true → B.1.2 = true) : joinCell s B = s := by
  rcases lt_or_eq_of_le lower with less | same
  · have keylt : cellKey B < cellKey s := Prod.Lex.toLex_lt_toLex.mpr (Or.inl less)
    simp [joinCell,max_eq_left (le_of_lt keylt)]
  · rcases coherent with ⟨payload,sz,Bz⟩
    rcases s with ⟨⟨sc,sf⟩,sp⟩
    rcases B with ⟨⟨Bc,Bf⟩,Bp⟩
    simp only [Prod.fst,Prod.snd] at *
    subst Bc
    cases sf <;> cases Bf
    · have eq := (sz rfl).trans (Bz rfl).symm
      subst Bp; exact joinCell_idem _
    · rw [joinCell_comm]
      have keylt : cellKey ((sc,true),Bp) < cellKey ((sc,false),sp) := by
        apply Prod.Lex.toLex_lt_toLex.mpr
        right; refine ⟨rfl,?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        left; simp
      simp [joinCell,max_eq_right (le_of_lt keylt)]
    · exact False.elim (Bool.noConfusion (tied rfl rfl))
    · have eq := (payload rfl rfl).2.2 rfl
      subst Bp; exact joinCell_idem _

/-- The causal equation uses reconstructed field evidence and single-writer
Set prefixes. It does not invoke representation Join. -/
theorem causal_delta (C : ReplayContext D.toUpdateSig) (U : Set Event)
    (s B : State) (e : Event) (sup : Supported C U) (closed : (scheme C).Closed U)
    (member : e ∈ U)
    (semantic : ∀ x ∈ U, x ≠ e → ¬ paperOrder policy C U e x)
    (metadata : ∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x)
    (hs : representation C (U \ {e}) s)
    (hB : representation C ((scheme C).Past e \ {e}) B) :
    merge B s (update B e) = update s e := by
  have sub : ((scheme C).Past e \ {e}) ⊆ (U \ {e}) :=
    fun x hx => ⟨(scheme C).past_subset U e closed member hx.1,hx.2⟩
  have Bdom := domain_subset hB hs sub
  obtain ⟨lower,same⟩ := past_count_facts C U s B e sup closed member metadata hs hB
  have tied : ∀ r, (s.cells r).1.1 = (B.cells r).1.1 →
      (s.cells r).1.2 = true → (B.cells r).1.2 = true :=
    fun r eq bit => true_of_equal_count_subset hB hs sub r eq.symm bit
  have preClosed := (scheme C).closed_diff_of_max U U e Set.Subset.rfl closed metadata
  have pastClosed := (scheme C).closed_diff_of_max U ((scheme C).Past e) e
    ((scheme C).past_subset U e closed member) ((scheme C).past_closed e) metadata
  have coherent := represented_coherent C (U \ {e}) ((scheme C).Past e \ {e}) s B preClosed pastClosed hs hB
  have count_if_true : e.op = .unset → ∀ r, (s.cells r).1.2 = true →
      (s.cells r).1.1 = (B.cells r).1.1 := by
    intro reset r bit
    have ins : insert e (U \ {e}) = U := by
      simpa [Set.insert_eq_of_mem member] using (Set.insert_diff_singleton : insert e (U \ {e}) = insert e U)
    obtain ⟨F,hF⟩ := hs.finite
    obtain ⟨G,hG⟩ := hB.finite
    have killed : ¬ Live C (insert e (U \ {e})) r :=
      reset_kills_live C _ hs.good hs.supported F hF e (sup e member) reset
        (fun x hx ne => by rw [ins]; exact semantic x hx.1 ne)
        (fun x hx => metadata x hx.1 hx.2) (by simp) r
    have before := winners_before_reset hs.good hs.supported reset r ((hs.active r).mp bit) killed
    have eqwins : winners F r = winners G r := by
      ext w
      constructor
      · intro hw
        obtain ⟨hw,own,win⟩ := Finset.mem_filter.mp hw
        have hwU : w ∈ U \ {e} := by rw [← hF]; exact hw
        have wp : w ∈ (scheme C).Past e \ {e} := ⟨Or.inr (.single (before w hwU own win)),hwU.2⟩
        rw [← hG] at wp
        exact Finset.mem_filter.mpr ⟨wp,own,win⟩
      · intro hw
        obtain ⟨hw,own,win⟩ := Finset.mem_filter.mp hw
        have wp : w ∈ (scheme C).Past e \ {e} := by rw [← hG]; exact hw
        have wu := sub wp
        rw [← hF] at wu
        exact Finset.mem_filter.mpr ⟨wu,own,win⟩
    rw [hs.counts F hF,hB.counts G hG]
    unfold count; rw [eqwins]
  apply State.ext
  · cases hop : e.op
    all_goals ext r; simp only [merge,update,hop,Finset.mem_union,Finset.mem_insert]
    all_goals have dom := fun h : r ∈ B.domain => Bdom h
    all_goals tauto
  · intro r
    cases hop : e.op with
    | set value =>
      by_cases own : r = e.rep
      · subst r
        have ts : (s.cells e.rep).1.2 = true → (s.cells e.rep).2.1 < e.time := by
          intro bit
          obtain ⟨w,hw,wown,live,payload,_⟩ := hs.payload e.rep bit
          obtain ⟨rw,Sw,hLw,hwS⟩ := sup w hw.1
          obtain ⟨re,Se,hLe,heS⟩ := sup e member
          have before := (C.vis_total_same_replica hLw hwS hLe heS hw.2 wown).resolve_right
            (metadata w hw.1 hw.2)
          rw [payload]; exact hs.good.mono before
        change mergeCell (B.cells e.rep) (s.cells e.rep) ((update B e).cells e.rep) = ((update s e).cells e.rep)
        simp only [update,hop,ite_true]
        cases bit : (s.cells e.rep).1.2
        · simp [mergeCell,Instances.NeemFlag.mergeFlag,bit,same]
        · have growth := ts bit
          simp [mergeCell,Instances.NeemFlag.mergeFlag,bit,same,mergePayload,
            ne_of_lt growth,not_lt_of_ge (le_of_lt growth)]
      · change mergeCell (B.cells r) (s.cells r) ((update B e).cells r) = ((update s e).cells r)
        simp only [update,hop,if_neg own]
        rw [sourceCell_as_join _ _ _ (min_eq_right (lower r)).symm (coherent r)]
        exact joinCell_of_past _ _ (lower r) (coherent r) (tied r)
    | unset =>
      have ct := count_if_true hop r
      change mergeCell (B.cells r) (s.cells r) ((update B e).cells r) = ((update s e).cells r)
      simp only [update,hop]
      cases bit : (s.cells r).1.2
      · simp [mergeCell,Instances.NeemFlag.mergeFlag,bit]
      · have eq := ct bit
        simp [mergeCell,Instances.NeemFlag.mergeFlag,bit,eq]


/-- The causal slice is the represented intersection with the remainder. -/
private theorem past_merge_as_join (C : ReplayContext D.toUpdateSig)
    (U : Set Event) (s B d : State) (e : Event)
    (closed : (scheme C).Closed U) (member : e ∈ U)
    (metadata : ∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x)
    (hs : representation C (U \ {e}) s)
    (hB : representation C ((scheme C).Past e \ {e}) B)
    (hd : representation C ((scheme C).Past e) d) : merge B s d = join s d := by
  have sub := (scheme C).past_subset U e closed member
  have intersection : (U \ {e}) ∩ (scheme C).Past e = (scheme C).Past e \ {e} := by
    ext x
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · exact fun h => ⟨⟨sub h.1,h.2⟩,h.1⟩
  apply source_as_join C (U \ {e}) ((scheme C).Past e) B s d
    ((scheme C).closed_diff_of_max U U e Set.Subset.rfl closed metadata)
    ((scheme C).past_closed e) _ hs hd
  simpa only [intersection] using hB

theorem local_equation (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (l B t b : State) (e : Event)
    (ctx : Raw.Context policy scheme C E₁ E₂ e)
    (member : e ∈ E₁) (absent : e ∉ E₂)
    (hl : representation C (E₁ ∩ E₂) l)
    (hB : representation C ((scheme C).Past e \ {e}) B)
    (ht : representation C (E₁ \ {e}) t) (hb : representation C E₂ b)
    (hc : representation C ((scheme C).Past e) (update B e))
    (ha : representation C E₁ (merge B t (update B e)))
    (hm : representation C ((E₁ ∪ E₂) \ {e}) (merge l t b)) :
    merge l (merge B t (update B e)) b = merge B (merge l t b) (update B e) := by
  have preClosed := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₁ e
    Set.subset_union_left ctx.closed₁ ctx.metadata
  have eq : (E₁ \ {e}) ∩ E₂ = E₁ ∩ E₂ := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,fun same => absent (same ▸ h.2)⟩,h.2⟩
  have base : representation C ((E₁ \ {e}) ∩ E₂) l := by rw [eq]; exact hl
  have outer := source_as_join C E₁ E₂ l _ b ctx.closed₁ ctx.closed₂ hl ha hb
  have inner := past_merge_as_join C E₁ t B (update B e) e ctx.closed₁ member
    (fun x hx ne => ctx.metadata x (Or.inl hx) ne) ht hB hc
  have middle := source_as_join C (E₁ \ {e}) E₂ l t b preClosed ctx.closed₂ base ht hb
  have right := past_merge_as_join C (E₁ ∪ E₂) (merge l t b) B (update B e) e
    (fun a b edge hx => hx.elim
      (fun h => Or.inl (ctx.closed₁ a b edge h))
      (fun h => Or.inr (ctx.closed₂ a b edge h)))
    (Or.inl member) ctx.metadata hm hB hc
  rw [outer,inner,right,middle]
  exact join_local t b (update B e)

theorem shared_equation (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (t₀ t₁ t₂ B : State) (e : Event)
    (ctx : Raw.Context policy scheme C E₁ E₂ e)
    (member₁ : e ∈ E₁) (member₂ : e ∈ E₂)
    (h₀ : representation C ((E₁ ∩ E₂) \ {e}) t₀)
    (hB : representation C ((scheme C).Past e \ {e}) B)
    (h₁ : representation C (E₁ \ {e}) t₁) (h₂ : representation C (E₂ \ {e}) t₂)
    (hc : representation C ((scheme C).Past e) (update B e))
    (ha₀ : representation C (E₁ ∩ E₂) (merge B t₀ (update B e)))
    (ha₁ : representation C E₁ (merge B t₁ (update B e)))
    (ha₂ : representation C E₂ (merge B t₂ (update B e)))
    (hm : representation C ((E₁ ∪ E₂) \ {e}) (merge t₀ t₁ t₂)) :
    merge (merge B t₀ (update B e)) (merge B t₁ (update B e))
      (merge B t₂ (update B e)) = merge B (merge t₀ t₁ t₂) (update B e) := by
  have pre₁ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₁ e
    Set.subset_union_left ctx.closed₁ ctx.metadata
  have pre₂ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₂ e
    Set.subset_union_right ctx.closed₂ ctx.metadata
  have eq : (E₁ \ {e}) ∩ (E₂ \ {e}) = (E₁ ∩ E₂) \ {e} := by ext x; simp; tauto
  have base : representation C ((E₁ \ {e}) ∩ (E₂ \ {e})) t₀ := by rw [eq]; exact h₀
  have outer := source_as_join C E₁ E₂ _ _ _ ctx.closed₁ ctx.closed₂ ha₀ ha₁ ha₂
  have inner₁ := past_merge_as_join C E₁ t₁ B (update B e) e ctx.closed₁ member₁
    (fun x hx ne => ctx.metadata x (Or.inl hx) ne) h₁ hB hc
  have inner₂ := past_merge_as_join C E₂ t₂ B (update B e) e ctx.closed₂ member₂
    (fun x hx ne => ctx.metadata x (Or.inr hx) ne) h₂ hB hc
  have middle := source_as_join C (E₁ \ {e}) (E₂ \ {e}) t₀ t₁ t₂ pre₁ pre₂ base h₁ h₂
  have right := past_merge_as_join C (E₁ ∪ E₂) (merge t₀ t₁ t₂) B (update B e) e
    (fun a b edge hx => hx.elim
      (fun h => Or.inl (ctx.closed₁ a b edge h))
      (fun h => Or.inr (ctx.closed₂ a b edge h)))
    (Or.inl member₁) ctx.metadata hm hB hc
  rw [outer,inner₁,inner₂,right,middle]
  exact join_shared t₁ t₂ (update B e)


private theorem active_count_positive (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (hs : representation C E s) (r : Nat)
    (bit : (s.cells r).1.2 = true) : 0 < (s.cells r).1.1 := by
  obtain ⟨F,hF⟩ := hs.finite
  obtain ⟨w,hw,own,live⟩ := (hs.active r).mp bit
  have hwF : w ∈ F := by rw [← hF] at hw; exact hw
  have hwW : w ∈ winners F r := Finset.mem_filter.mpr ⟨hwF,own,live.1⟩
  have positive := Finset.card_pos.mpr (show (winners F r).Nonempty from ⟨w,hwW⟩)
  rw [hs.counts F hF]
  unfold count; exact_mod_cast positive

theorem initial_equation (C : ReplayContext D.toUpdateSig)
    (E : Set Event) (s : State) (hs : representation C E s) : merge initial initial s = s := by
  apply State.ext
  · simp [merge,initial]
  · intro r
    change mergeCell zero zero (s.cells r) = s.cells r
    cases bit : (s.cells r).1.2
    · have payload := hs.inactive r bit
      apply Prod.ext
      · apply Prod.ext
        · simp [mergeCell,zero]
        · simp [mergeCell,Instances.NeemFlag.mergeFlag,zero,bit]
      · simp [mergeCell,Instances.NeemFlag.mergeFlag,zero,bit,payload]
    · have positive := active_count_positive C E s hs r bit
      apply Prod.ext
      · apply Prod.ext
        · simp [mergeCell,zero]
        · simp [mergeCell,Instances.NeemFlag.mergeFlag,zero,bit,positive]
      · simp [mergeCell,Instances.NeemFlag.mergeFlag,zero,bit,positive]

/-- Source arithmetic, finite domain, flag, and averaging branches satisfy
all five equations. Payload coherence is derived in each represented triple. -/
theorem fiveVC : Raw.MergeVCs policy representation scheme := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    exact source_comm l a b
  · intro C E s _ _ hs
    exact initial_equation C E s hs
  · intro C U s B e _ _ sup closed member semantic metadata hs hB _ _
    exact causal_delta C U s B e sup closed member semantic metadata hs hB
  · exact local_equation
  · exact shared_equation

/-- The complete source Join is obtained by the framework's strict finite
history induction, independently of the proof algebra called `join`. -/
theorem representationJoin : RepresentationJoin representation := by
  apply Raw.representationJoin_of_vcs fiveVC unique
    (fun C E s h => initial_rep C h.good) finite_rep
  intro C _ _ _ _ _ _ _ _ ha _
  exact replaySupply C ha.good

#print axioms causal_delta
#print axioms fiveVC
#print axioms representationJoin
end Sal.MRDTs.Paper1.OptionalRegister
