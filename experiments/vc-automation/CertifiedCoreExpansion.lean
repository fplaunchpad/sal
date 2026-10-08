import CertifiedRGAExpansion
import TransferProductExpansion
import Sal.MRDTs.Paper1.CertifiedRGACoreVC
import Sal.MRDTs.Paper1.CertifiedRGARichVC

/-! Fresh expansion of the exact Core and RichCore replay representations.
The existing native-insert-only premise makes the text component monotone.
No production datatype VC, Join or invariant proof is invoked. -/
namespace NeemExpansion.CertifiedCore
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Classical Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedPeritext Sal.MRDTs.Instances.SidedEmbedRGA
open CertifiedRGACoreVC (representation policy scheme NativeInsertOnly)
noncomputable section
theorem represented_text (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s) :
    CertifiedRGAVCReplay.Sided.representation Γ (projReplayContext₁ C) (evRes₁ H) s.1 := by
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2.2
  refine ⟨rep.1,?_,?_,?_,projList₁ xs,listPermOf_projList₁ perm,?_,?_⟩
  · intro a b c ab bc
    exact rep.2.2.1 ab bc
  · intro a vis
    exact rep.2.2.2.1 (inlOp a) vis
  · intro a ha
    exact mem_projReplayContext₁_events.mpr (rep.2.2.2.2.1 ha)
  · exact respects_projList₁_of (fun _ _ h => h) ordered
  · have f := congrArg Prod.fst fold
    simpa only [applySeq_prod] using f

theorem text_membership (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s)
    (p : SRec) : p ∈ (show SState from s.1) ↔ ∃o∈evRes₁ H, sIsIns o = true ∧ p = sRecOf Γ o := by
  rw [CertifiedRGA.replay_membership Γ (projReplayContext₁ C) _ _
    (represented_text Γ C H s rep) p]
  constructor
  · exact And.left
  · intro born
    refine ⟨born,?_⟩
    intro d hd shape
    exact rep.2.1 (inlOp d) (rep.2.2.2.2.1 hd) p.1 (congrArg Sum.inl shape)

theorem text_mono (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H K : Set (Op (Core Γ).AppOp)) (s t : (Core Γ).State)
    (hs : representation Γ C H s) (ht : representation Γ C K t) (subset : H ⊆ K) :
    ∀(p : SRec), p ∈ (show SState from s.1) → p ∈ (show SState from t.1) := by
  intro p hp
  obtain ⟨o,ho,ins,birth⟩ := (text_membership Γ C H s hs p).mp hp
  exact (text_membership Γ C K t ht p).mpr ⟨o,subset ho,ins,birth⟩

/-- A represented common subhistory has no disappearing text records.
Consequently the actual raw three-way merge normalizes to binary union. -/
theorem text_merge_union (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (L A B : Set (Op (Core Γ).AppOp)) (l a b : (Core Γ).State)
    (hl : representation Γ C L l) (ha : representation Γ C A a)
    (hb : representation Γ C B b) (left : L ⊆ A) (right : L ⊆ B) :
    (sMerge l.1 a.1 b.1).toFinset =
      (show SState from a.1).toFinset ∪ (show SState from b.1).toFinset := by
  rw [CertifiedRGA.merge_toFinset Γ (projReplayContext₁ C) _ _ _ _ _ _
    (represented_text Γ C L l hl) (represented_text Γ C A a ha) (represented_text Γ C B b hb)]
  ext p
  have hleft : p ∈ (show SState from l.1).toFinset → p ∈ (show SState from a.1).toFinset :=
    fun h => List.mem_toFinset.mpr (text_mono Γ C L A l a hl ha left p (List.mem_toFinset.mp h))
  have hright : p ∈ (show SState from l.1).toFinset → p ∈ (show SState from b.1).toFinset :=
    fun h => List.mem_toFinset.mpr (text_mono Γ C L B l b hl hb right p (List.mem_toFinset.mp h))
  simp only [SetMergeAlgebra.merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
  tauto

theorem store_fold_mem {β : Type} [DecidableEq β] (s : Finset β)
    (xs : List (Op β)) (p : β) :
    p ∈ (show Finset β from applySeq (Instances.FinsetStore.D β).toUpdateSig s xs) ↔
      p ∈ s ∨ ∃e∈xs, p = e.2.2 := by
  induction xs generalizing s with
  | nil => simp [applySeq]
  | cons e xs ih =>
    rw [show applySeq (Instances.FinsetStore.D β).toUpdateSig s (e::xs) =
      applySeq (Instances.FinsetStore.D β).toUpdateSig (insert e.2.2 s : Finset β) xs from rfl,ih]
    simp only [Finset.mem_insert,List.mem_cons]
    constructor
    · rintro (h | ⟨o,ho,hp⟩)
      · rcases h with h|h
        · exact Or.inr ⟨e,Or.inl rfl,h⟩
        · exact Or.inl h
      · exact Or.inr ⟨o,Or.inr ho,hp⟩
    · rintro (h | ⟨o,ho,hp⟩)
      · exact Or.inl (Or.inr h)
      · rcases ho with rfl|ho
        · exact Or.inl (Or.inl hp)
        · exact Or.inr ⟨o,ho,hp⟩

theorem delete_store_membership (Γ : OrderedPrefixCode)
    (C : ReplayContext (Core Γ).toUpdateSig) (H : Set (Op (Core Γ).AppOp))
    (s : (Core Γ).State) (rep : representation Γ C H s) (p : Nat) :
    p ∈ (show Finset Nat from s.2.1) ↔ ∃e∈evRes₁ (evRes₂ H), p=e.2.2 := by
  obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2.2
  have f := congrArg (fun s : (Core Γ).State => s.2.1) fold
  simp only [applySeq_prod] at f
  rw [←f,store_fold_mem]
  have perm' := listPermOf_projList₁ (listPermOf_projList₂ perm)
  simp only [prodSig,Instances.FinsetStore.D,Finset.notMem_empty,false_or]
  exact exists_congr (fun e => and_congr_left (fun _ => perm'.2 e))

theorem mark_store_membership (Γ : OrderedPrefixCode)
    (C : ReplayContext (Core Γ).toUpdateSig) (H : Set (Op (Core Γ).AppOp))
    (s : (Core Γ).State) (rep : representation Γ C H s) (p : MarkEvent) :
    p ∈ (show Finset MarkEvent from s.2.2) ↔ ∃e∈evRes₂ (evRes₂ H), p=e.2.2 := by
  obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2.2
  have f := congrArg (fun s : (Core Γ).State => s.2.2) fold
  simp only [applySeq_prod] at f
  rw [←f,store_fold_mem]
  have perm' := listPermOf_projList₂ (listPermOf_projList₂ perm)
  simp only [prodSig,Instances.FinsetStore.D,Finset.notMem_empty,false_or]
  exact exists_congr (fun e => and_congr_left (fun _ => perm'.2 e))

abbrev FiniteState := Finset SRec × Finset Nat × Finset MarkEvent

def normalize {Γ : OrderedPrefixCode} (s : (Core Γ).State) : FiniteState :=
  ((show SState from s.1).toFinset,s.2)
def unite (s t : FiniteState) : FiniteState := (s.1 ∪ t.1,s.2.1 ∪ t.2.1,s.2.2 ∪ t.2.2)

theorem normalize_merge (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (L A B : Set (Op (Core Γ).AppOp)) (l a b : (Core Γ).State)
    (hl : representation Γ C L l) (ha : representation Γ C A a) (hb : representation Γ C B b)
    (left : L ⊆ A) (right : L ⊆ B) :
    normalize ((Core Γ).merge l a b) = unite (normalize a) (normalize b) := by
  apply Prod.ext
  · exact text_merge_union Γ C L A B l a b hl ha hb left right
  · rfl

theorem eq_of_normalize (Γ : OrderedPrefixCode) (s t : (Core Γ).State)
    (hs : SSorted s.1) (ht : SSorted t.1) (eq : normalize s = normalize t) : s=t := by
  apply Prod.ext
  · exact CertifiedRGAVCAlgebra.Sided.eq_of_toFinset hs ht (congrArg Prod.fst eq)
  · exact congrArg (fun z : FiniteState => z.2) eq

theorem normalized_mono (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H K : Set (Op (Core Γ).AppOp)) (s t : (Core Γ).State)
    (hs : representation Γ C H s) (ht : representation Γ C K t) (subset : H ⊆ K) :
    (normalize s).1 ⊆ (normalize t).1 ∧ (normalize s).2.1 ⊆ (normalize t).2.1 ∧
      (normalize s).2.2 ⊆ (normalize t).2.2 := by
  refine ⟨?_,?_,?_⟩
  · intro p hp
    exact List.mem_toFinset.mpr (text_mono Γ C H K s t hs ht subset p (List.mem_toFinset.mp hp))
  · intro p hp
    obtain ⟨e,he,rfl⟩ := (delete_store_membership Γ C H s hs p).mp hp
    exact (delete_store_membership Γ C K t ht e.2.2).mpr ⟨e,subset he,rfl⟩
  · intro p hp
    obtain ⟨e,he,rfl⟩ := (mark_store_membership Γ C H s hs p).mp hp
    exact (mark_store_membership Γ C K t ht e.2.2).mpr ⟨e,subset he,rfl⟩

def step (Γ : OrderedPrefixCode) (s : FiniteState) (e : Op (Core Γ).AppOp) : FiniteState :=
  match e.2.2 with
  | .inl op => (CertifiedRGAVCAlgebra.Sided.recordStep Γ (e.1,e.2.1,op) s.1,s.2)
  | .inr (.inl p) => (s.1,insert p s.2.1,s.2.2)
  | .inr (.inr p) => (s.1,s.2.1,insert p s.2.2)

theorem normalize_update (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s)
    (e : Op (Core Γ).AppOp) (eligible : e ∈ C.events) (absent : e ∉ H) :
    normalize ((Core Γ).update s e) = step Γ (normalize s) e := by
  rcases e with ⟨t,r,op|op⟩
  · apply Prod.ext
    · exact CertifiedRGA.update_toFinset Γ (projReplayContext₁ C) _ _
        (represented_text Γ C H s rep) (t,r,op)
        (mem_projReplayContext₁_events.mpr eligible) absent
    · rfl
  · cases op <;> rfl

theorem step_union (Γ : OrderedPrefixCode) (s b : FiniteState) (e : Op (Core Γ).AppOp)
    (sub : b.1 ⊆ s.1 ∧ b.2.1 ⊆ s.2.1 ∧ b.2.2 ⊆ s.2.2)
    (native : ∀target, e.2.2 ≠ Sum.inl (SOp.del target)) :
    unite s (step Γ b e) = step Γ s e := by
  rcases e with ⟨t,r,op|op⟩
  · cases op with
    | del target => exact False.elim (native target rfl)
    | ins el pref anchor side =>
      apply Prod.ext
      · apply Finset.ext; intro p
        have h : p ∈ b.1 → p ∈ s.1 := fun h => sub.1 h
        simp only [unite,step,CertifiedRGAVCAlgebra.Sided.recordStep,Finset.mem_union,Finset.mem_insert]
        tauto
      · apply Prod.ext
        · exact Finset.union_eq_left.mpr sub.2.1
        · exact Finset.union_eq_left.mpr sub.2.2
  · cases op with
    | inl p =>
      apply Prod.ext (Finset.union_eq_left.mpr sub.1)
      apply Prod.ext
      · apply Finset.ext; intro x
        have h : x ∈ b.2.1 → x ∈ s.2.1 := fun h => sub.2.1 h
        simp only [unite,step,Finset.mem_union,Finset.mem_insert]
        tauto
      · exact Finset.union_eq_left.mpr sub.2.2
    | inr p =>
      apply Prod.ext (Finset.union_eq_left.mpr sub.1)
      apply Prod.ext (Finset.union_eq_left.mpr sub.2.1)
      apply Finset.ext; intro x
      have h : x ∈ b.2.2 → x ∈ s.2.2 := fun h => sub.2.2 h
      simp only [unite,step,Finset.mem_union,Finset.mem_insert]
      tauto

theorem initial (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s) :
    representation Γ C ∅ (Core Γ).init :=
  ⟨rep.1,rep.2.1,rep.2.2.1,rep.2.2.2.1,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s) : SSorted s.1 :=
  CertifiedRGA.sorted Γ _ _ _ (represented_text Γ C H s rep)

theorem merge_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (A B : Set (Op (Core Γ).AppOp)) (l a b : (Core Γ).State)
    (ha : representation Γ C A a) (hb : representation Γ C B b) :
    SSorted ((Core Γ).merge l a b).1 :=
  CertifiedRGA.merge_sorted Γ _ _ _ _ _ _
    (represented_text Γ C A a ha) (represented_text Γ C B b hb)

theorem expanded_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    (policy Γ) (representation Γ) (scheme Γ) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro C E₁ E₂ l a b _ _ _ _ hl ha hb
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ l a b ha hb)
      (merge_sorted Γ C _ _ l b a hb ha)
    rw [normalize_merge Γ C _ _ _ l a b hl ha hb Set.inter_subset_left Set.inter_subset_right,
      normalize_merge Γ C _ _ _ l b a hl hb ha Set.inter_subset_right Set.inter_subset_left]
    simp [unite,Finset.union_comm]
  · intro C H s _ _ rep
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ _ _ _ (initial Γ C H s rep) rep)
      (sorted Γ C H s rep)
    rw [normalize_merge Γ C _ _ _ _ _ s (initial Γ C H s rep) (initial Γ C H s rep) rep
      (by simp) (by simp)]
    simp [normalize,unite,prodSig,S,Instances.FinsetStore.D]
  · intro C U s B e _ _ _ closed member _ _ hs hB hD hu
    have pastSub := (scheme Γ C).past_subset U e closed member
    have sub : (scheme Γ C).Past e \ {e} ⊆ U \ {e} := fun _ h => ⟨pastSub h.1,h.2⟩
    have he := hu.2.2.2.2.1 member
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ B s _ hs hD) (sorted Γ C U _ hu)
    rw [normalize_merge Γ C _ _ _ B s _ hB hs hD sub Set.diff_subset,
      normalize_update Γ C _ B hB e he (by simp),normalize_update Γ C _ s hs e he (by simp)]
    exact step_union Γ _ _ e (normalized_mono Γ C _ _ B s hB hs sub) (hB.2.1 e he)
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    have pastSub := (scheme Γ C).past_subset E₁ e ctx.closed₁ member
    have pb : (scheme Γ C).Past e \ {e} ⊆ E₁ \ {e} := fun _ h => ⟨pastSub h.1,h.2⟩
    have pu : (scheme Γ C).Past e \ {e} ⊆ (E₁ ∪ E₂) \ {e} := fun _ h => ⟨Or.inl (pastSub h.1),h.2⟩
    have lt : E₁ ∩ E₂ ⊆ E₁ \ {e} := by
      intro x h; exact ⟨h.1,fun eq => absent (eq ▸ h.2)⟩
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ l _ b hi hb)
      (merge_sorted Γ C _ _ B _ _ hm hD)
    rw [normalize_merge Γ C _ _ _ l _ b hl hi hb Set.inter_subset_left Set.inter_subset_right,
      normalize_merge Γ C _ _ _ B _ _ hB hm hD pu Set.diff_subset,
      normalize_merge Γ C _ _ _ B t _ hB ht hD pb Set.diff_subset,
      normalize_merge Γ C _ _ _ l t b hl ht hb lt Set.inter_subset_right]
    simp [unite,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx m₁ m₂ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    have p₁ := (scheme Γ C).past_subset E₁ e ctx.closed₁ m₁
    have p₂ := (scheme Γ C).past_subset E₂ e ctx.closed₂ m₂
    have pu : (scheme Γ C).Past e \ {e} ⊆ (E₁ ∪ E₂) \ {e} := fun _ h => ⟨Or.inl (p₁ h.1),h.2⟩
    apply eq_of_normalize Γ _ _ (merge_sorted Γ C _ _ _ _ _ hi₁ hi₂)
      (merge_sorted Γ C _ _ B _ _ hm hD)
    rw [normalize_merge Γ C _ _ _ _ _ _ hi₀ hi₁ hi₂ Set.inter_subset_left Set.inter_subset_right,
      normalize_merge Γ C _ _ _ B _ _ hB hm hD pu Set.diff_subset,
      normalize_merge Γ C _ _ _ B t₁ _ hB h₁ hD (fun _ h => ⟨p₁ h.1,h.2⟩) Set.diff_subset,
      normalize_merge Γ C _ _ _ B t₂ _ hB h₂ hD (fun _ h => ⟨p₂ h.1,h.2⟩) Set.diff_subset,
      normalize_merge Γ C _ _ _ t₀ t₁ t₂ h₀ h₁ h₂ (fun _ h => ⟨h.1.1,h.2⟩) (fun _ h => ⟨h.1.2,h.2⟩)]
    simp [unite,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]


theorem rich_expanded_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    (CertifiedRGARichVC.policy Γ) (CertifiedRGARichVC.representation Γ)
    (CertifiedRGARichVC.scheme Γ) := by
  have h := expanded_vcs Γ
  refine ⟨h.merge_comm,h.init,h.causal_delta,?_,?_⟩
  · intro C E₁ E₂ l B t b e ctx
    exact h.local_redistribute C E₁ E₂ l B t b e
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx
    exact h.shared C E₁ E₂ t₀ t₁ t₂ B e
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩

#print axioms expanded_vcs
#print axioms rich_expanded_vcs
end
end NeemExpansion.CertifiedCore
