import Sal.MRDTs.Paper1.CertifiedRGASidedVC

/-! Original core issuance disables native deletion. This gives a monotone
raw text carrier for the product VC route, while evidence deletions remain
actual grow-only-store events. -/
namespace Sal.MRDTs.Paper1.CertifiedRGACoreVC
open Foundation Classical Sal.EmbedRGA
open Instances.SidedPeritext Instances.SidedEmbedRGA

def NativeInsertOnly (Γ : OrderedPrefixCode)
    (C : ReplayContext (Core Γ).toUpdateSig) : Prop :=
  ∀ o ∈ C.events, ∀ target, o.2.2 ≠ Sum.inl (SOp.del target)

theorem nativeInsertOnly_of_mint (Γ : OrderedPrefixCode) (C : Configuration (Core Γ))
    (mint : MintHonest (Core Γ) (coreGuard Γ) C) : NativeInsertOnly Γ C.replayContext := by
  intro e he target shape
  obtain ⟨xs,_,_,guard⟩ := mint e he
  rcases e with ⟨t,r,op⟩
  change op = Sum.inl (SOp.del target) at shape
  subst op
  simpa [coreGuard] using guard

def representation (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) : Prop :=
  SHonestCore Γ (projReplayContext₁ C) ∧ NativeInsertOnly Γ C ∧
  Transitive C.vis ∧ (∀e, ¬ C.vis e e) ∧ H ⊆ C.events ∧
  ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧ applySeq (Core Γ).toUpdateSig (Core Γ).init xs = s

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
  rw [CertifiedRGAVCAlgebra.Sided.membership Γ (projReplayContext₁ C) _ _
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
  rw [CertifiedRGAVCAlgebra.Sided.merge_toFinset Γ (projReplayContext₁ C) _ _ _ _ _ _
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
  simp only [Core,Stores,DeleteStore,MarkStore,prodSig,Instances.FinsetStore.D,Finset.notMem_empty,false_or]
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
  simp only [Core,Stores,DeleteStore,MarkStore,prodSig,Instances.FinsetStore.D,Finset.notMem_empty,false_or]
  exact exists_congr (fun e => and_congr_left (fun _ => perm'.2 e))

noncomputable def model (Γ : OrderedPrefixCode) : AbstractMRDT.Model (Core Γ) := Raw.model (Core Γ)
def policy (Γ : OrderedPrefixCode) : OperationPolicy (Core Γ).AppOp where before _ _ := False
def scheme (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig) :
    AbstractMRDT.MetadataDependencies (model Γ) C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

theorem unique (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.Unique (representation Γ) := by
  intro C H s t hs ht
  apply Prod.ext
  · exact CertifiedRGAVCReplay.Sided.unique Γ _ _ _ _
      (represented_text Γ C H s hs) (represented_text Γ C H t ht)
  · apply Prod.ext
    · apply Finset.ext; intro p
      exact (delete_store_membership Γ C H s hs p).trans (delete_store_membership Γ C H t ht p).symm
    · apply Finset.ext; intro p
      exact (mark_store_membership Γ C H s hs p).trans (mark_store_membership Γ C H t ht p).symm

theorem supply (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (honest : SHonestCore Γ (projReplayContext₁ C)) (native : NativeInsertOnly Γ C)
    (trans : Transitive C.vis) (irr : ∀e, ¬C.vis e e)
    (H : Set (Op (Core Γ).AppOp)) (xs : List (Op (Core Γ).AppOp))
    (perm : listPermOf xs H) (support : H ⊆ C.events) : ∃s, representation Γ C H s := by
  obtain ⟨ys,py,ordered⟩ := exists_respecting_perm (R := C.vis) (fun {_ _ _} h k => trans h k) irr xs
  exact ⟨applySeq (Core Γ).toUpdateSig (Core Γ).init ys,honest,native,trans,irr,support,ys,
    ⟨py.nodup perm.1,fun o => (py.mem_iff (a:=o)).symm.trans (perm.2 o)⟩,ordered,rfl⟩

theorem initial (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s) :
    representation Γ C ∅ (Core Γ).init :=
  ⟨rep.1,rep.2.1,rep.2.2.1,rep.2.2.2.1,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem finite (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C H s) :
    ∃xs, listPermOf xs H := by
  obtain ⟨xs,perm,_,_⟩ := rep.2.2.2.2.2
  exact ⟨xs,perm⟩

theorem snoc (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (e : Op (Core Γ).AppOp)
    (rep : representation Γ C H s) (eligible : e ∈ C.events) (absent : e ∉ H)
    (maximal : ∀ a ∈ H, ¬ C.vis e a) :
    representation Γ C (insert e H) ((Core Γ).update s e) := by
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2.2
  refine ⟨rep.1,rep.2.1,rep.2.2.1,rep.2.2.2.1,?_,xs ++ [e],?_,?_,?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact eligible
    · exact rep.2.2.2.2.1 hx
  · refine ⟨List.nodup_append.mpr ⟨perm.1,by simp,?_⟩,?_⟩
    · intro a ha b hb eq
      exact absent ((eq.trans (List.mem_singleton.mp hb)) ▸ ((perm.2 a).mp ha))
    · intro x
      simp only [List.mem_append,List.mem_singleton,Set.mem_insert_iff]
      rw [perm.2]
      tauto
  · apply List.pairwise_append.mpr ⟨ordered,by simp,?_⟩
    intro a ha b hb vis
    have eq := List.mem_singleton.mp hb
    subst b
    exact maximal a ((perm.2 a).mp ha) vis
  · rw [applySeq_append_single,fold]

theorem peel (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (U : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (rep : representation Γ C U s)
    (nonempty : U.Nonempty) (closed : (scheme  Γ C).Closed U) :
    Nonempty (AbstractMRDT.Raw.PeelChoice (model Γ) (policy Γ) (representation Γ) C (scheme Γ C) U) := by
  obtain ⟨xs,perm,ordered,_⟩ := rep.2.2.2.2.2
  have semantic : respects xs (paperOrder (policy Γ) C U) := by
    apply ordered.imp
    intro a b hn edge
    rcases edge with ⟨vis,_⟩ | ⟨_,_,bad,_⟩
    · exact hn vis
    · exact bad
  obtain ⟨e,member,semanticMax,metadataMax⟩ :=
    AbstractMRDT.joint_maximal_of_enumeration xs perm nonempty semantic ordered
  let M := scheme  Γ C
  have pastSub : M.Past e ⊆ U := M.past_subset U e closed member
  obtain ⟨pre,pPre⟩ := AbstractMRDT.enumeration_subset perm
    (show U \ {e} ⊆ U from Set.diff_subset)
  obtain ⟨past,pPast⟩ := AbstractMRDT.enumeration_subset perm
    (show M.Past e \ {e} ⊆ U from fun _ h => pastSub h.1)
  obtain ⟨a,ha⟩ := supply Γ C rep.1 rep.2.1 rep.2.2.1 rep.2.2.2.1 _ pre pPre
    (fun _ h => rep.2.2.2.2.1 h.1)
  obtain ⟨b,hb⟩ := supply Γ C rep.1 rep.2.1 rep.2.2.1 rep.2.2.2.1 _ past pPast
    (fun _ h => rep.2.2.2.2.1 (pastSub h.1))
  refine ⟨⟨e,member,semanticMax,metadataMax,a,b,ha,hb,?_,?_⟩⟩
  · have eq : insert e (M.Past e \ {e}) = M.Past e := by
      ext x
      simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact h.1
      · intro h
        by_cases same : x = e
        · exact Or.inl same
        · exact Or.inr ⟨h,same⟩
    rw [← eq]
    apply snoc Γ C _ _ e hb (rep.2.2.2.2.1 member) (by simp)
    intro x hx forward
    have back := M.past_vis rep.2.2.1 hx.1 hx.2
    exact rep.2.2.2.1 e (rep.2.2.1 forward back)
  · have eq : insert e (U \ {e}) = U := by
      ext x
      simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
      tauto
    rw [← eq]
    apply snoc Γ C _ _ e ha (rep.2.2.2.2.1 member) (by simp)
    intro x hx
    exact metadataMax x hx.1 hx.2

theorem replaySupply (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (honest : SHonestCore Γ (projReplayContext₁ C)) (native : NativeInsertOnly Γ C) (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e) :
    AbstractMRDT.Raw.ReplaySupply (model Γ) (policy Γ) (representation Γ) (scheme Γ) C := by
  refine ⟨?_,?_⟩
  · intro H xs perm support
    exact supply Γ C honest native trans irr H xs perm (fun _ h => support _ h)
  · intro H s rep _ nonempty closed
    exact peel Γ C H s rep nonempty closed

#print axioms nativeInsertOnly_of_mint
#print axioms text_mono
end Sal.MRDTs.Paper1.CertifiedRGACoreVC
