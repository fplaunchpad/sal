import Sal.MRDTs.Paper1.CertifiedRGAFugue
import Sal.MRDTs.Paper1.GuardedRawModel
import Sal.MRDTs.Paper1.GuardedRawJoin

namespace Sal.MRDTs.Paper1.CertifiedFugueVCReplay
open Foundation Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
attribute [local instance] Instances.SidedEmbedRGA.FugueMax.rc

def representation (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) : Prop :=
  (∃ K : Configuration (datatype Γ), MintHonest (datatype Γ) (applicable Γ) K ∧
    K.replayContext = C) ∧ Transitive C.vis ∧ (∀ e, ¬ C.vis e e) ∧ H ⊆ C.events ∧
    ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧
      applySeq (datatype Γ).toUpdateSig (datatype Γ).init xs = s

def model (Γ : OrderedPrefixCode) : AbstractMRDT.Model (datatype Γ) := Raw.model (datatype Γ)
def policy : OperationPolicy Payload where before _ _ := False
def scheme (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig) :
    AbstractMRDT.MetadataDependencies (model Γ) C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

theorem respects_lo (Γ : OrderedPrefixCode) (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (H : Set (Op Payload)) (xs : List (Op Payload)) (perm : listPermOf xs H)
    (support : H ⊆ C.events) (ordered : respects xs C.vis) :
    respects xs (loOn C.replayContext H) := by
  apply ordered.imp_of_mem
  intro a b ha hb hn edge
  have ea := support ((perm.2 a).mp ha)
  have eb := support ((perm.2 b).mp hb)
  exact hn (rc_visible C mint trans eb ea ((lo_iff_rc C mint trans H eb ea).mp edge))

theorem unique (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.Unique (representation Γ) := by
  intro C H s t hs ht
  obtain ⟨K,mint,rfl⟩ := hs.1
  obtain ⟨xs,px,rx,fx⟩ := hs.2.2.2.2
  obtain ⟨ys,py,ry,fy⟩ := ht.2.2.2.2
  have trans : Transitive K.vis := hs.2.1
  have subX : ∀ e ∈ xs, e ∈ K.events := fun e he => hs.2.2.2.1 ((px.2 e).mp he)
  have subY : ∀ e ∈ ys, e ∈ K.events := fun e he => ht.2.2.2.1 ((py.2 e).mp he)
  have lx := respects_lo Γ K mint trans H xs px hs.2.2.2.1 rx
  have ly := respects_lo Γ K mint trans H ys py ht.2.2.2.1 ry
  have wfX := projected_wf K mint trans px (fun _ h => hs.2.2.2.1 h) lx
  have wfY := projected_wf K mint trans py (fun _ h => ht.2.2.2.1 h) ly
  have live : mFold Γ (xs.map recordOf) = mFold Γ (ys.map recordOf) := by
    rw [liveFold_project K mint trans xs subX, liveFold_project K mint trans ys subY]
    apply f_fold_canon Γ wfX wfY
    intro o
    simp only [List.mem_map]
    constructor
    · rintro ⟨e,he,eq⟩
      exact ⟨e,(py.2 e).mpr ((px.2 e).mp he),eq⟩
    · rintro ⟨e,he,eq⟩
      exact ⟨e,(px.2 e).mpr ((py.2 e).mp he),eq⟩
  apply fx.symm.trans
  apply Eq.trans _ fy
  rw [rawFold_records,rawFold_records]
  change State.mk _ _ = State.mk _ _
  apply congrArg₂ State.mk
  · exact live
  · apply Finset.ext
    intro g
    simp only [List.mem_toFinset,mMinted,List.mem_filter,List.mem_map]
    constructor
    · rintro ⟨⟨e,he,eq⟩,hi⟩
      exact ⟨⟨e,(py.2 e).mpr ((px.2 e).mp he),eq⟩,hi⟩
    · rintro ⟨⟨e,he,eq⟩,hi⟩
      exact ⟨⟨e,(px.2 e).mpr ((py.2 e).mp he),eq⟩,hi⟩

theorem supply (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (honest : ∃ K : Configuration (datatype Γ), MintHonest (datatype Γ) (applicable Γ) K ∧ K.replayContext = C) (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e)
    (H : Set (Op Payload)) (xs : List (Op Payload)) (perm : listPermOf xs H)
    (support : H ⊆ C.events) : ∃ s, representation Γ C H s := by
  obtain ⟨ys,py,ordered⟩ := exists_respecting_perm (R := C.vis) (fun {_ _ _} h k => trans h k) irr xs
  refine ⟨applySeq (datatype Γ).toUpdateSig (datatype Γ).init ys,honest,trans,irr,support,ys,?_,ordered,rfl⟩
  exact ⟨py.nodup perm.1,fun o => (py.mem_iff (a := o)).symm.trans (perm.2 o)⟩

theorem snoc (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (e : Op Payload)
    (rep : representation Γ C H s) (eligible : e ∈ C.events) (absent : e ∉ H)
    (maximal : ∀ a ∈ H, ¬ C.vis e a) :
    representation Γ C (insert e H) (rawUpdate Γ s e) := by
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  refine ⟨rep.1,rep.2.1,rep.2.2.1,?_,xs ++ [e],?_,?_,?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact eligible
    · exact rep.2.2.2.1 hx
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
  · simp only [applySeq, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change rawUpdate Γ (applySeq (datatype Γ).toUpdateSig (datatype Γ).init xs) e = _
    rw [fold]

theorem initial (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) :
    representation Γ C ∅ (datatype Γ).init :=
  ⟨rep.1,rep.2.1,rep.2.2.1,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem finite (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) :
    ∃ xs, listPermOf xs H := by
  obtain ⟨xs,perm,_,_⟩ := rep.2.2.2.2
  exact ⟨xs,perm⟩

theorem peel (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (U : Set (Op Payload)) (s : State) (rep : representation Γ C U s)
    (nonempty : U.Nonempty) (closed : (scheme Γ C).Closed U) :
    Nonempty (AbstractMRDT.Raw.PeelChoice (model Γ) policy (representation Γ) C (scheme Γ C) U) := by
  obtain ⟨xs,perm,ordered,_⟩ := rep.2.2.2.2
  have semantic : respects xs (paperOrder policy C U) := by
    apply ordered.imp
    intro a b hn edge
    rcases edge with ⟨vis,_⟩ | ⟨_,_,bad,_⟩
    · exact hn vis
    · exact bad
  obtain ⟨e,member,semanticMax,metadataMax⟩ :=
    AbstractMRDT.joint_maximal_of_enumeration xs perm nonempty semantic ordered
  let M := scheme Γ C
  have pastSub : M.Past e ⊆ U := M.past_subset U e closed member
  obtain ⟨pre,pPre⟩ := AbstractMRDT.enumeration_subset perm
    (show U \ {e} ⊆ U from Set.diff_subset)
  obtain ⟨past,pPast⟩ := AbstractMRDT.enumeration_subset perm
    (show M.Past e \ {e} ⊆ U from fun _ h => pastSub h.1)
  obtain ⟨a,ha⟩ := supply Γ C rep.1 rep.2.1 rep.2.2.1 _ pre pPre
    (fun _ h => rep.2.2.2.1 h.1)
  obtain ⟨b,hb⟩ := supply Γ C rep.1 rep.2.1 rep.2.2.1 _ past pPast
    (fun _ h => rep.2.2.2.1 (pastSub h.1))
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
    apply snoc Γ C _ _ e hb (rep.2.2.2.1 member) (by simp)
    intro x hx forward
    have back := M.past_vis rep.2.1 hx.1 hx.2
    exact rep.2.2.1 e (rep.2.1 forward back)
  · have eq : insert e (U \ {e}) = U := by
      ext x
      simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
      tauto
    rw [← eq]
    apply snoc Γ C _ _ e ha (rep.2.2.2.1 member) (by simp)
    intro x hx
    exact metadataMax x hx.1 hx.2

theorem replaySupply (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (honest : ∃ K : Configuration (datatype Γ), MintHonest (datatype Γ) (applicable Γ) K ∧ K.replayContext = C) (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e) :
    AbstractMRDT.Raw.ReplaySupply (model Γ) policy (representation Γ) (scheme Γ) C := by
  refine ⟨?_,?_⟩
  · intro H xs perm support
    exact supply Γ C honest trans irr H xs perm (fun _ h => support _ h)
  · intro H s rep _ nonempty closed
    exact peel Γ C H s rep nonempty closed

end Sal.MRDTs.Paper1.CertifiedFugueVCReplay
