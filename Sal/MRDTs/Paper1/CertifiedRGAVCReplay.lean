import Sal.MRDTs.Paper1.CertifiedRGAIssuance
import Sal.MRDTs.Paper1.GuardedRawModel
import Sal.MRDTs.Paper1.GuardedRawJoin

namespace Sal.MRDTs.Paper1.CertifiedRGAVCReplay
open Foundation Sal.EmbedRGA
namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

/-- A subset need not be closed to admit raw replay. If both an insertion
and its delete occur, original mint honesty identifies the birth and causal
ordering puts that insertion first. -/
theorem wellformed_supported (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (xs : List (Op (EOp α))) (nodup : xs.Nodup)
    (support : ∀ o ∈ xs, o ∈ C.events) (ordered : respects xs C.vis) : EWf Γ xs := by
  constructor
  · apply List.Nodup.map_on ?_ (nodup.filter _)
    intro a ha b hb same
    exact C.ts_unique (support a (List.mem_of_mem_filter ha))
      (support b (List.mem_of_mem_filter hb)) same
  · intro pre o post split ins deleted
    obtain ⟨d,hd,shape⟩ := mem_eDels.mp deleted
    have hdAll : d ∈ xs := by rw [split]; exact List.mem_append_left _ hd
    have hoAll : o ∈ xs := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨birth,hbirth,vis,time,_⟩ := honest.del_has_ins d (support d hdAll) o.1 shape
    have eq : birth = o := C.ts_unique hbirth (support o hoAll) time
    subst birth
    have pair := ordered
    rw [split] at pair
    exact (List.pairwise_append.mp pair).2.2 d hd o List.mem_cons_self vis
  · intro a ha b hb ia ib ne
    exact e_keys_inj_events honest a (support a ha) b (support b hb) ia ib ne

def representation (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (H : Set (Op (EOp α))) (s : EState α) : Prop :=
  EHonestCore Γ C ∧ Transitive C.vis ∧ (∀ e, ¬ C.vis e e) ∧ H ⊆ C.events ∧
    ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧ eFold Γ xs = s

def model (Γ : OrderedPrefixCode) : AbstractMRDT.Model (E Γ α) := Raw.model (E Γ α)
def policy : OperationPolicy (EOp α) where before _ _ := False

def scheme (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig) :
    AbstractMRDT.MetadataDependencies (model (α := α) Γ) C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

theorem unique (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.Unique (representation (α := α) Γ) := by
  intro C H s t hs ht
  obtain ⟨xs,px,rx,fx⟩ := hs.2.2.2.2
  obtain ⟨ys,py,ry,fy⟩ := ht.2.2.2.2
  have wx := wellformed_supported Γ C hs.1 xs px.1 (fun o ho => hs.2.2.2.1 ((px.2 o).mp ho)) rx
  have wy := wellformed_supported Γ C ht.1 ys py.1 (fun o ho => ht.2.2.2.1 ((py.2 o).mp ho)) ry
  exact fx.symm.trans ((e_fold_canon Γ wx wy (fun o => (px.2 o).trans (py.2 o).symm)).trans fy)

theorem supply (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e)
    (H : Set (Op (EOp α))) (xs : List (Op (EOp α))) (perm : listPermOf xs H)
    (support : H ⊆ C.events) : ∃ s, representation Γ C H s := by
  obtain ⟨ys,py,ordered⟩ := exists_respecting_perm (R := C.vis) (fun {_ _ _} h k => trans h k) irr xs
  refine ⟨eFold Γ ys,honest,trans,irr,support,ys,?_,ordered,rfl⟩
  exact ⟨py.nodup perm.1,fun o => (py.mem_iff (a := o)).symm.trans (perm.2 o)⟩

theorem snoc (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (H : Set (Op (EOp α))) (s : EState α) (e : Op (EOp α))
    (rep : representation Γ C H s) (eligible : e ∈ C.events) (absent : e ∉ H)
    (maximal : ∀ a ∈ H, ¬ C.vis e a) :
    representation Γ C (insert e H) (eUpdate Γ s e) := by
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
  · rw [eFold_snoc,fold]

theorem initial (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (H : Set (Op (EOp α))) (s : EState α) (rep : representation Γ C H s) :
    representation Γ C ∅ (E Γ α).init :=
  ⟨rep.1,rep.2.1,rep.2.2.1,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem finite (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (H : Set (Op (EOp α))) (s : EState α) (rep : representation Γ C H s) :
    ∃ xs, listPermOf xs H := by
  obtain ⟨xs,perm,_,_⟩ := rep.2.2.2.2
  exact ⟨xs,perm⟩

theorem peel (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (U : Set (Op (EOp α))) (s : EState α) (rep : representation Γ C U s)
    (nonempty : U.Nonempty) (closed : (scheme (α := α) Γ C).Closed U) :
    Nonempty (AbstractMRDT.Raw.PeelChoice (model Γ) policy (representation Γ) C (scheme Γ C) U) := by
  obtain ⟨xs,perm,ordered,_⟩ := rep.2.2.2.2
  have semantic : respects xs (paperOrder (policy (α := α)) C U) := by
    apply ordered.imp
    intro a b hn edge
    rcases edge with ⟨vis,_⟩ | ⟨_,_,bad,_⟩
    · exact hn vis
    · exact bad
  obtain ⟨e,member,semanticMax,metadataMax⟩ :=
    AbstractMRDT.joint_maximal_of_enumeration xs perm nonempty semantic ordered
  let M := scheme (α := α) Γ C
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

theorem replaySupply (Γ : OrderedPrefixCode) (C : ReplayContext (E Γ α).toUpdateSig)
    (honest : EHonestCore Γ C) (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e) :
    AbstractMRDT.Raw.ReplaySupply (model Γ) policy (representation Γ) (scheme Γ) C := by
  refine ⟨?_,?_⟩
  · intro H xs perm support
    exact supply Γ C honest trans irr H xs perm (fun _ h => support _ h)
  · intro H s rep _ nonempty closed
    exact peel Γ C H s rep nonempty closed

end Embedded
namespace Sided
open Instances.SidedEmbedRGA

/-- A subset need not be closed to admit raw replay. If both an insertion
and its delete occur, original mint honesty identifies the birth and causal
ordering puts that insertion first. -/
theorem wellformed_supported (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (xs : List (Op (SOp))) (nodup : xs.Nodup)
    (support : ∀ o ∈ xs, o ∈ C.events) (ordered : respects xs C.vis) : SWf Γ xs := by
  constructor
  · apply List.Nodup.map_on ?_ (nodup.filter _)
    intro a ha b hb same
    exact C.ts_unique (support a (List.mem_of_mem_filter ha))
      (support b (List.mem_of_mem_filter hb)) same
  · intro pre o post split ins deleted
    obtain ⟨d,hd,shape⟩ := mem_sDels.mp deleted
    have hdAll : d ∈ xs := by rw [split]; exact List.mem_append_left _ hd
    have hoAll : o ∈ xs := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨birth,hbirth,vis,time,_⟩ := honest.del_has_ins d (support d hdAll) o.1 shape
    have eq : birth = o := C.ts_unique hbirth (support o hoAll) time
    subst birth
    have pair := ordered
    rw [split] at pair
    exact (List.pairwise_append.mp pair).2.2 d hd o List.mem_cons_self vis
  · intro a ha b hb ia ib ne
    exact s_keys_inj_events honest a (support a ha) b (support b hb) ia ib ne

def representation (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op (SOp))) (s : SState) : Prop :=
  SHonestCore Γ C ∧ Transitive C.vis ∧ (∀ e, ¬ C.vis e e) ∧ H ⊆ C.events ∧
    ∃ xs, listPermOf xs H ∧ respects xs C.vis ∧ sFold Γ xs = s

def model (Γ : OrderedPrefixCode) : AbstractMRDT.Model (S Γ) := Raw.model (S Γ)
def policy : OperationPolicy (SOp) where before _ _ := False

def scheme (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig) :
    AbstractMRDT.MetadataDependencies (model Γ) C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

theorem unique (Γ : OrderedPrefixCode) : AbstractMRDT.Raw.Unique (representation Γ) := by
  intro C H s t hs ht
  obtain ⟨xs,px,rx,fx⟩ := hs.2.2.2.2
  obtain ⟨ys,py,ry,fy⟩ := ht.2.2.2.2
  have wx := wellformed_supported Γ C hs.1 xs px.1 (fun o ho => hs.2.2.2.1 ((px.2 o).mp ho)) rx
  have wy := wellformed_supported Γ C ht.1 ys py.1 (fun o ho => ht.2.2.2.1 ((py.2 o).mp ho)) ry
  exact fx.symm.trans ((s_fold_canon Γ wx wy (fun o => (px.2 o).trans (py.2 o).symm)).trans fy)

theorem supply (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e)
    (H : Set (Op (SOp))) (xs : List (Op (SOp))) (perm : listPermOf xs H)
    (support : H ⊆ C.events) : ∃ s, representation Γ C H s := by
  obtain ⟨ys,py,ordered⟩ := exists_respecting_perm (R := C.vis) (fun {_ _ _} h k => trans h k) irr xs
  refine ⟨sFold Γ ys,honest,trans,irr,support,ys,?_,ordered,rfl⟩
  exact ⟨py.nodup perm.1,fun o => (py.mem_iff (a := o)).symm.trans (perm.2 o)⟩

theorem snoc (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op (SOp))) (s : SState) (e : Op (SOp))
    (rep : representation Γ C H s) (eligible : e ∈ C.events) (absent : e ∉ H)
    (maximal : ∀ a ∈ H, ¬ C.vis e a) :
    representation Γ C (insert e H) (sUpdate Γ s e) := by
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
  · rw [sFold_snoc,fold]

theorem initial (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op (SOp))) (s : SState) (rep : representation Γ C H s) :
    representation Γ C ∅ (S Γ).init :=
  ⟨rep.1,rep.2.1,rep.2.2.1,by simp,[],⟨List.nodup_nil,by simp⟩,List.Pairwise.nil,rfl⟩

theorem finite (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (H : Set (Op (SOp))) (s : SState) (rep : representation Γ C H s) :
    ∃ xs, listPermOf xs H := by
  obtain ⟨xs,perm,_,_⟩ := rep.2.2.2.2
  exact ⟨xs,perm⟩

theorem peel (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (U : Set (Op (SOp))) (s : SState) (rep : representation Γ C U s)
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

theorem replaySupply (Γ : OrderedPrefixCode) (C : ReplayContext (S Γ).toUpdateSig)
    (honest : SHonestCore Γ C) (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e) :
    AbstractMRDT.Raw.ReplaySupply (model Γ) policy (representation Γ) (scheme Γ) C := by
  refine ⟨?_,?_⟩
  · intro H xs perm support
    exact supply Γ C honest trans irr H xs perm (fun _ h => support _ h)
  · intro H s rep _ nonempty closed
    exact peel Γ C H s rep nonempty closed

end Sided

#print axioms Embedded.replaySupply
#print axioms Sided.replaySupply
end Sal.MRDTs.Paper1.CertifiedRGAVCReplay
