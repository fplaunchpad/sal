import Sal.MRDTs.Paper1.CertifiedRGACoreMergeVC

/-! RichCore changes only the independent client query. The raw equality
VC equations and metadata supply remain the operational Core proof. -/
namespace Sal.MRDTs.Paper1.CertifiedRGARichVC
open Foundation Sal.EmbedRGA Instances.SidedPeritext
noncomputable section
abbrev representation (Γ : OrderedPrefixCode) : ConcreteMRDT.Representation (RichCore Γ) :=
  CertifiedRGACoreVC.representation Γ

def policy (Γ : OrderedPrefixCode) : OperationPolicy (RichCore Γ).AppOp := CertifiedRGACoreVC.policy Γ

def scheme (Γ : OrderedPrefixCode) (C : ReplayContext (RichCore Γ).toUpdateSig) :
    ConcreteMRDT.MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

theorem mergeVCs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    (policy Γ) (representation Γ) (scheme Γ) := by
  have h := CertifiedRGACoreMergeVC.mergeVCs Γ
  refine ⟨h.merge_comm,h.init,h.causal_delta,?_,?_⟩
  · intro C E₁ E₂ l B t b e ctx
    exact h.local_redistribute C E₁ E₂ l B t b e
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx
    exact h.shared C E₁ E₂ t₀ t₁ t₂ B e
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩

theorem replaySupply (Γ : OrderedPrefixCode) (C : ReplayContext (RichCore Γ).toUpdateSig)
    (honest : Instances.SidedEmbedRGA.SHonestCore Γ (projReplayContext₁ C))
    (native : CertifiedRGACoreVC.NativeInsertOnly Γ C) (trans : Transitive C.vis)
    (irr : ∀e, ¬C.vis e e) :
    ConcreteMRDT.Raw.ReplaySupply (policy Γ) (representation Γ) (scheme Γ) C := by
  have h := CertifiedRGACoreVC.replaySupply Γ C honest native trans irr
  refine ⟨h.represented,?_⟩
  intro H s rep sup nonempty closed
  obtain ⟨choice⟩ := h.peel H s rep sup nonempty closed
  exact ⟨⟨choice.event,choice.member,choice.semantic_maximal,choice.metadata_maximal,
    choice.remainder,choice.past,choice.remainder_rep,choice.past_rep,
    choice.reconstructed_past,choice.reconstructed_union⟩⟩

theorem representationJoin (Γ : OrderedPrefixCode) : ConcreteMRDT.RepresentationJoin (representation Γ) := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs (mergeVCs Γ)
    (CertifiedRGACoreVC.unique Γ) (CertifiedRGACoreVC.initial Γ) (CertifiedRGACoreVC.finite Γ)
  intro C E₁ E₂ a b trans irr _ _ ha _
  exact replaySupply Γ C ha.1 ha.2.1 trans irr

#print axioms mergeVCs
#print axioms representationJoin
end
end Sal.MRDTs.Paper1.CertifiedRGARichVC
