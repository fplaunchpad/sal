import Sal.MRDTs.Paper1.CertifiedRGAExecution
import Sal.MRDTs.Paper1.CertifiedRGARichVC

namespace Sal.MRDTs.Paper1.CertifiedRGACoreExecution
open Foundation Classical Sal.EmbedRGA
open Instances.SidedPeritext Instances.SidedEmbedRGA CertifiedRGACoreVC
attribute [local instance] coreRc

theorem represented_of_canonical (Γ : OrderedPrefixCode)
    (C : ReplayContext (Core Γ).toUpdateSig) (honest : SHonestCore Γ (projReplayContext₁ C))
    (native : NativeInsertOnly Γ C) (trans : Transitive C.vis) (irr : ∀e, ¬C.vis e e)
    (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State) (support : H ⊆ C.events)
    (closed : ∀a b, C.vis a b → b∈H → a∈H)
    (canonical : IsCanonicalState C H s) : representation Γ C H s := by
  obtain ⟨xs,perm,order,fold⟩ := canonical
  obtain ⟨t,rep⟩ := supply Γ C honest native trans irr H xs perm support
  have source : CertifiedRGAVCReplay.Sided.representation Γ (projReplayContext₁ C) (evRes₁ H) s.1 := by
    apply CertifiedRGAExecution.Sided.represented_of_canonical Γ _ honest
      (fun _ _ _ h k => trans h k) (fun e => irr (inlOp e))
    · intro e he
      exact mem_projReplayContext₁_events.mpr (support he)
    · intro a b vis hb
      exact closed (inlOp a) (inlOp b) vis hb
    · exact coreIsCanonicalState_proj₁ ⟨xs,perm,order,fold⟩
  have same : t=s := by
    apply Prod.ext
    · exact CertifiedRGAVCReplay.Sided.unique Γ _ _ _ _ (represented_text Γ C H t rep) source
    · obtain ⟨ys,py,_,fy⟩ := rep.2.2.2.2.2
      have px₂ := listPermOf_projList₂ perm
      have py₂ := listPermOf_projList₂ py
      have pp : (projList₂ ys).Perm (projList₂ xs) :=
        (List.perm_ext_iff_of_nodup py₂.1 px₂.1).mpr
          (fun e => (py₂.2 e).trans (px₂.2 e).symm)
      have eq := applySeq_perm_of_all_comm (D' := Stores.toUpdateSig) CertifiedRGAProducts.SidedPeritext.stores_commute pp Stores.init
      have fx₂ := congrArg Prod.snd fold
      have fy₂ := congrArg Prod.snd fy
      simp only [applySeq_prod] at fx₂ fy₂ eq
      exact fy₂.symm.trans (eq.trans fx₂)
  simpa only [same] using rep

theorem canonical_of_represented (Γ : OrderedPrefixCode)
    (C : ReplayContext (Core Γ).toUpdateSig) (H : Set (Op (Core Γ).AppOp)) (s : (Core Γ).State)
    (rep : representation Γ C H s) : IsCanonicalState C H s := by
  apply coreCanonical_glue
  · exact CertifiedRGAExecution.Sided.canonical_of_represented Γ _ _ _ (represented_text Γ C H s rep)
  · obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2.2
    refine ⟨projList₂ xs,listPermOf_projList₂ perm,?_,?_⟩
    · unfold respects
      exact List.pairwise_of_forall fun _ _ => by
        simp [loOn,UpdateSig.rc,ReplayPolicy.Before,ReplayPolicy.default,ReplayPolicy.unconstrained]
    · exact congrArg Prod.snd ((applySeq_prod (Core Γ).init xs).symm.trans fold)

theorem closedJoinAt (Γ : OrderedPrefixCode) (C : Configuration (Core Γ))
    (mint : MintHonest (Core Γ) (Instances.SidedPeritext.generation Γ).CanIssue C) :
    CertifiedClosedExecution.ClosedJoinAt (Core Γ) C.replayContext := by
  have honest : SHonestCore Γ (projReplayContext₁ C.replayContext) := by
    simpa only [projConf₁_core] using sHonest_core (coreHonest_of_mint C mint)
  have native := nativeInsertOnly_of_mint Γ C mint
  intro A B l a b trans irr supA supB closedA closedB hl ha hb
  apply canonical_of_represented
  exact CertifiedRGACoreMergeVC.representationJoin Γ C.replayContext A B l a b
    (fun _ _ _ h k => trans h k) irr supA supB closedA closedB
    (represented_of_canonical Γ _ honest native (fun _ _ _ h k => trans h k) irr _ _
      (fun x hx => supA x hx.1) (fun x y vis hy => ⟨closedA x y vis hy.1,closedB x y vis hy.2⟩) hl)
    (represented_of_canonical Γ _ honest native (fun _ _ _ h k => trans h k) irr _ _ supA closedA ha)
    (represented_of_canonical Γ _ honest native (fun _ _ _ h k => trans h k) irr _ _ supB closedB hb)

theorem canonicalConfig (Γ : OrderedPrefixCode) {C : Configuration (Core Γ)}
    (execution : CertifiedExecution (Core Γ) (Instances.SidedPeritext.generation Γ) C) : CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_execution (closedJoinAt Γ) execution

theorem representedVersions (Γ : OrderedPrefixCode) {C : Configuration (Core Γ)}
    (execution : CertifiedExecution (Core Γ) (Instances.SidedPeritext.generation Γ) C)
    {v : Version} {s : (Core Γ).State} {H : Set (Op (Core Γ).AppOp)}
    (hv : C.ver v=some (s,H)) : representation Γ C.replayContext H s := by
  have good := canonicalConfig Γ execution
  have honest : SHonestCore Γ (projReplayContext₁ C.replayContext) := by
    simpa only [projConf₁_core] using sHonest_core (coreHonest_of_mint C execution.mintHonest)
  exact represented_of_canonical Γ C.replayContext honest
    (nativeInsertOnly_of_mint Γ C execution.mintHonest)
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl H s
    (fun e he => good.version_events_supported v s H hv e he)
    (good.version_events_causal v s H hv) (good.canonical v s H hv)

namespace Rich
attribute [local instance] richRc

theorem closedJoinAt (Γ : OrderedPrefixCode) (C : Configuration (RichCore Γ))
    (mint : MintHonest (RichCore Γ) (richGeneration Γ).CanIssue C) :
    CertifiedClosedExecution.ClosedJoinAt (RichCore Γ) C.replayContext := by
  simpa only [RichCore,richRc,asCoreConfig] using
    CertifiedRGACoreExecution.closedJoinAt Γ (asCoreConfig C) (mintHonest_to_core mint)

theorem canonicalConfig (Γ : OrderedPrefixCode) {C : Configuration (RichCore Γ)}
    (execution : CertifiedExecution (RichCore Γ) (richGeneration Γ) C) : CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_execution (closedJoinAt Γ) execution

theorem representedVersions (Γ : OrderedPrefixCode) {C : Configuration (RichCore Γ)}
    (execution : CertifiedExecution (RichCore Γ) (richGeneration Γ) C)
    {v : Version} {s : (RichCore Γ).State} {H : Set (Op (RichCore Γ).AppOp)}
    (hv : C.ver v=some (s,H)) : CertifiedRGARichVC.representation Γ C.replayContext H s := by
  have good := canonicalConfig Γ execution
  have mint := mintHonest_to_core execution.mintHonest
  have honest : SHonestCore Γ (projReplayContext₁ C.replayContext) := by
    simpa only [projConf₁_core,asCoreConfig] using sHonest_core (coreHonest_of_mint (asCoreConfig C) mint)
  apply CertifiedRGACoreExecution.represented_of_canonical Γ C.replayContext honest
    (by simpa only [asCoreConfig] using nativeInsertOnly_of_mint Γ (asCoreConfig C) mint)
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl H s
    (fun e he => good.version_events_supported v s H hv e he)
    (good.version_events_causal v s H hv)
  simpa only [richRc] using good.canonical v s H hv

#print axioms canonicalConfig
#print axioms representedVersions
end Rich

#print axioms canonicalConfig
end Sal.MRDTs.Paper1.CertifiedRGACoreExecution
