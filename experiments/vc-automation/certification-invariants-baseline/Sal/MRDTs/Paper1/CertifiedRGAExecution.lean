import Sal.MRDTs.Paper1.CertifiedClosedExecution
import Sal.MRDTs.Paper1.CertifiedRGAVC
import Sal.MRDTs.Paper1.CertifiedRGASidedVC

/-! Raw VC-derived closed-history merge preservation. The old event-policy
canonical interface is used only as a structural execution invariant; its
states are reconstructed as full-causal replays using update-only lemmas. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAExecution
open Foundation Sal.EmbedRGA
namespace Embedded
open Instances.EmbedRGA CertifiedRGAVCReplay.Embedded
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem represented_of_canonical (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (H : Set (Op (EOp α))) (s : EState α) (support : H ⊆ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (canonical : IsCanonicalState C H s) : representation Γ C H s := by
  obtain ⟨xs,perm,order,fold⟩ := canonical
  obtain ⟨t,rep⟩ := supply Γ C honest trans irrefl H xs perm support
  obtain ⟨ys,py,ry,fy⟩ := rep.2.2.2.2
  have wx := e_wf_of_enum honest support (fun a b vis _ hb => closed a b vis hb) perm order
  have wy := wellformed_supported Γ C honest ys py.1 (fun e he => support ((py.2 e).mp he)) ry
  have same : t = s := fy.symm.trans ((e_fold_canon Γ wy wx
    (fun e => (py.2 e).trans (perm.2 e).symm)).trans fold)
  simpa only [same] using rep

theorem canonical_of_represented (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (H : Set (Op (EOp α))) (s : EState α)
    (rep : representation Γ C H s) : IsCanonicalState C H s := by
  obtain ⟨xs,perm,order,fold⟩ := rep.2.2.2.2
  refine ⟨xs,perm,?_,fold⟩
  apply order.imp_of_mem
  intro a b ha hb notvis edge
  rcases edge with causal | concurrent
  · exact notvis causal.1
  · exact notvis (e_vis_of_rc_of_honest rep.1
      (rep.2.2.2.1 ((perm.2 a).mp ha)) (rep.2.2.2.1 ((perm.2 b).mp hb)) concurrent.2.2.1)

theorem merge_canonical (Γ : OrderedPrefixCode)
    (C : ReplayContext (E Γ α).toUpdateSig) (honest : EHonestCore Γ C)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (A B : Set (Op (EOp α))) (l a b : EState α)
    (supA : A ⊆ C.events) (supB : B ⊆ C.events)
    (closedA : ∀ x y, C.vis x y → y ∈ A → x ∈ A)
    (closedB : ∀ x y, C.vis x y → y ∈ B → x ∈ B)
    (hl : IsCanonicalState C (A ∩ B) l)
    (ha : IsCanonicalState C A a) (hb : IsCanonicalState C B b) :
    IsCanonicalState C (A ∪ B) (eMerge l a b) := by
  apply canonical_of_represented
  exact CertifiedRGAVC.Embedded.representationJoin Γ C A B l a b trans irrefl
    supA supB closedA closedB
    (represented_of_canonical Γ C honest trans irrefl _ _ (fun x hx => supA hx.1)
      (fun x y vis hy => ⟨closedA x y vis hy.1,closedB x y vis hy.2⟩) hl)
    (represented_of_canonical Γ C honest trans irrefl _ _ supA closedA ha)
    (represented_of_canonical Γ C honest trans irrefl _ _ supB closedB hb)

theorem closedJoinAt (Γ : OrderedPrefixCode) (C : Configuration (E Γ α))
    (mint : MintHonest (E Γ α) (generation Γ).CanIssue C) :
    CertifiedClosedExecution.ClosedJoinAt (E Γ α) C.replayContext := by
  intro A B l a b trans irrefl supA supB closedA closedB hl ha hb
  exact merge_canonical Γ C.replayContext (eHonest_core (eHonest_of_mint mint))
    (fun _ _ _ h k => trans h k) irrefl A B l a b supA supB closedA closedB hl ha hb

theorem canonicalConfig (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C) : CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_execution (closedJoinAt Γ) execution

theorem representedVersions (Γ : OrderedPrefixCode) {C : Configuration (E Γ α)}
    (execution : CertifiedExecution (E Γ α) (generation Γ) C)
    {v : Version} {s : EState α} {H : Set (Op (EOp α))}
    (hv : C.ver v = some (s,H)) : representation Γ C.replayContext H s := by
  have good := canonicalConfig Γ execution
  exact represented_of_canonical Γ C.replayContext
    (eHonest_core (eHonest_of_mint execution.mintHonest))
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl H s
    (fun e he => good.version_events_supported v s H hv e he)
    (good.version_events_causal v s H hv) (good.canonical v s H hv)

end Embedded
namespace Sided
open Instances.SidedEmbedRGA CertifiedRGAVCReplay.Sided

theorem represented_of_canonical (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (H : Set (Op (SOp))) (s : SState) (support : H ⊆ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (canonical : IsCanonicalState C H s) : representation Γ C H s := by
  obtain ⟨xs,perm,order,fold⟩ := canonical
  obtain ⟨t,rep⟩ := supply Γ C honest trans irrefl H xs perm support
  obtain ⟨ys,py,ry,fy⟩ := rep.2.2.2.2
  have wx := s_wf_of_enum honest support (fun a b vis _ hb => closed a b vis hb) perm order
  have wy := wellformed_supported Γ C honest ys py.1 (fun e he => support ((py.2 e).mp he)) ry
  have same : t = s := fy.symm.trans ((s_fold_canon Γ wy wx
    (fun e => (py.2 e).trans (perm.2 e).symm)).trans fold)
  simpa only [same] using rep

theorem canonical_of_represented (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (H : Set (Op (SOp))) (s : SState)
    (rep : representation Γ C H s) : IsCanonicalState C H s := by
  obtain ⟨xs,perm,order,fold⟩ := rep.2.2.2.2
  refine ⟨xs,perm,?_,fold⟩
  apply order.imp_of_mem
  intro a b ha hb notvis edge
  rcases edge with causal | concurrent
  · exact notvis causal.1
  · exact notvis (s_vis_of_rc_of_honest rep.1
      (rep.2.2.2.1 ((perm.2 a).mp ha)) (rep.2.2.2.1 ((perm.2 b).mp hb)) concurrent.2.2.1)

theorem merge_canonical (Γ : OrderedPrefixCode)
    (C : ReplayContext (S Γ).toUpdateSig) (honest : SHonestCore Γ C)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (A B : Set (Op (SOp))) (l a b : SState)
    (supA : A ⊆ C.events) (supB : B ⊆ C.events)
    (closedA : ∀ x y, C.vis x y → y ∈ A → x ∈ A)
    (closedB : ∀ x y, C.vis x y → y ∈ B → x ∈ B)
    (hl : IsCanonicalState C (A ∩ B) l)
    (ha : IsCanonicalState C A a) (hb : IsCanonicalState C B b) :
    IsCanonicalState C (A ∪ B) (sMerge l a b) := by
  apply canonical_of_represented
  exact CertifiedRGAVC.Sided.representationJoin Γ C A B l a b trans irrefl
    supA supB closedA closedB
    (represented_of_canonical Γ C honest trans irrefl _ _ (fun x hx => supA hx.1)
      (fun x y vis hy => ⟨closedA x y vis hy.1,closedB x y vis hy.2⟩) hl)
    (represented_of_canonical Γ C honest trans irrefl _ _ supA closedA ha)
    (represented_of_canonical Γ C honest trans irrefl _ _ supB closedB hb)

theorem closedJoinAt (Γ : OrderedPrefixCode) (C : Configuration (S Γ))
    (mint : MintHonest (S Γ) (generation Γ).CanIssue C) :
    CertifiedClosedExecution.ClosedJoinAt (S Γ) C.replayContext := by
  intro A B l a b trans irrefl supA supB closedA closedB hl ha hb
  exact merge_canonical Γ C.replayContext (sHonest_core (sHonest_of_mint mint))
    (fun _ _ _ h k => trans h k) irrefl A B l a b supA supB closedA closedB hl ha hb

theorem canonicalConfig (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C) : CanonicalConfig C :=
  CertifiedClosedExecution.canonicalConfig_of_execution (closedJoinAt Γ) execution

theorem representedVersions (Γ : OrderedPrefixCode) {C : Configuration (S Γ)}
    (execution : CertifiedExecution (S Γ) (generation Γ) C)
    {v : Version} {s : SState} {H : Set (Op (SOp))}
    (hv : C.ver v = some (s,H)) : representation Γ C.replayContext H s := by
  have good := canonicalConfig Γ execution
  exact represented_of_canonical Γ C.replayContext
    (sHonest_core (sHonest_of_mint execution.mintHonest))
    (fun _ _ _ h k => good.vis_trans h k) good.vis_irrefl H s
    (fun e he => good.version_events_supported v s H hv e he)
    (good.version_events_causal v s H hv) (good.canonical v s H hv)

end Sided
end Sal.MRDTs.Paper1.CertifiedRGAExecution
