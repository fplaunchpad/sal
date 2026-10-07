import Sal.MRDTs.Paper1.CertifiedPrefixScope
import Sal.MRDTs.Paper1.CertifiedRGAScope

namespace Sal.MRDTs.Paper1.CertifiedRGAProducts
open Foundation Classical

/-- Supported causal prefixes project to supported causal prefixes. -/
theorem represented_proj₁ {D₁ D₂ : MRDTSig}
    (C : ReplayContext (prodSig D₁ D₂).toUpdateSig)
    (H : Set (Op (D₁.AppOp ⊕ D₂.AppOp))) (s : (prodSig D₁ D₂).State)
    (rep : CertifiedPrefixScope.represented (prodSig D₁ D₂) C H s) :
    CertifiedPrefixScope.represented D₁ (projReplayContext₁ C) (evRes₁ H) s.1 := by
  rcases rep with ⟨support,closed,xs,perm,ordered,fold⟩
  refine ⟨?_,?_,projList₁ xs,listPermOf_projList₁ perm,?_,?_⟩
  · intro a ha
    exact mem_projReplayContext₁_events.mpr (support ha)
  · intro a b vis hb
    exact closed (inlOp a) (inlOp b) vis hb
  · exact respects_projList₁_of (fun _ _ h => h) ordered
  · have h := congrArg Prod.fst fold
    simpa only [applySeq_prod] using h

/-- Component uniqueness plus a commuting auxiliary store gives concrete
product uniqueness; the proof invokes no product Join theorem. -/
theorem unique_product {D₁ D₂ : MRDTSig}
    (C : ReplayContext (prodSig D₁ D₂).toUpdateSig)
    (leftUnique : ∀ H s t,
      CertifiedPrefixScope.represented D₁ (projReplayContext₁ C) H s →
      CertifiedPrefixScope.represented D₁ (projReplayContext₁ C) H t → s = t)
    (commuting : ∀ a b, D₂.toUpdateSig.commutes a b) :
    ∀ H s t, CertifiedPrefixScope.represented (prodSig D₁ D₂) C H s →
      CertifiedPrefixScope.represented (prodSig D₁ D₂) C H t → s = t := by
  intro H s t hs ht
  apply Prod.ext
  · exact leftUnique _ _ _ (represented_proj₁ C H s hs) (represented_proj₁ C H t ht)
  · obtain ⟨xs,px,_,fx⟩ := hs.2.2
    obtain ⟨ys,py,_,fy⟩ := ht.2.2
    have qx := listPermOf_projList₂ px
    have qy := listPermOf_projList₂ py
    have perm := (List.perm_ext_iff_of_nodup qx.1 qy.1).mpr
      (fun o => (qx.2 o).trans (qy.2 o).symm)
    have eq := applySeq_perm_of_all_comm commuting perm D₂.init
    have fx' := congrArg Prod.snd fx
    have fy' := congrArg Prod.snd fy
    simp only [applySeq_prod] at fx' fy'
    exact fx'.symm.trans (eq.trans fy')

namespace SidedPeritext
open Instances.SidedPeritext Instances.SidedEmbedRGA
open Sal.EmbedRGA

theorem stores_commute (a b : Op Stores.AppOp) : Stores.toUpdateSig.commutes a b := by
  rcases a with ⟨ta,ra,oa | oa⟩ <;> rcases b with ⟨tb,rb,ob | ob⟩
  · exact commutes_prod_inl_of (D₂ := MarkStore) (Instances.FinsetStore.all_comm (ta,ra,oa) (tb,rb,ob))
  · exact commutes_prod_cross (D₁ := DeleteStore) (D₂ := MarkStore) (ta,ra,oa) (tb,rb,ob)
  · exact commutes_prod_cross' (D₁ := DeleteStore) (D₂ := MarkStore) (ta,ra,oa) (tb,rb,ob)
  · exact commutes_prod_inr_of (D₁ := DeleteStore) (Instances.FinsetStore.all_comm (ta,ra,oa) (tb,rb,ob))

theorem unique (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (honest : SHonestCore Γ (projReplayContext₁ C)) :
    ∀ H s t, CertifiedPrefixScope.represented (Core Γ) C H s →
      CertifiedPrefixScope.represented (Core Γ) C H t → s = t := by
  apply unique_product C _ stores_commute
  exact CertifiedRGAScope.Sided.unique Γ (projReplayContext₁ C) honest

theorem laws (Γ : OrderedPrefixCode) (C : ReplayContext (Core Γ).toUpdateSig)
    (honest : SHonestCore Γ (projReplayContext₁ C))
    (domain : ∀ a b, C.vis a b → a ∈ C.events) (P : OperationPolicy (Core Γ).AppOp) :
    CertifiedReplay.Laws (CertifiedPrefixScope.scope (Core Γ) C) P :=
  CertifiedPrefixScope.laws (Core Γ) C (unique Γ C honest) domain P

/-- RichCore has exactly Core's state, updates and merge. Its narrowed read
requires no abstraction of the replicated state. -/
theorem rich_laws (Γ : OrderedPrefixCode) (C : ReplayContext (RichCore Γ).toUpdateSig)
    (honest : SHonestCore Γ (projReplayContext₁ C))
    (domain : ∀ a b, C.vis a b → a ∈ C.events) (P : OperationPolicy (RichCore Γ).AppOp) :
    CertifiedReplay.Laws (CertifiedPrefixScope.scope (RichCore Γ) C) P :=
  laws Γ C honest domain P

end SidedPeritext
#print axioms SidedPeritext.laws
#print axioms SidedPeritext.rich_laws
end Sal.MRDTs.Paper1.CertifiedRGAProducts
