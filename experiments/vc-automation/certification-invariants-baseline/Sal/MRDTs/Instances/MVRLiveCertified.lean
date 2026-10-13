import Sal.MRDTs.Instances.MVRLiveVirtual
import Sal.MRDTs.Metatheory.AdequacyResult
import Sal.MRDTs.Metatheory.CertifiedAdequacy

namespace Sal.MRDTs.Instances.MVRLive
open Sal.MRDTs.Foundation
open Classical
local instance : ReplayPolicy D.toUpdateSig := rc
set_option maxHeartbeats 1000000

theorem repConfig_init : RepConfig (initConfig D) := by
  intro v s E hv
  change (if v = 0 then some (D.init,∅) else none) = some (s,E) at hv
  split at hv
  · cases Option.some.inj hv
    exact represents_empty
  · cases hv

theorem repConfig_store {C C' : Configuration D}
    {v : Version} {s : State} {E : Set Event}
    (hver : C'.ver = fun w => if w = v then some (s,E) else C.ver w)
    (hR : RepConfig C) (hs : Represents E s) : RepConfig C' := by
  intro w sw Ew hw
  rw [hver] at hw
  dsimp only at hw
  split at hw
  · cases Option.some.inj hw
    exact hs
  · exact hR w sw Ew hw

theorem repConfig_apply {C C' : Configuration D}
    {e : Event} {v vnew : Version} {s : State} {E : Set Event}
    (hver : C.ver v = some (s,E))
    (hstore : C'.ver = fun w => if w = vnew then some (update s e,E ∪ {e}) else C.ver w)
    (hfresh : ∀ a ∈ C.events, a.1 ≠ e.1)
    (hG : CanonicalConfig C) (hG' : CanonicalConfig C')
    (mint : MintHonest D issuance.CanIssue C)
    (after : MintHonest D issuance.CanIssue C') (hR : RepConfig C) : RepConfig C' := by
  apply repConfig_store hstore hR
  apply represents_update e (hR v s E hver)
  · intro b hb hn
    obtain ⟨a,ha,_,ht⟩ := issued_overwrite mint
      (hG.version_events_supported v s E hver b hb) hn
    exact hfresh a ha ht
  · intro hn
    have hvnew : C'.ver vnew = some (update s e,E ∪ {e}) := by rw [hstore]; simp
    have he := hG'.version_events_supported vnew _ _ hvnew e (by simp)
    exact (Nat.lt_irrefl _) (issued_overwrite_lt after he hn)

theorem canonical_union {C : Configuration D}
    (hG : CanonicalConfig C) (mint : MintHonest D issuance.CanIssue C)
    {v₁ v₂ : Version} {s₁ s₂ s : State} {E₁ E₂ : Set Event}
    (hv₁ : C.ver v₁ = some (s₁,E₁)) (hv₂ : C.ver v₂ = some (s₂,E₂))
    (hs : Represents (E₁ ∪ E₂) s) :
    IsCanonicalState C.replayContext (E₁ ∪ E₂) s := by
  obtain ⟨ops₁,hp₁,_⟩ := hG.canonical v₁ s₁ E₁ hv₁
  obtain ⟨ops₂,hp₂,_⟩ := hG.canonical v₂ s₂ E₂ hv₂
  apply canonical_of_represents C mint (E₁ ∪ E₂) _ (ops₁ ++ ops₂).dedup _ hs
  · intro e he
    rcases he with he | he
    · exact hG.version_events_supported v₁ s₁ E₁ hv₁ e he
    · exact hG.version_events_supported v₂ s₂ E₂ hv₂ e he
  · exact ⟨List.nodup_dedup _,fun a => by simp [hp₁.2 a,hp₂.2 a]⟩

theorem represented_of_mintCertifiedV {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) :
    StoreInv C.ver C.parents ∧ CanonicalConfig C ∧ RepConfig C := by
  induction reach with
  | init => exact ⟨storeInv_init,canonicalConfig_init,repConfig_init⟩
  | @step C C' l _ mint step after ih =>
    obtain ⟨hSI,hG,hR⟩ := ih
    refine ⟨storeInv_stepV step.toRaw hSI,?_⟩
    cases step.toRaw with
    | base raw =>
      cases raw with
      | fork fresh sourceHead sourceVersion freshVersion rank C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ freshVersion hver hhead
        exact ⟨canonicalConfig_fork fresh sourceHead sourceVersion hL hvis hver hG,
          repConfig_store hver hR (hR _ _ _ sourceVersion)⟩
      | apply hhead hver hfresh hstore hvnew hrank C' hvis hversions hheads hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvnew hversions hheads
        have hG' := canonicalConfig_apply hhead hver hfresh hL hvis hversions hG
        exact ⟨hG',repConfig_apply hver hversions (fun a ha => hfresh a ha) hG hG' mint after hR⟩
      | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hvm hr₁ hr₂ C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
        have hT := hR _ _ _ hvT
        rw [C.gca_events hgca hv₁ hv₂ hvT] at hT
        have hm := represents_merge C mint _ _
          (fun e he => hG.version_events_supported _ _ _ hv₁ e he)
          (fun e he => hG.version_events_supported _ _ _ hv₂ e he)
          (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
          hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
        exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
          (canonical_union hG mint hv₁ hv₂ hm),repConfig_store hver hR hm⟩
      | query hs hv => exact ⟨hG,hR⟩
    | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
      have hT := virtualMergeBaseState_represents hSI hG hR mint hv₁ hv₂
      have hm := represents_merge C mint _ _
        (fun e he => hG.version_events_supported _ _ _ hv₁ e he)
        (fun e he => hG.version_events_supported _ _ _ hv₂ e he)
        (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
        hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
      exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
        (canonical_union hG mint hv₁ hv₂ hm),repConfig_store hver hR hm⟩

noncomputable def replayAdequacy : @ReplayAdequacyCertificate D issuance rc where
  soundV reach := hasReplayWitness_of_canonical (represented_of_mintCertifiedV reach).2.1

theorem represented_of_execution {C : Configuration D}
    (exec : CertifiedExecution D issuance C) : CanonicalConfig C ∧ RepConfig C := by
  cases exec with
  | ordinary h => exact (represented_of_mintCertifiedV h.toV).2
  | virtual h => exact (represented_of_mintCertifiedV h).2

end Sal.MRDTs.Instances.MVRLive
