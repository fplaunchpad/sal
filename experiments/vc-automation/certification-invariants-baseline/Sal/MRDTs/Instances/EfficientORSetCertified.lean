import Sal.MRDTs.Instances.EfficientORSetVirtual
import Sal.MRDTs.Metatheory.AdequacyResult
import Sal.MRDTs.Metatheory.CertifiedAdequacy

namespace Sal.MRDTs.Instances.EfficientORSet
open Sal.MRDTs.Foundation
open Classical
variable {α : Type} [DecidableEq α]
local instance : ReplayPolicy (D α).toUpdateSig := rc

theorem repConfig_init : RepConfig (initConfig (D α)) := by
  intro v s E hv
  change (if v = 0 then some ((D α).init,∅) else none) = some (s,E) at hv
  split at hv
  · cases Option.some.inj hv
    exact represents_empty _
  · cases hv

theorem repConfig_store {C C' : Configuration (D α)}
    {v : Version} {s : State α} {E : Set (Event α)}
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = v then some (s,E) else C.ver w)
    (hR : RepConfig C) (hs : Represents C.vis E s) : RepConfig C' := by
  intro w sw Ew hw
  rw [hvis]
  rw [hver] at hw
  dsimp only at hw
  split at hw
  · cases Option.some.inj hw
    exact hs
  · exact hR w sw Ew hw

theorem repConfig_apply {C C' : Configuration (D α)}
    {e : Event α} {v vnew : Version} {s : State α} {E : Set (Event α)}
    (hver : C.ver v = some (s,E))
    (hf : e ∉ C.events)
    (hvis : C'.vis = fun a b => C.vis a b ∨ (a ∈ E ∧ b = e))
    (hstore : C'.ver = fun w => if w = vnew then some (update s e,E ∪ {e}) else C.ver w)
    (hG : CanonicalConfig C) (hR : RepConfig C) : RepConfig C' := by
  intro w sw Ew hw
  rw [hvis]
  rw [hstore] at hw
  dsimp only at hw
  split at hw
  · cases Option.some.inj hw
    apply represents_apply _ _ (hR v s E hver)
    · exact fun he => hf (hG.version_events_supported v s E hver e he)
    · intro b hv
      exact hf (C.vis_src hv)
  · apply represents_congr _ (hR w sw Ew hw)
    intro a b hb
    have hne : b ≠ e := by
      intro he; exact hf (he ▸ hG.version_events_supported w sw Ew hw b hb)
    simp [hne]

theorem canonical_union {C : Configuration (D α)}
    (hG : CanonicalConfig C)
    {v₁ v₂ : Version} {s₁ s₂ s : State α} {E₁ E₂ : Set (Event α)}
    (hv₁ : C.ver v₁ = some (s₁,E₁)) (hv₂ : C.ver v₂ = some (s₂,E₂))
    (hs : Represents C.vis (E₁ ∪ E₂) s) :
    IsCanonicalState C.replayContext (E₁ ∪ E₂) s := by
  obtain ⟨ops₁,hp₁,_⟩ := hG.canonical v₁ s₁ E₁ hv₁
  obtain ⟨ops₂,hp₂,_⟩ := hG.canonical v₂ s₂ E₂ hv₂
  have hsup : ∀ a ∈ E₁ ∪ E₂, a ∈ C.events := by
    intro a ha
    rcases ha with ha | ha
    · exact hG.version_events_supported v₁ s₁ E₁ hv₁ a ha
    · exact hG.version_events_supported v₂ s₂ E₂ hv₂ a ha
  apply canonical_of_represents C.replayContext (E₁ ∪ E₂) (fun _ _ _ hab hbc => hG.vis_trans hab hbc)
    (fun _ _ h => C.causal_mono h) _ (ops₁ ++ ops₂).dedup _ hs
  · intro a ha b hb hne hr
    obtain ⟨ra,sa,hsa,haa⟩ := hsup a ha
    obtain ⟨rb,sb,hsb,hbb⟩ := hsup b hb
    exact C.vis_total_same_replica hsa haa hsb hbb hne hr
  · exact ⟨List.nodup_dedup _,fun a => by simp [hp₁.2 a,hp₂.2 a]⟩

theorem represented_of_mintCertifiedV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    StoreInv C.ver C.parents ∧ CanonicalConfig C ∧ RepConfig C := by
  induction reach with
  | init => exact ⟨storeInv_init,canonicalConfig_init,repConfig_init⟩
  | @step C C' l _ mint step _ ih =>
    obtain ⟨hSI,hG,hR⟩ := ih
    refine ⟨storeInv_stepV step.toRaw hSI,?_⟩
    cases step.toRaw with
    | base raw =>
      cases raw with
      | fork fresh sourceHead sourceVersion freshVersion rank C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ freshVersion hver hhead
        exact ⟨canonicalConfig_fork fresh sourceHead sourceVersion hL hvis hver hG,
          repConfig_store hvis hver hR (hR _ _ _ sourceVersion)⟩
      | apply hhead hver hfresh hstore hvnew hrank C' hvis hversions hheads hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvnew hversions hheads
        refine ⟨canonicalConfig_apply hhead hver hfresh hL hvis hversions hG,?_⟩
        exact repConfig_apply hver (fun he => hfresh _ he rfl) hvis hversions hG hR
      | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hvm hr₁ hr₂ C' hvis hver hhead hparents =>
        have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
        have hT := hR _ _ _ hvT
        rw [C.gca_events hgca hv₁ hv₂ hvT] at hT
        have hm := represents_merge C.vis _ _
          (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
          hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
        exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
          (canonical_union hG hv₁ hv₂ hm),repConfig_store hvis hver hR hm⟩
      | query hs hv => exact ⟨hG,hR⟩
    | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
      have hT := virtualMergeBaseState_represents hSI hG hR hv₁ hv₂
      have hm := represents_merge C.vis _ _
        (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
        hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
      exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
        (canonical_union hG hv₁ hv₂ hm),repConfig_store hvis hver hR hm⟩

theorem keyUnique_reachableV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C)
    (v : Version) (s : State α) (E : Set (Event α)) (hv : C.ver v = some (s,E)) :
    KeyUnique s := by
  obtain ⟨_,hG,hR⟩ := represented_of_mintCertifiedV reach
  apply keyUnique_of_represents C.vis E _ (hR v s E hv)
  intro a ha b hb hne hr
  obtain ⟨ra,sa,hsa,haa⟩ := hG.version_events_supported v s E hv a ha
  obtain ⟨rb,sb,hsb,hbb⟩ := hG.version_events_supported v s E hv b hb
  exact C.vis_total_same_replica hsa haa hsb hbb hne hr

noncomputable def replayAdequacy : @ReplayAdequacyCertificate (D α) issuance rc where
  soundV reach := hasReplayWitness_of_canonical (represented_of_mintCertifiedV reach).2.1

noncomputable def verified : VerifiedMRDT (D α) where
  issuance := issuance
  rc := rc
  replayAdequacy := replayAdequacy
  Spec := spec
  Rel := stateRel
  sequentialCorrectness := sequentialCorrectness

#print axioms represented_of_mintCertifiedV
#print axioms verified
#print axioms keyUnique_reachableV
end Sal.MRDTs.Instances.EfficientORSet
