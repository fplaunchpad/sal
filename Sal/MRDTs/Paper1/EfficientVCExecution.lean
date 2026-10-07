import Sal.MRDTs.Paper1.VCExecutionContract
import Sal.MRDTs.Paper1.EfficientVCVirtual

/-! All stored-version and scratch-state merge nodes in this certificate use
VC-derived Join. Local issuance and context-transport lemmas are reused from
the production execution model. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
local instance : ReplayPolicy (D α).toUpdateSig := rc

theorem vcRepresentedConfig {C : Configuration (D α)}
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
        have hm := vcHistoryMerge hG _ _ _ _ _
          (version_enumerated hG hv₁) (version_enumerated hG hv₂)
          (hG.version_events_supported _ _ _ hv₁) (hG.version_events_supported _ _ _ hv₂)
          (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
          hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
        exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
          (canonical_union hG hv₁ hv₂ hm),repConfig_store hvis hver hR hm⟩
      | query hs hv => exact ⟨hG,hR⟩
    | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
      have hL := Configuration.headEvents_update_of_store_head_update _ _ hvm hver hhead
      have hT := vcVirtualMergeBaseStateRepresents hSI hG hR hv₁ hv₂
      have hm := vcHistoryMerge hG _ _ _ _ _
          (version_enumerated hG hv₁) (version_enumerated hG hv₂)
          (hG.version_events_supported _ _ _ hv₁) (hG.version_events_supported _ _ _ hv₂)
        (hG.version_events_causal _ _ _ hv₁) (hG.version_events_causal _ _ _ hv₂)
        hT (hR _ _ _ hv₁) (hR _ _ _ hv₂)
      exact ⟨canonicalConfig_merge_result hh₁ hv₁ hv₂ hL hvis hver hG
        (canonical_union hG hv₁ hv₂ hm),repConfig_store hvis hver hR hm⟩

theorem vcRepresentedVersions {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    ∀ v s E, C.ver v = some (s,E) → representation C.replayContext E s := by
  obtain ⟨_,good,represented⟩ := vcRepresentedConfig reach
  intro v s E hv
  obtain ⟨π,hp,_⟩ := good.canonical v s E hv
  exact ⟨represented v s E hv,⟨π,hp⟩,
    good.version_events_supported v s E hv,
    (fun _ _ _ h k => good.vis_trans h k),(fun _ _ h => C.causal_mono h)⟩

def vcConditions : AbstractMRDT.VCConditions (model (α := α)) (EventSpec.conflict α)
    (EventSpec.spec α) issuance where
  representation := representation
  scheme C := AbstractMRDT.MetadataDependencies.ofConcrete (model (α := α)) C
  queryComplete := AbstractMRDT.ofQuery_complete QuerySpec.abstraction
  laws := laws
  vcs := mergeVCs
  canonical := representsCanonical
  substitute := metadataSubstitution
  initial := initialMetadata
  initMetadata := initMetadata
  symmetry := mergeCommMetadata
  causal := causalMetadata
  localMetadata := localMetadata
  sharedMetadata := sharedMetadata
  replaySupply := fun C _ _ _ _ trans irrefl _ _ ha _ => replaySupply C trans irrefl ha.2.2.2.2
  representedVersions _ := vcRepresentedVersions
  compatibility := compatibility
  historySound := EventSpec.foldHistorySound

def vcCertificate : AbstractMRDT.Certificate (model (α := α)) (EventSpec.conflict α)
    (EventSpec.spec α) issuance := vcConditions.toCertificate

theorem vcCertifiedVersionsRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    AbstractMRDT.VersionsRALinearizable (model (α := α)) (EventSpec.conflict α) (EventSpec.spec α) C :=
  vcCertificate.versionsV reach

theorem vcCertifiedExecutionsV (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTSV (D α) issuance).Execution (initConfig (D α)) trace) :
    AbstractMRDT.ExecutionCorrect (model (α := α)) (EventSpec.conflict α) (EventSpec.spec α) trace :=
  vcCertificate.executionsV trace execution

theorem vcCertifiedExecutions (trace : List (Label (D α) × Configuration (D α)))
    (execution : (certifiedTS (D α) issuance).Execution (initConfig (D α)) trace) :
    AbstractMRDT.ExecutionCorrect (model (α := α)) (EventSpec.conflict α) (EventSpec.spec α) trace :=
  vcCertificate.executions trace execution

end Sal.MRDTs.Paper1.EfficientORSet.AbstractSpec
