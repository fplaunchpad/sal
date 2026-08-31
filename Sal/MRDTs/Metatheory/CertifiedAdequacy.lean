import Sal.MRDTs.Framework.Certificates
import Sal.MRDTs.Metatheory.VirtualAdequacy

/-! Adequacy for datatype joins justified by the certified mint history at
each execution node. -/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

theorem canonicalConfig_of_mintCertified {D : MRDTSig} {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → JoinAt D C.replayContext)
    {C : Configuration D} (reach : MintCertifiedReach D I C) : CanonicalConfig C := by
  induction reach with
  | init => exact canonicalConfig_init
  | @step C C' l _ mint step _ ih =>
      have hJoin := join C mint
      cases step.toRaw with
      | fork fresh sourceHead sourceVersion freshVersion rank C'
          hvis hver hhead hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ freshVersion hver hhead
          exact canonicalConfig_fork fresh sourceHead sourceVersion hL hvis hver ih
      | apply hhead hver hfresh hstore hvnew hrank C' hvis hversions hheads hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ hvnew hversions hheads
          exact canonicalConfig_apply hhead hver hfresh hL hvis hversions ih
      | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hvm hr₁ hr₂ C' hvis hver hhead hparents =>
          have hL := Configuration.headEvents_update_of_store_head_update
            _ _ hvm hver hhead
          exact canonicalConfig_merge_at hJoin hh₁ hv₁ hv₂ hgca hvT hL hvis hver ih
      | query hs hv => exact ih

theorem replayWitness_of_mintCertified {D : MRDTSig} {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → JoinAt D C.replayContext)
    {C : Configuration D} (reach : MintCertifiedReach D I C) :
    HasReplayWitness C :=
  hasReplayWitness_of_canonical (canonicalConfig_of_mintCertified join reach)

theorem canonicalConfig_of_mintCertifiedV {D : MRDTSig} {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → JoinAt D C.replayContext)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    CanonicalConfig C := by
  have h : StoreInv C.ver C.parents ∧ CanonicalConfig C := by
    induction reach with
    | init => exact ⟨storeInv_init, canonicalConfig_init⟩
    | @step C C' l _ mint step _ ih =>
        have hJoin := join C mint
        refine ⟨storeInv_stepV step.toRaw ih.1, ?_⟩
        cases step.toRaw with
        | base raw =>
            cases raw with
            | fork fresh sourceHead sourceVersion freshVersion rank C'
                hvis hver hhead hparents =>
                have hL := Configuration.headEvents_update_of_store_head_update
                  _ _ freshVersion hver hhead
                exact canonicalConfig_fork fresh sourceHead sourceVersion hL hvis hver ih.2
            | apply hhead hver hfresh hstore hvnew hrank C' hvis hversions hheads hparents =>
                have hL := Configuration.headEvents_update_of_store_head_update
                  _ _ hvnew hversions hheads
                exact canonicalConfig_apply hhead hver hfresh hL hvis hversions ih.2
            | merge hh₁ hh₂ hv₁ hv₂ hgca hvT hvm hr₁ hr₂ C' hvis hver hhead hparents =>
                have hL := Configuration.headEvents_update_of_store_head_update
                  _ _ hvm hver hhead
                exact canonicalConfig_merge_at hJoin hh₁ hv₁ hv₂ hgca hvT hL hvis hver ih.2
            | query hs hv => exact ih.2
        | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hvis hver hhead hparents =>
            have hL := Configuration.headEvents_update_of_store_head_update
              _ _ hvm hver hhead
            exact canonicalConfig_mergeVirtual_at hJoin ih.1 hh₁ hv₁ hv₂ hL hvis hver ih.2
  exact h.2

theorem replayWitness_of_mintCertifiedV {D : MRDTSig} {I : Issuance D}
    (join : ∀ C, MintHonest D I.CanIssue C → JoinAt D C.replayContext)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) I C) :
    HasReplayWitness C :=
  hasReplayWitness_of_canonical (canonicalConfig_of_mintCertifiedV join reach)

end Sal.MRDTs
