import Sal.MRDTs.Framework.Certificates
import Sal.MRDTs.Metatheory.VirtualAdequacy

/-! Adequacy for datatype joins justified by the certified mint history at
each execution node. -/

namespace Sal.MRDTs

open Sal.Emulation

theorem goodConfig_of_mintCertified {D : MRDTSig} {G : GenerationContract D}
    (join : ∀ C, G.History C → JoinLemma3At D C.core)
    {C : Configuration D} (reach : MintCertifiedReach D G C) : GoodConfig3 C := by
  induction reach with
  | init => exact goodConfig3_init
  | @step C C' l _ mint step _ ih =>
      have hJoin := join C (G.history_of_mint C mint)
      cases step.toRaw with
      | createReplica fresh C' hN hL hvis hver hhead hparents =>
          exact goodConfig3_createReplica fresh hL hvis hver ih
      | apply hhead hver hfresh hstore hvnew hrank C' hN hL hvis hversions hheads hparents =>
          exact goodConfig3_apply hhead hver hfresh hvnew hL hvis hversions ih
      | merge hh₁ hh₂ hv₁ hv₂ hlca hvT hvm hr₁ hr₂ C' hN hL hvis hver hhead hparents =>
          exact goodConfig3_merge_at hJoin hh₁ hv₁ hv₂ hlca hvT hL hvis hver ih
      | query hs hv => exact ih

theorem ra_of_mintCertified {D : MRDTSig} {G : GenerationContract D}
    (join : ∀ C, G.History C → JoinLemma3At D C.core)
    {C : Configuration D} (reach : MintCertifiedReach D G C) :
    IsRALinearizableJoin C :=
  isRALinearizable3_of_good (goodConfig_of_mintCertified join reach)

theorem goodConfig_of_mintCertifiedV {D : MRDTSig} {G : GenerationContract D}
    (join : ∀ C, G.History C → JoinLemma3At D C.core)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualLCA D) G C) :
    GoodConfig3 C := by
  have h : StoreInv C.ver C.parents ∧ GoodConfig3 C := by
    induction reach with
    | init => exact ⟨storeInv_init, goodConfig3_init⟩
    | @step C C' l _ mint step _ ih =>
        have hJoin := join C (G.history_of_mint C mint)
        refine ⟨storeInv_stepV step.toRaw ih.1, ?_⟩
        cases step.toRaw with
        | base raw =>
            cases raw with
            | createReplica fresh C' hN hL hvis hver hhead hparents =>
                exact goodConfig3_createReplica fresh hL hvis hver ih.2
            | apply hhead hver hfresh hstore hvnew hrank C' hN hL hvis hversions hheads hparents =>
                exact goodConfig3_apply hhead hver hfresh hvnew hL hvis hversions ih.2
            | merge hh₁ hh₂ hv₁ hv₂ hlca hvT hvm hr₁ hr₂ C' hN hL hvis hver hhead hparents =>
                exact goodConfig3_merge_at hJoin hh₁ hv₁ hv₂ hlca hvT hL hvis hver ih.2
            | query hs hv => exact ih.2
        | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hN hL hvis hver hhead hparents =>
            exact goodConfig3_mergeVirtual_at hJoin ih.1 hh₁ hv₁ hv₂ hL hvis hver ih.2
  exact h.2

theorem ra_of_mintCertifiedV {D : MRDTSig} {G : GenerationContract D}
    (join : ∀ C, G.History C → JoinLemma3At D C.core)
    {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualLCA D) G C) :
    IsRALinearizableJoin C :=
  isRALinearizable3_of_good (goodConfig_of_mintCertifiedV join reach)

end Sal.MRDTs
