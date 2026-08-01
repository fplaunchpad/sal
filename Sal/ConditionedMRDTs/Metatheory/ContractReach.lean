import Sal.ConditionedMRDTs.Metatheory.HonestReach

/-! Migration adapters for the generic contract-indexed reachability core. -/

namespace Sal.ConditionedMRDTs

variable {D : ConditionedMRDTSig} {H : Configuration D → Prop}
  {hInit : D.Inv D.init}

abbrev ContractReach3 (D : ConditionedMRDTSig) (H : Configuration D → Prop)
    (hInit : D.Inv D.init) : Configuration D → Prop :=
  ContractReach (initConfig D hInit) (Step3 D) H

abbrev ContractReach3V (D : ConditionedMRDTSig) (H : Configuration D → Prop)
    (hInit : D.Inv D.init) : Configuration D → Prop :=
  ContractReach (initConfig D hInit) (Step3V D) H

theorem contractReach3_of_honestReach {C : Configuration D}
    (h : HonestReach D H hInit C) : ContractReach3 D H hInit C := h

theorem honestReach_of_contractReach3 {C : Configuration D}
    (h : ContractReach3 D H hInit C) : HonestReach D H hInit C := h

theorem contractReach3_iff_honestReach {C : Configuration D} :
    ContractReach3 D H hInit C ↔ HonestReach D H hInit C :=
  ⟨honestReach_of_contractReach3, contractReach3_of_honestReach⟩

theorem contractReach3V_of_honestReachV {C : Configuration D}
    (h : HonestReachV D H hInit C) : ContractReach3V D H hInit C := h

theorem honestReachV_of_contractReach3V {C : Configuration D}
    (h : ContractReach3V D H hInit C) : HonestReachV D H hInit C := h

theorem contractReach3V_iff_honestReachV {C : Configuration D} :
    ContractReach3V D H hInit C ↔ HonestReachV D H hInit C :=
  ⟨honestReachV_of_contractReach3V, contractReach3V_of_honestReachV⟩

end Sal.ConditionedMRDTs
