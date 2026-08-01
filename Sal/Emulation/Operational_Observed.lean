import Sal.Emulation.Conditioned_Trace_TS
import Sal.Emulation.Operational_Progress

/-! Operational-progress certificates exposed as weak steps of the client LTS. -/

namespace Sal.Emulation

open Sal.ConditionedMRDTs LabeledTS

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

namespace OperationalTransferInput

theorem applyWeak (I : OperationalTransferInput D hb)
    {C : Sal.ConditionedMRDTs.Configuration
      (shapiroConditionedG D I.schedule)} {r : Replica} {op : D.AppOp}
    (hHonest : I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core C))
    (henabled : I.progress.CanApply C r op) :
    ∃ C', (honestConditionedObservedTSV I.semantic).weakStep C
      (.update r op) C' := by
  obtain ⟨t, C', hstep⟩ := I.progress.apply hHonest henabled
  refine ⟨C', WeakSimM.weakStep_of_step ?_⟩
  exact ⟨hHonest, ⟨.apply t r op, hstep, rfl⟩⟩

theorem mergeWeak (I : OperationalTransferInput D hb)
    {C : Sal.ConditionedMRDTs.Configuration
      (shapiroConditionedG D I.schedule)} {target source : Replica}
    (hHonest : I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core C))
    (henabled : I.progress.CanMerge C target source) :
    ∃ C', (honestConditionedObservedTSV I.semantic).weakStep C
      .internal C' := by
  obtain ⟨C', hstep⟩ := I.progress.merge hHonest henabled
  refine ⟨C', WeakSimM.weakStep_of_step ?_⟩
  exact ⟨hHonest, ⟨.merge target source, hstep, rfl⟩⟩

theorem queryWeak (I : OperationalTransferInput D hb)
    {C : Sal.ConditionedMRDTs.Configuration
      (shapiroConditionedG D I.schedule)} {r : Replica} {q : D.Query}
    {x : EmulatorState D}
    (hHonest : I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core C))
    (hx : C.N r = some x) :
    (honestConditionedObservedTSV I.semantic).weakStep C
      (.query r q (D.query x.materialized q)) C := by
  apply WeakSimM.weakStep_of_step
  exact ⟨hHonest, ⟨.query r q (D.query x.materialized q),
    ConditionedOperationalProgress.query hx, rfl⟩⟩

end OperationalTransferInput

end Sal.Emulation
