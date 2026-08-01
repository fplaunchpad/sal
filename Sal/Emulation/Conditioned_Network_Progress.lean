import Sal.Emulation.Conditioned_Network_TS

/-!
# Constructive progress for the conditioned snapshot network

Core `Step3V` progress and network progress are separate obligations.  The
network layer must choose the immutable version produced by an update and must
construct a historical `SnapshotMerge` successor on delivery.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs LabeledTS

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

structure ConditionedNetworkProgress (I : OperationalTransferInput D hb) where
  CanUpdate : ConditionedNetworkConfig (shapiroConditionedG D I.schedule) →
    Replica → D.AppOp → Prop
  CanDeliver : ConditionedNetworkConfig (shapiroConditionedG D I.schedule) →
    Replica → Version → Prop
  update : ∀ {C r op}, CanUpdate C r op → ∀ recipients : Set Replica,
    ∃ t vNew C',
      ConditionedNetworkStep (shapiroConditionedG D I.schedule)
        (fun core => I.verified.Honest
          (Sal.ConditionedMRDTs.Configuration.core core))
        C (.apply t r op) C' ∧
      C'.core.head r = some vNew ∧
      C'.inFlight = C.inFlight ∪
        {packet | packet.2 = vNew ∧ packet.1 ∈ recipients ∧ packet.1 ≠ r}
  deliver : ∀ {C target snapshot}, CanDeliver C target snapshot →
    ∃ C', ConditionedNetworkStep (shapiroConditionedG D I.schedule)
      (fun core => I.verified.Honest
        (Sal.ConditionedMRDTs.Configuration.core core))
      C (.merge target target) C'

namespace ConditionedNetworkProgress

theorem updateWeak (P : ConditionedNetworkProgress I)
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {r : Replica} {op : D.AppOp} (h : P.CanUpdate C r op)
    (recipients : Set Replica) :
    ∃ C', (conditionedNetworkObservedTS D I).weakStep C (.update r op) C' := by
  obtain ⟨t, vNew, C', hstep, hhead, hbuffer⟩ := P.update h recipients
  refine ⟨C', WeakSimM.weakStep_of_step ?_⟩
  exact ⟨.apply t r op, hstep, rfl⟩

theorem deliverWeak (P : ConditionedNetworkProgress I)
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {target : Replica} {snapshot : Version}
    (h : P.CanDeliver C target snapshot) :
    ∃ C', (conditionedNetworkObservedTS D I).weakStep C .internal C' := by
  obtain ⟨C', hstep⟩ := P.deliver h
  refine ⟨C', WeakSimM.weakStep_of_step ?_⟩
  exact ⟨.merge target target, hstep, rfl⟩

theorem queryWeak (I : OperationalTransferInput D hb)
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {r : Replica} {q : D.Query} {x : EmulatorState D}
    (hHonest : I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core C.core))
    (hx : C.core.N r = some x) :
    (conditionedNetworkObservedTS D I).weakStep C
      (.query r q (D.query x.materialized q)) C := by
  apply WeakSimM.weakStep_of_step
  exact ⟨.query r q (D.query x.materialized q),
    .query hHonest hx rfl, rfl⟩

end ConditionedNetworkProgress

end Sal.Emulation
