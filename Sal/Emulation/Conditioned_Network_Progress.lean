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

structure NetworkUpdateResult (I : OperationalTransferInput D hb)
    (C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule))
    (r : Replica) (op : D.AppOp) (recipients : Set Replica) where
  time : Timestamp
  version : Version
  next : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)
  step : ConditionedNetworkStep (shapiroConditionedG D I.schedule)
    (fun core => I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core core))
    C (.apply time r op) next
  head : next.core.head r = some version
  buffer : next.inFlight = C.inFlight ∪
    {packet | packet.2 = version ∧ packet.1 ∈ recipients ∧ packet.1 ≠ r}
  honest : I.verified.Honest
    (Sal.ConditionedMRDTs.Configuration.core next.core)

structure NetworkDeliveryResult (I : OperationalTransferInput D hb)
    (C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule))
    (target : Replica) where
  next : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)
  step : ConditionedNetworkStep (shapiroConditionedG D I.schedule)
    (fun core => I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core core))
    C (.merge target target) next
  honest : I.verified.Honest
    (Sal.ConditionedMRDTs.Configuration.core next.core)

structure ConditionedNetworkProgress (I : OperationalTransferInput D hb) where
  CanUpdate : ConditionedNetworkConfig (shapiroConditionedG D I.schedule) →
    Replica → D.AppOp → Prop
  CanDeliver : ConditionedNetworkConfig (shapiroConditionedG D I.schedule) →
    Replica → Version → Prop
  update : ∀ {C r op}, CanUpdate C r op → ∀ recipients : Set Replica,
    NetworkUpdateResult I C r op recipients
  deliver : ∀ {C target snapshot}, CanDeliver C target snapshot →
    NetworkDeliveryResult I C target

namespace ConditionedNetworkProgress

theorem updateWeak (P : ConditionedNetworkProgress I)
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {r : Replica} {op : D.AppOp} (h : P.CanUpdate C r op)
    (recipients : Set Replica) :
    ∃ C', (conditionedNetworkObservedTS D I).weakStep C (.update r op) C' := by
  let R := P.update h recipients
  refine ⟨R.next, WeakSimM.weakStep_of_step ?_⟩
  exact ⟨.apply R.time r op, R.step, rfl⟩

theorem deliverWeak (P : ConditionedNetworkProgress I)
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {target : Replica} {snapshot : Version}
    (h : P.CanDeliver C target snapshot) :
    ∃ C', (conditionedNetworkObservedTS D I).weakStep C .internal C' := by
  let R := P.deliver h
  refine ⟨R.next, WeakSimM.weakStep_of_step ?_⟩
  exact ⟨.merge target target, R.step, rfl⟩

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
