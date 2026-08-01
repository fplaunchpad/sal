import Sal.Emulation.Conditioned_Trace_TS
import Sal.Emulation.Operational_Progress

/-!
# Snapshot network envelope for conditioned MRDTs

Liittschwager's state-based system sends immutable state snapshots.  A direct
`Step3V.merge target sender` is not equivalent: by delivery time the sender's
head may include later updates.  The envelope below buffers version ids, whose
states and event sets are immutable in the conditioned version store, and
delivers exactly the version that was broadcast.

The core remains Sal's conditioned configuration.  This module only supplies
network state and transition shape; the corresponding preservation theorem is
proved separately so the existing `Step3V` metatheory is not weakened.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs

/-- A packet carries the immutable version that existed at send time. -/
abbrev SnapshotPacket := Replica × Version

structure ConditionedNetworkConfig (D : ConditionedMRDTSig) where
  core : Sal.ConditionedMRDTs.Configuration D
  inFlight : Set SnapshotPacket

/-- Initial network state: the verified conditioned core and no packets. -/
def conditionedNetworkInit (D : ConditionedMRDTSig) (hInit : D.Inv D.init) :
    ConditionedNetworkConfig D where
  core := Sal.ConditionedMRDTs.initConfig D hInit
  inFlight := ∅

/-- Delivering a historical snapshot is the virtual-LCA merge rule with the
second input obtained directly from the immutable version store instead of a
sender's current head. -/
inductive SnapshotMerge (D : ConditionedMRDTSig) :
    Sal.ConditionedMRDTs.Configuration D → Replica → Version →
      Sal.ConditionedMRDTs.Configuration D → Prop where
  | step {C : Sal.ConditionedMRDTs.Configuration D} {target : Replica}
      {vTarget vSnapshot vNew : Version} {sTarget sSnapshot : D.State}
      {eTarget eSnapshot : Set (Op D.AppOp)}
      (hHead : C.head target = some vTarget)
      (hTarget : C.ver vTarget = some (sTarget, eTarget))
      (hSnapshot : C.ver vSnapshot = some (sSnapshot, eSnapshot))
      (hFresh : C.ver vNew = none)
      (hRankTarget : vTarget < vNew) (hRankSnapshot : vSnapshot < vNew)
      (C' : Sal.ConditionedMRDTs.Configuration D)
      (hN : C'.N = updateRep C.N target
        (D.mergeL (virtualLCAState C vTarget vSnapshot) sTarget sSnapshot))
      (hL : C'.L = updateRep C.L target (eTarget ∪ eSnapshot))
      (hvis : C'.vis = C.vis)
      (hver : C'.ver = fun w => if w = vNew then
        some (D.mergeL (virtualLCAState C vTarget vSnapshot)
          sTarget sSnapshot, eTarget ∪ eSnapshot) else C.ver w)
      (hhead : C'.head = fun r => if r = target then some vNew else C.head r)
      (hparents : C'.parents = fun w =>
        if w = vNew then [vTarget, vSnapshot] else C.parents w) :
      SnapshotMerge D C target vSnapshot C'

theorem SnapshotMerge.storeInv {D : ConditionedMRDTSig}
    {C C' : Sal.ConditionedMRDTs.Configuration D}
    {target : Replica} {snapshot : Version}
    (hstep : SnapshotMerge D C target snapshot C')
    (hInv : StoreInv C.ver C.parents) : StoreInv C'.ver C'.parents := by
  cases hstep with
  | step hHead hTarget hSnapshot hFresh hRankTarget hRankSnapshot C'
      hN hL hvis hver hhead hparents =>
      rename_i vTarget vNew sTarget sSnapshot eTarget eSnapshot
      exact storeInv_merge_extend
        (sm := D.mergeL (virtualLCAState C vTarget snapshot)
          sTarget sSnapshot)
        hInv hFresh hTarget hSnapshot
        (by rw [hver]; simp)
        (fun w hw => by rw [hver]; simp [hw])
        (by rw [hparents]; simp)
        (fun w hw => by rw [hparents]; simp [hw])

theorem SnapshotMerge.goodConfig {D : ConditionedMRDTSig}
    {C C' : Sal.ConditionedMRDTs.Configuration D}
    {target : Replica} {snapshot : Version}
    (hJoin : JoinLemma3At D (Sal.ConditionedMRDTs.Configuration.core C))
    (hStore : StoreInv C.ver C.parents) (hGood : GoodConfig3 C)
    (hstep : SnapshotMerge D C target snapshot C') : GoodConfig3 C' := by
  cases hstep with
  | step hHead hTarget hSnapshot hFresh hRankTarget hRankSnapshot C'
      hN hL hvis hver hhead hparents =>
      exact goodConfig3_mergeVirtual_at hJoin hStore hHead hTarget hSnapshot
        hL hvis hver hGood

/-- Network transitions over the conditioned core. Updates broadcast their
new immutable version to an arbitrary recipient set; delivery consumes one
packet. Replica creation and queries do not alter the network buffer. -/
inductive ConditionedNetworkStep (D : ConditionedMRDTSig)
    (Honest : Sal.ConditionedMRDTs.Configuration D → Prop) :
    ConditionedNetworkConfig D → Label3 D →
      ConditionedNetworkConfig D → Prop where
  | createReplica {C C' : ConditionedNetworkConfig D} {r : Replica}
      (hHonest : Honest C.core)
      (hstep : Step3V D C.core (.createReplica r) C'.core)
      (hbuf : C'.inFlight = C.inFlight) :
      ConditionedNetworkStep D Honest C (.createReplica r) C'
  | update {C C' : ConditionedNetworkConfig D}
      {t : Timestamp} {r : Replica} {op : D.AppOp} {vNew : Version}
      (hHonest : Honest C.core)
      (hstep : Step3V D C.core (.apply t r op) C'.core)
      (hHead : C'.core.head r = some vNew)
      (recipients : Set Replica)
      (hbuf : C'.inFlight = C.inFlight ∪
        {packet | packet.2 = vNew ∧ packet.1 ∈ recipients ∧ packet.1 ≠ r}) :
      ConditionedNetworkStep D Honest C (.apply t r op) C'
  | deliver {C C' : ConditionedNetworkConfig D}
      {target : Replica} {snapshot : Version}
      (hHonest : Honest C.core)
      (hin : (target, snapshot) ∈ C.inFlight)
      (hstep : SnapshotMerge D C.core target snapshot C'.core)
      (hbuf : C'.inFlight = C.inFlight \ {(target, snapshot)}) :
      ConditionedNetworkStep D Honest C (.merge target target) C'
  | query {C : ConditionedNetworkConfig D} {r : Replica}
      {q : D.Query} {v : D.Value} {s : D.State}
      (hHonest : Honest C.core)
      (hs : C.core.N r = some s) (hv : v = D.query s q) :
      ConditionedNetworkStep D Honest C (.query r q v) C

/-- Client observation of the snapshot-network system. Timestamp choice is
hidden; snapshot delivery and replica creation are τ. -/
def conditionedNetworkObservedTS (D : OpCRDTSig)
    {hb : D.Msg → D.Msg → Prop} (I : OperationalTransferInput D hb) :
    LabeledTS where
  State := ConditionedNetworkConfig (shapiroConditionedG D I.schedule)
  Label := ConditionedObsLabel D
  step := fun C ℓ C' => ∃ raw,
    ConditionedNetworkStep (shapiroConditionedG D I.schedule)
      (fun core => I.verified.Honest
        (Sal.ConditionedMRDTs.Configuration.core core)) C raw C' ∧
      observeConditionedLabel D raw = ℓ
  silent := ConditionedObsLabel.silent

def disciplinedOpToConditionedNetworkLabels (D : OpCRDTSig)
    {hb : D.Msg → D.Msg → Prop} (I : OperationalTransferInput D hb) :
    LabelMorphism (disciplinedOpLabeledTS D hb)
      (conditionedNetworkObservedTS D I) where
  map
    | .update r op => .update r op
    | .query r q v => .query r q v
    | .deliver _ _ => .internal
  silent_iff := by
    intro ℓ
    cases ℓ <;>
      simp [disciplinedOpLabeledTS, conditionedNetworkObservedTS,
        OpLabel.isSilent, ConditionedObsLabel.silent]

end Sal.Emulation
