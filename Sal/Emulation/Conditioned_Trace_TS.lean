import Sal.Emulation.Conditioned_Emulation
import Sal.Emulation.Disciplined_Op_TS
import Sal.Emulation.Op_Based_TS
import Sal.Emulation.Transfer
import Sal.Emulation.Weak_Simulation

/-!
# Client observation of the conditioned ternary transition system

`labeledTS3` is the authoritative execution model for conditioned MRDTs, but
its raw labels expose fresh timestamps, replica creation, and state merges.
The operation-based system exposes only client updates and query responses;
message delivery is silent.  This file gives `labeledTS3` the corresponding
observation alphabet without changing its states or transition rules.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs

/-- Client observations shared by op-based and conditioned state-based
systems. `internal` represents network/topology administration and is τ. -/
inductive ConditionedObsLabel (D : OpCRDTSig) where
  | update (r : Replica) (op : D.AppOp)
  | query (r : Replica) (q : D.Query) (v : D.Value)
  | internal

def ConditionedObsLabel.silent {D : OpCRDTSig} :
    ConditionedObsLabel D → Prop
  | .internal => True
  | _ => False

/-- Erase fresh timestamps and hide replica creation / state merge. -/
def observeConditionedLabel (D : OpCRDTSig) {hb : D.Msg → D.Msg → Prop}
    {sched : CausalSchedule D hb} :
    Label3 (shapiroConditionedG D sched) → ConditionedObsLabel D
  | .createReplica _ => .internal
  | .apply _ r op => .update r op
  | .merge _ _ => .internal
  | .query r q v => .query r q v

/-- The exact conditioned `Step3` system viewed through client observations.
The existential raw label retains all timestamp and merge information needed
by the authoritative transition relation. -/
def conditionedObservedTS (D : OpCRDTSig) {hb : D.Msg → D.Msg → Prop}
    (sched : CausalSchedule D hb) : LabeledTS where
  State := Sal.ConditionedMRDTs.Configuration (shapiroConditionedG D sched)
  Label := ConditionedObsLabel D
  step := fun C ℓ C' => ∃ raw,
    Step3 (shapiroConditionedG D sched) C raw C' ∧
      observeConditionedLabel D raw = ℓ
  silent := ConditionedObsLabel.silent

/-- The certificate-scoped system used by transfer: only transitions from
configurations admitted by the datatype's declared honesty discipline occur.
This matches `HonestReach`, rather than silently widening the metatheorem to
arbitrary `Step3` executions. -/
def honestConditionedObservedTS {D : OpCRDTSig}
    {hb : D.Msg → D.Msg → Prop} (I : ConditionedTransferInput D hb) :
    LabeledTS where
  State := Sal.ConditionedMRDTs.Configuration
    (shapiroConditionedG D I.schedule)
  Label := ConditionedObsLabel D
  step := fun C ℓ C' =>
    I.verified.Honest (Sal.ConditionedMRDTs.Configuration.core C) ∧
    ∃ raw, Step3 (shapiroConditionedG D I.schedule) C raw C' ∧
      observeConditionedLabel D raw = ℓ
  silent := ConditionedObsLabel.silent

/-- Widened certificate-scoped target. This is the production transfer target:
virtual LCAs make state delivery total even after criss-cross synchronization,
while `VerifiedMRDT.ra_linearizableV` supplies the same RA guarantee. -/
def honestConditionedObservedTSV {D : OpCRDTSig}
    {hb : D.Msg → D.Msg → Prop} (I : ConditionedTransferInput D hb) :
    LabeledTS where
  State := Sal.ConditionedMRDTs.Configuration
    (shapiroConditionedG D I.schedule)
  Label := ConditionedObsLabel D
  step := fun C ℓ C' =>
    I.verified.Honest (Sal.ConditionedMRDTs.Configuration.core C) ∧
    ∃ raw, Step3V (shapiroConditionedG D I.schedule) C raw C' ∧
      observeConditionedLabel D raw = ℓ
  silent := ConditionedObsLabel.silent

/-- Operation labels map to the conditioned client alphabet. Causal message
delivery is matched by zero or more internal conditioned steps. -/
def opToConditionedLabels (D : OpCRDTSig)
    (hb : D.Msg → D.Msg → Prop) (sched : CausalSchedule D hb) :
    LabelMorphism (opLabeledTS D hb) (conditionedObservedTS D sched) where
  map
    | .update r op => .update r op
    | .query r q v => .query r q v
    | .deliver _ _ => .internal
  silent_iff := by
    intro ℓ
    cases ℓ <;>
      simp [opLabeledTS, conditionedObservedTS, OpLabel.isSilent,
        ConditionedObsLabel.silent]

/-- The same observation map for the honesty-restricted target system used by
the conditioned transfer theorem. -/
def opToHonestConditionedLabels {D : OpCRDTSig}
    {hb : D.Msg → D.Msg → Prop} (I : ConditionedTransferInput D hb) :
    LabelMorphism (opLabeledTS D hb) (honestConditionedObservedTS I) where
  map
    | .update r op => .update r op
    | .query r q v => .query r q v
    | .deliver _ _ => .internal
  silent_iff := by
    intro ℓ
    cases ℓ <;>
      simp [opLabeledTS, honestConditionedObservedTS, OpLabel.isSilent,
        ConditionedObsLabel.silent]

def opToHonestConditionedLabelsV {D : OpCRDTSig}
    {hb : D.Msg → D.Msg → Prop} (I : ConditionedTransferInput D hb) :
    LabelMorphism (opLabeledTS D hb) (honestConditionedObservedTSV I) where
  map
    | .update r op => .update r op
    | .query r q v => .query r q v
    | .deliver _ _ => .internal
  silent_iff := by
    intro ℓ
    cases ℓ <;>
      simp [opLabeledTS, honestConditionedObservedTSV, OpLabel.isSilent,
        ConditionedObsLabel.silent]

/-- Production label map from well-formed op executions. -/
def disciplinedOpToHonestConditionedLabelsV {D : OpCRDTSig}
    {hb : D.Msg → D.Msg → Prop} (I : ConditionedTransferInput D hb) :
    LabelMorphism (disciplinedOpLabeledTS D hb)
      (honestConditionedObservedTSV I) where
  map
    | .update r op => .update r op
    | .query r q v => .query r q v
    | .deliver _ _ => .internal
  silent_iff := by
    intro ℓ
    cases ℓ <;>
      simp [disciplinedOpLabeledTS, honestConditionedObservedTSV,
        OpLabel.isSilent, ConditionedObsLabel.silent]

end Sal.Emulation
