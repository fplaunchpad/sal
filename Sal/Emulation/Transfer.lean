import Sal.Emulation.Conditioned_Emulation
import Sal.Emulation.Weak_Simulation

/-!
# Operation-based RA-linearizability transfer

The transfer project now targets the corrected conditioned metatheory:

`OpCRDTSig → shapiroConditionedG → VerifiedMRDT → trace transfer`.

The old scaffold targeted `SatisfiesVCs` and concluded a predicate defined as
`True`; both have been retired.  This file instead defines the client-facing
claim as a universal property of the observable weak traces, connects a
conditioned `VerifiedMRDT` certificate to such a property through an explicit
trace realizer, and transports the result across label-morphic emulation.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs
open LabeledTS

/-- A sequential legality judgment for observable histories.  Concrete
operation-based datatypes instantiate this with their RA-linearization
relation (visibility/causality constraints and sequential return-value
legality); it is data, rather than the former `True` placeholder. -/
structure RATraceSpec (Label : Type) where
  linearizable : List Label → Prop

/-- Genuine trace-level RA-linearizability: every observable weak trace from
the distinguished initial state admits the datatype's RA linearization. -/
def OpBasedRALinearizable (T : LabeledTS) (init : T.State)
    (S : RATraceSpec T.Label) : Prop :=
  ∀ trace, trace ∈ T.weakTrace init → S.linearizable trace

/-- Pull a trace specification back along a label morphism. -/
def RATraceSpec.pullback {T₁ T₂ : LabeledTS} (μ : LabelMorphism T₁ T₂)
    (S : RATraceSpec T₂.Label) : RATraceSpec T₁.Label where
  linearizable trace := S.linearizable (trace.map μ.map)

/-- All datatype-specific semantic work required before trace transfer: a
conditioned certificate for the Shapiro emulator. -/
structure ConditionedTransferInput (D : OpCRDTSig)
    (hb : D.Msg → D.Msg → Prop) where
  schedule : CausalSchedule D hb
  verified : ShapiroVerified D schedule

namespace ConditionedTransferInput

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

theorem initInv (I : ConditionedTransferInput D hb) :
    (shapiroConditionedG D I.schedule).Inv
      (shapiroConditionedG D I.schedule).init :=
  I.verified.initInv

end ConditionedTransferInput

/-- The semantic bridge from the conditioned MRDT theorem to observable
system traces.  It records the nontrivial modeling fact that every target
trace is represented by an honestly reachable ternary configuration, and
that per-version `IsRALinearizable3` entails the chosen client trace
judgment.  Keeping these fields explicit prevents a generic emulation theorem
from silently assuming that the configuration and LTS semantics coincide. -/
structure ConditionedTraceBridge {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}
    (I : ConditionedTransferInput D hb) (T : LabeledTS) (init : T.State)
    (S : RATraceSpec T.Label) where
  realize : List T.Label → Sal.ConditionedMRDTs.Configuration
    (shapiroConditionedG D I.schedule)
  reachable : ∀ trace, trace ∈ T.weakTrace init →
    HonestReach (shapiroConditionedG D I.schedule)
      (fun C => I.verified.Honest (Sal.ConditionedMRDTs.Configuration.core C))
      I.verified.initInv (realize trace)
  adequate : ∀ trace, trace ∈ T.weakTrace init →
    IsRALinearizable3 (realize trace) → S.linearizable trace

namespace ConditionedTraceBridge

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}
  {I : ConditionedTransferInput D hb} {T : LabeledTS} {init : T.State}
  {S : RATraceSpec T.Label}

/-- A conditioned certificate plus trace realization proves the corresponding
state-system trace property. -/
theorem state_ra_linearizable (B : ConditionedTraceBridge I T init S) :
    OpBasedRALinearizable T init S := by
  intro trace htrace
  exact B.adequate trace htrace
    (I.verified.ra_linearizable (B.reachable trace htrace))

end ConditionedTraceBridge

/-- The one-way form needed for safety properties.  Full trace equivalence is
not required: a forward weak simulation and reflection of the target legality
judgment suffice.  This is the useful form for Shapiro emulation, whose two
systems may have different families of silent administrative labels. -/
theorem op_ra_linearizable_of_conditioned_simulation
    {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}
    (I : ConditionedTransferInput D hb)
    {OpTS StateTS : LabeledTS} {μ : LabelMorphism OpTS StateTS}
    (R : WeakSimM OpTS StateTS μ)
    {opInit : OpTS.State} {stateInit : StateTS.State}
    (hrel : R.rel opInit stateInit)
    (OpSpec : RATraceSpec OpTS.Label)
    (StateSpec : RATraceSpec StateTS.Label)
    (hreflect : ∀ trace,
      StateSpec.linearizable (trace.map μ.map) → OpSpec.linearizable trace)
    (B : ConditionedTraceBridge I StateTS stateInit StateSpec) :
    OpBasedRALinearizable OpTS opInit OpSpec := by
  intro trace htrace
  exact hreflect trace
    (B.state_ra_linearizable _ (R.trace_sound hrel htrace))

/-- End-to-end behavioral transfer.  If the state-based emulator is certified
at the conditioned endpoint and emulates the op-based system at their initial
states, every op trace satisfies the pulled-back state-side RA judgment. -/
theorem op_ra_linearizable_of_conditioned_emulation
    {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}
    (I : ConditionedTransferInput D hb)
    {OpTS StateTS : LabeledTS}
    (E : EmulationEquivalence OpTS StateTS)
    {opInit : OpTS.State} {stateInit : StateTS.State}
    (hforward : E.forward.rel opInit stateInit)
    (hbackward : E.backward.rel stateInit opInit)
    (S : RATraceSpec OpTS.Label)
    (B : ConditionedTraceBridge I StateTS stateInit
      (S.pullback E.labels.backward)) :
    OpBasedRALinearizable OpTS opInit S := by
  have hstate := B.state_ra_linearizable
  exact (E.representation_independence hforward hbackward S.linearizable).mpr
    hstate

end Sal.Emulation
