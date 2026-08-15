import Sal.Emulation.Shapiro_Coupling_Invariant

/-!
# Trace realization for the conditioned snapshot network

Historical snapshot delivery is a network-envelope transition, not literally
a core `Step3V` transition from a current sender head.  Its trace realizer
therefore targets network reachability and uses `networkRALinearizable`, whose
induction already covers `SnapshotMerge`.
-/

namespace Sal.Emulation

open LabeledTS Sal.ConditionedMRDTs

namespace LabeledTS

def weakEnd (T : LabeledTS) (start : T.State) :
    List (T.Label × T.State) → T.State
  | [] => start
  | (_, next) :: rest => weakEnd T next rest

theorem silentClosure_reachable {T : LabeledTS} {s t : T.State}
    (h : T.silentClosure s t) : T.Reachable s t := by
  induction h with
  | refl => exact .refl
  | tail hclosure hstep ih =>
      exact .tail ih ⟨hstep.choose, hstep.choose_spec.2⟩

theorem weakStep_reachable {T : LabeledTS} {s t : T.State} {label : T.Label}
    (h : T.weakStep s label t) : T.Reachable s t := by
  cases h with
  | ofSilent hsilent hclosure => exact silentClosure_reachable hclosure
  | ofObs hobs hpre hstep hpost =>
      exact (silentClosure_reachable hpre).trans
        ((Relation.ReflTransGen.single ⟨_, hstep⟩).trans
          (silentClosure_reachable hpost))

theorem isWeakExecution_reachable_end {T : LabeledTS} {s : T.State}
    {trail : List (T.Label × T.State)} (h : T.isWeakExecution s trail) :
    T.Reachable s (weakEnd T s trail) := by
  induction h with
  | nil => exact .refl
  | cons hobs hstep hrest ih =>
      exact (weakStep_reachable hstep).trans ih

end LabeledTS

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

private abbrev NetworkTS (I : OperationalTransferInput D hb) :=
  conditionedNetworkObservedTS D I

private def networkInitial (I : OperationalTransferInput D hb) :
    (NetworkTS I).State :=
  conditionedNetworkInit (shapiroConditionedG D I.schedule) I.verified.initInv

/-- A canonical endpoint chosen from a weak execution realizing `trace`.
For a non-trace the value is the initial state; all theorems use it only under
the weak-trace premise. -/
noncomputable def canonicalNetworkRealize (I : OperationalTransferInput D hb)
    (trace : List (NetworkTS I).Label) : (NetworkTS I).State := by
  classical
  exact if h : trace ∈ (NetworkTS I).weakTrace (networkInitial I) then
      let trail := Classical.choose h
      LabeledTS.weakEnd (NetworkTS I) (networkInitial I) trail
    else networkInitial I

theorem canonicalNetworkRealize_reachable (I : OperationalTransferInput D hb)
    (trace : List (NetworkTS I).Label)
    (htrace : trace ∈ (NetworkTS I).weakTrace (networkInitial I)) :
    (NetworkTS I).ReachableFrom (networkInitial I)
      (canonicalNetworkRealize I trace) := by
  classical
  rw [canonicalNetworkRealize, dif_pos htrace]
  exact LabeledTS.isWeakExecution_reachable_end (Classical.choose_spec htrace).1

/-- The datatype-specific observable adequacy leaf.  Reachability is no
longer part of this input: it is supplied canonically above. -/
structure NetworkTraceAdequacy (I : OperationalTransferInput D hb)
    (S : RATraceSpec (NetworkTS I).Label) where
  adequate : ∀ trace, trace ∈ (NetworkTS I).weakTrace (networkInitial I) →
    IsRALinearizable3 (canonicalNetworkRealize I trace).core →
    S.linearizable trace

theorem network_ra_linearizable (I : OperationalTransferInput D hb)
    (S : RATraceSpec (NetworkTS I).Label) (A : NetworkTraceAdequacy I S) :
    OpBasedRALinearizable (NetworkTS I) (networkInitial I) S := by
  intro trace htrace
  exact A.adequate trace htrace
    (I.networkRALinearizable (canonicalNetworkRealize_reachable I trace htrace))

/-- End-to-end one-way transfer using the concrete Shapiro simulation. -/
theorem disciplined_op_ra_linearizable
    (I : OperationalTransferInput D hb)
    (P : ConditionedNetworkProgress I)
    (A : ShapiroCoupled.ProgressCompatibility I P)
    (OpSpec : RATraceSpec (disciplinedOpLabeledTS D hb).Label)
    (StateSpec : RATraceSpec (NetworkTS I).Label)
    (hreflect : ∀ trace,
      StateSpec.linearizable
        (trace.map (disciplinedOpToConditionedNetworkLabels D I).map) →
      OpSpec.linearizable trace)
    (B : NetworkTraceAdequacy I StateSpec) :
    OpBasedRALinearizable (disciplinedOpLabeledTS D hb) (opInitConfig D)
      OpSpec := by
  intro trace htrace
  exact hreflect trace (network_ra_linearizable I StateSpec B _
    ((ShapiroCoupled.forwardSimulation I P A).trace_sound
      (ShapiroCoupled.initial I) htrace))

end Sal.Emulation
