import Sal.Emulation.Network_Transfer

/-!
# Grow-only-set canary for the conditioned transfer

This specializes the datatype-generic Shapiro/network theorem to a concrete
op signature.  Certificate construction, network progress, and observable
adequacy remain explicit inputs, so the canary cannot manufacture either
safety or liveness evidence.
-/

namespace Sal.Emulation.Instances.GSetConditionedCanary

open Sal.Emulation

def GSetOp : OpCRDTSig where
  State := Finset Nat
  dec_state := inferInstance
  init := ∅
  AppOp := Nat
  dec_op := inferInstance
  Msg := Replica × Nat × Nat
  dec_msg := inferInstance
  Query := Unit
  Value := Finset Nat
  prepare := fun r value state => (r, state.card, value)
  effect := fun message state => insert message.2.2 state
  query := fun state _ => state
  rc := fun _ _ => RcRes.Either

/-- Messages from one replica are ordered by their issuer-local generation
index.  Cross-replica causality can be supplied by a richer clocked canary;
the generic theorem itself is independent of this choice. -/
def hb (a b : GSetOp.Msg) : Prop := a.1 = b.1 ∧ a.2.1 < b.2.1

abbrev OpTS := disciplinedOpLabeledTS GSetOp hb

theorem conditioned_gset_transfer
    (I : OperationalTransferInput GSetOp hb)
    (P : ConditionedNetworkProgress I)
    (A : ShapiroCoupled.ProgressCompatibility I P)
    (OpSpec : RATraceSpec OpTS.Label)
    (StateSpec : RATraceSpec (conditionedNetworkObservedTS GSetOp I).Label)
    (hreflect : ∀ trace,
      StateSpec.linearizable
        (trace.map (disciplinedOpToConditionedNetworkLabels GSetOp I).map) →
      OpSpec.linearizable trace)
    (B : NetworkTraceAdequacy I StateSpec) :
    OpBasedRALinearizable OpTS (opInitConfig GSetOp) OpSpec :=
  disciplined_op_ra_linearizable I P A OpSpec StateSpec hreflect B

/-! PASS/FAIL controls for the concrete operation semantics. -/

example : GSetOp.effect (4, 0, 9) (∅ : Finset Nat) = ({9} : Finset Nat) := by
  decide

example : GSetOp.effect (4, 0, 9) (∅ : Finset Nat) ≠ (∅ : Finset Nat) := by
  decide

end Sal.Emulation.Instances.GSetConditionedCanary
