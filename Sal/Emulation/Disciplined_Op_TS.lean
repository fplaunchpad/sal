import Sal.Emulation.Op_Based_TS

/-!
# Well-formed operation-based executions

The raw Liittschwager-style rules describe network mechanics but deliberately
leave message-generation freshness to the CRDT/causal-broadcast discipline.
Shapiro's conditioned endpoint makes that discipline explicit through
`PrepareEnabled`.  This file imposes the corresponding trace-local condition
on op updates; queries and already-causally-enabled deliveries are unchanged.
-/

namespace Sal.Emulation

/-- A message has been incorporated at replica `r` either by local generation
or by network delivery. -/
def incorporatedAt {D : OpCRDTSig} (Γ : List (OpEvent D))
    (r : Replica) (m : D.Msg) : Prop :=
  (∃ op, (r, OpInput.update op, OpOutput.send m) ∈ Γ) ∨
  (∃ out, (r, OpInput.deliver m, out) ∈ Γ)

/-- Global message identity: a generated message denotes one broadcast event,
not a replica-local occurrence. -/
def incorporatedAnywhere {D : OpCRDTSig} (Γ : List (OpEvent D))
    (m : D.Msg) : Prop := ∃ r, incorporatedAt Γ r m

/-- Trace-side counterpart of `EmulatorState.PrepareEnabled`, strengthened
with the causal-broadcast generation law.  A locally generated message is
causally after every message already incorporated at its issuer.  This law is
load-bearing for snapshot emulation: when a receiver is allowed to deliver
the new message, causal delivery has already incorporated every older message
contained in the issuer's immutable snapshot. -/
def generationEnabled {D : OpCRDTSig} (hb : D.Msg → D.Msg → Prop)
    (Γ : List (OpEvent D)) (r : Replica) (m : D.Msg) : Prop :=
  ¬ incorporatedAnywhere Γ m ∧
  (∀ p, incorporatedAt Γ r p → hb p m) ∧
  (∀ p, incorporatedAt Γ r p → hb p m →
    (r, OpInput.deliver p, OpOutput.none) ∈ Γ ∨
    (∃ op, (r, OpInput.update op, OpOutput.send p) ∈ Γ)) ∧
  (∀ q, incorporatedAt Γ r q → ¬ hb m q)

/-- Restrict only update generation. The source-state equality pins the
message to the actual `prepare` result used by `OpStep.opUpdate`. -/
def disciplinedLabel {D : OpCRDTSig} (hb : D.Msg → D.Msg → Prop)
    (C : OpConfiguration D) : OpLabel D → Prop
  | .update r op => ∃ s, C.replicas r = some s ∧
      generationEnabled hb C.trace r (D.prepare r op s)
  | .query _ _ _ => True
  | .deliver _ _ => True

/-- Operation-based LTS with the generation discipline required by the
conditioned Shapiro construction. -/
def disciplinedOpLabeledTS (D : OpCRDTSig)
    (hb : D.Msg → D.Msg → Prop) : LabeledTS where
  State := OpConfiguration D
  Label := OpLabel D
  step := fun C ℓ C' => disciplinedLabel hb C ℓ ∧ OpStep D hb C ℓ C'
  silent := OpLabel.isSilent

end Sal.Emulation
