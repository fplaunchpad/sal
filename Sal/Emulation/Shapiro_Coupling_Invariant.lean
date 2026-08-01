import Sal.Emulation.Shapiro_Forward_Simulation

/-!
# Concrete Shapiro op/state coupling invariant

The correspondence is dynamic: generation allocates a fresh conditioned
version, so an arbitrary message type need not be encoded into `Nat` in
advance.  A witness maps generated messages to their immutable broadcast
versions and relates replica materializations and network packets.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

/-- Version `v` is a valid immutable snapshot for message `m`. -/
def VersionCarries (I : OperationalTransferInput D hb)
    (C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule))
    (m : D.Msg) (v : Version) : Prop :=
  ∃ x E, C.core.ver v = some (x, E) ∧ m ∈ x.known

/-- Concrete relation data between an op configuration and the conditioned
snapshot network. -/
structure ShapiroCouplingWitness (I : OperationalTransferInput D hb)
    (O : OpConfiguration D)
    (C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)) where
  messageVersion : D.Msg → Option Version
  honest : I.verified.Honest
    (Sal.ConditionedMRDTs.Configuration.core C.core)
  replicas_forward : ∀ {r s}, O.replicas r = some s →
    ∃ x : EmulatorState D, C.core.N r = some x ∧ x.materialized = s
  replicas_backward : ∀ {r x}, C.core.N r = some x →
    ∃ s, O.replicas r = some s ∧ x.materialized = s
  incorporated_iff : ∀ {r x}, C.core.N r = some x → ∀ m,
    incorporatedAt O.trace r m ↔ m ∈ x.delivered
  fullyDrained : ∀ {r x}, C.core.N r = some x → x.known = x.delivered
  generated_has_version : ∀ {r op m},
    (r, OpInput.update op, OpOutput.send m) ∈ O.trace →
    ∃ v, messageVersion m = some v ∧ VersionCarries I C m v
  op_packet : ∀ {r m}, (r, m) ∈ O.buffer →
    ∃ v, messageVersion m = some v ∧ (r, v) ∈ C.inFlight
  state_packet : ∀ {r v}, (r, v) ∈ C.inFlight →
    ∃ m, messageVersion m = some v ∧ (r, m) ∈ O.buffer

def ShapiroCoupled (I : OperationalTransferInput D hb)
    (O : OpConfiguration D)
    (C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)) : Prop :=
  Nonempty (ShapiroCouplingWitness I O C)

namespace ShapiroCoupled

/-- The empty op system and empty conditioned snapshot network are coupled. -/
theorem initial (I : OperationalTransferInput D hb) :
    ShapiroCoupled I (opInitConfig D)
      (conditionedNetworkInit (shapiroConditionedG D I.schedule)
        I.verified.initInv) := by
  refine ⟨{
    messageVersion := fun _ => none
    honest := I.progress.initHonest
    replicas_forward := ?_
    replicas_backward := ?_
    incorporated_iff := ?_
    fullyDrained := ?_
    generated_has_version := ?_
    op_packet := ?_
    state_packet := ?_ }⟩
  · intro r s hs
    by_cases hr : r = 0
    · subst r
      simp [opInitConfig] at hs
      subst s
      refine ⟨{ materialized := D.init, known := ∅, delivered := ∅ }, ?_, rfl⟩
      simp [conditionedNetworkInit, Sal.ConditionedMRDTs.initConfig,
        shapiroConditionedG, shapiroG]
    · simp [opInitConfig, hr] at hs
  · intro r x hx
    by_cases hr : r = 0
    · subst r
      simp [conditionedNetworkInit, Sal.ConditionedMRDTs.initConfig,
        shapiroConditionedG, shapiroG] at hx
      subst x
      exact ⟨D.init, by simp [opInitConfig], rfl⟩
    · simp [conditionedNetworkInit, Sal.ConditionedMRDTs.initConfig, hr] at hx
  · intro r x hx m
    by_cases hr : r = 0
    · subst r
      simp [conditionedNetworkInit, Sal.ConditionedMRDTs.initConfig,
        shapiroConditionedG, shapiroG] at hx
      subst x
      simp [opInitConfig, incorporatedAt]
    · simp [conditionedNetworkInit, Sal.ConditionedMRDTs.initConfig, hr] at hx
  · intro r x hx
    by_cases hr : r = 0
    · subst r
      simp [conditionedNetworkInit, Sal.ConditionedMRDTs.initConfig,
        shapiroConditionedG, shapiroG] at hx
      subst x
      rfl
    · simp [conditionedNetworkInit, Sal.ConditionedMRDTs.initConfig, hr] at hx
  · intro r op m hm
    simp [opInitConfig] at hm
  · intro r m hm
    exact absurd hm (by simp [opInitConfig])
  · intro r v hv
    exact absurd hv (by simp [conditionedNetworkInit])

/-- Queries preserve the concrete coupling: only a query event is appended to
the op trace, so generated messages, incorporated messages, replicas, and both
network buffers are unchanged. -/
theorem query_preserved (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {r : Replica} {q : D.Query} {v : D.Value}
    (h : ShapiroCoupled I O C)
    (hstep : (disciplinedOpLabeledTS D hb).step O (.query r q v) O') :
    ShapiroCoupled I O' C := by
  rcases h with ⟨W⟩
  rcases hstep with ⟨hdisc, hop⟩
  cases hop with
  | opQuery hs hv O' htrace hreps hbuf =>
      refine ⟨{
        messageVersion := W.messageVersion
        honest := W.honest
        replicas_forward := ?_
        replicas_backward := ?_
        incorporated_iff := ?_
        fullyDrained := W.fullyDrained
        generated_has_version := ?_
        op_packet := ?_
        state_packet := ?_ }⟩
      · intro r' s hs'
        rw [hreps] at hs'
        exact W.replicas_forward hs'
      · intro r' x hx
        obtain ⟨s, hs, hm⟩ := W.replicas_backward hx
        exact ⟨s, by rw [hreps]; exact hs, hm⟩
      · intro r' x hx m
        rw [htrace]
        have hi : incorporatedAt
            (O.trace ++ [(r, OpInput.query q, OpOutput.response v)]) r' m ↔
            incorporatedAt O.trace r' m := by
          simp [incorporatedAt]
        rw [hi, W.incorporated_iff hx]
      · intro r' op m hm
        rw [htrace] at hm
        simp at hm
        exact W.generated_has_version hm
      · intro r' m hm
        rw [hbuf] at hm
        exact W.op_packet hm
      · intro r' ver hver
        obtain ⟨m, hm, hopbuf⟩ := W.state_packet hver
        exact ⟨m, hm, by rw [hbuf]; exact hopbuf⟩

end ShapiroCoupled

end Sal.Emulation
