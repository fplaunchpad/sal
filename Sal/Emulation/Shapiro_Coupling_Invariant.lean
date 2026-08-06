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
  version_is_generated : ∀ {m v}, messageVersion m = some v →
    ∃ r op, (r, OpInput.update op, OpOutput.send m) ∈ O.trace ∧
      VersionCarries I C m v
  op_packet : ∀ {r m}, (r, m) ∈ O.buffer →
    ∃ v, messageVersion m = some v ∧ (r, v) ∈ C.inFlight
  state_packet : ∀ {r v}, (r, v) ∈ C.inFlight →
    ∃ m, messageVersion m = some v ∧ (r, m) ∈ O.buffer

def ShapiroCoupled (I : OperationalTransferInput D hb)
    (O : OpConfiguration D)
    (C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)) : Prop :=
  Nonempty (ShapiroCouplingWitness I O C)

/-- Extend the dynamic correspondence at one globally fresh message. -/
def extendMessageVersion [DecidableEq D.Msg]
    (μ : D.Msg → Option Version) (message : D.Msg) (version : Version) :
    D.Msg → Option Version :=
  fun m => if m = message then some version else μ m

@[simp] theorem extendMessageVersion_same [DecidableEq D.Msg]
    (μ : D.Msg → Option Version) (m : D.Msg) (v : Version) :
    extendMessageVersion μ m v m = some v := by
  simp [extendMessageVersion]

theorem extendMessageVersion_other [DecidableEq D.Msg]
    (μ : D.Msg → Option Version) {fresh other : D.Msg} (h : other ≠ fresh)
    (v : Version) : extendMessageVersion μ fresh v other = μ other := by
  simp [extendMessageVersion, h]

theorem incorporatedAt_append_update (Γ : List (OpEvent D))
    (issuer replica : Replica) (op : D.AppOp) (message candidate : D.Msg) :
    incorporatedAt
        (Γ ++ [(issuer, OpInput.update op, OpOutput.send message)])
        replica candidate ↔
      incorporatedAt Γ replica candidate ∨
        (replica = issuer ∧ candidate = message) := by
  simp [incorporatedAt]
  aesop

theorem generated_append_update {Γ : List (OpEvent D)}
    {issuer replica : Replica} {op op' : D.AppOp} {message candidate : D.Msg}
    (h : (replica, OpInput.update op', OpOutput.send candidate) ∈
      Γ ++ [(issuer, OpInput.update op, OpOutput.send message)]) :
    (replica, OpInput.update op', OpOutput.send candidate) ∈ Γ ∨
      (replica = issuer ∧ op' = op ∧ candidate = message) := by
  simpa using h

theorem fresh_message_unmapped
    {I : OperationalTransferInput D hb} {O : OpConfiguration D}
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    (W : ShapiroCouplingWitness I O C)
    {m : D.Msg} (hfresh : ¬ incorporatedAnywhere O.trace m) :
    W.messageVersion m = none := by
  cases hm : W.messageVersion m with
  | none => rfl
  | some v =>
      obtain ⟨r, op, hgen, hcarry⟩ := W.version_is_generated hm
      exact absurd ⟨r, Or.inl ⟨op, hgen⟩⟩ hfresh

theorem fresh_version_unmapped
    {I : OperationalTransferInput D hb} {O : OpConfiguration D}
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    (W : ShapiroCouplingWitness I O C) {v : Version}
    (hfresh : C.core.ver v = none) : ∀ m, W.messageVersion m ≠ some v := by
  intro m hm
  obtain ⟨r, op, hgen, x, E, hver, hmem⟩ := W.version_is_generated hm
  rw [hfresh] at hver
  simp at hver

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
    version_is_generated := ?_
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
    simp at hm
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
        version_is_generated := ?_
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
      · intro m ver hm
        obtain ⟨r', op, hgen, hcarry⟩ := W.version_is_generated hm
        exact ⟨r', op, by rw [htrace]; simp [hgen], hcarry⟩
      · intro r' m hm
        rw [hbuf] at hm
        exact W.op_packet hm
      · intro r' ver hver
        obtain ⟨m, hm, hopbuf⟩ := W.state_packet hver
        exact ⟨m, hm, by rw [hbuf]; exact hopbuf⟩

/-! ## Update preservation: local algebra

These facts are the pointwise heart of the update case.  They deliberately
avoid the large configuration record and expose exactly how immediate
self-delivery changes Shapiro's three state components. -/

@[simp] theorem prepare_materialized (x : EmulatorState D) (r : Replica)
    (op : D.AppOp) :
    (x.prepare r op).materialized =
      D.effect (D.prepare r op x.materialized) x.materialized := rfl

@[simp] theorem prepare_known (x : EmulatorState D) (r : Replica)
    (op : D.AppOp) :
    (x.prepare r op).known = insert (D.prepare r op x.materialized) x.known := rfl

@[simp] theorem prepare_delivered (x : EmulatorState D) (r : Replica)
    (op : D.AppOp) :
    (x.prepare r op).delivered =
      insert (D.prepare r op x.materialized) x.delivered := rfl

theorem incorporated_prepare_iff
    (W : ShapiroCouplingWitness I O C) {r : Replica} {x : EmulatorState D}
    (hx : C.core.N r = some x) (op : D.AppOp) (candidate : D.Msg) :
    incorporatedAt
        (O.trace ++ [(r, OpInput.update op,
          OpOutput.send (D.prepare r op x.materialized))]) r candidate ↔
      candidate ∈ (x.prepare r op).delivered := by
  rw [incorporatedAt_append_update]
  rw [prepare_delivered, Finset.mem_insert]
  rw [W.incorporated_iff hx]
  aesop

theorem prepare_fullyDrained
    (W : ShapiroCouplingWitness I O C) {r : Replica} {x : EmulatorState D}
    (hx : C.core.N r = some x) (op : D.AppOp) :
    (x.prepare r op).known = (x.prepare r op).delivered := by
  simp only [prepare_known, prepare_delivered]
  rw [W.fullyDrained hx]

/-- Normalized facts exposed by a conditioned network update. -/
def NetworkUpdateShape (I : OperationalTransferInput D hb)
    (C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule))
    (t : Timestamp) (r : Replica) (op : D.AppOp) : Prop :=
  ∃ vOld vNew xOld eventsOld,
    C.core.head r = some vOld ∧
    C'.core.head r = some vNew ∧
    C.core.ver vOld = some (xOld, eventsOld) ∧
    C.core.ver vNew = none ∧
    C'.core.N = updateRep C.core.N r
      ((shapiroConditionedG D I.schedule).update xOld (t, r, op)) ∧
    C'.core.ver = fun w => if w = vNew then
      some ((shapiroConditionedG D I.schedule).update xOld (t, r, op),
        eventsOld ∪ {(t, r, op)}) else C.core.ver w

theorem networkUpdateShape
    (I : OperationalTransferInput D hb)
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp}
    (hstep : ConditionedNetworkStep (shapiroConditionedG D I.schedule)
      (fun core => I.verified.Honest
        (Sal.ConditionedMRDTs.Configuration.core core))
      C (.apply t r op) C') :
    NetworkUpdateShape I C C' t r op := by
  cases hstep with
  | update hHonest hcore hProduced recipients hbuffer =>
      cases hcore with
      | base hraw =>
          cases hraw with
          | apply hOld hverOld hFreshT hFreshStore hFresh hRank Cnext
              hN hL hvis hver hhead hparents =>
              exact ⟨_, _, _, _, hOld, by rw [hhead]; simp,
                hverOld, hFresh, hN, hver⟩

theorem update_replicas_forward
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp}
    (W : ShapiroCouplingWitness I O C)
    (hop : OpStep D hb O (.update r op) O')
    (hshape : NetworkUpdateShape I C C' t r op) :
    ∀ {replica state}, O'.replicas replica = some state →
      ∃ x : EmulatorState D,
        C'.core.N replica = some x ∧ x.materialized = state := by
  rcases hshape with ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadNew,
    hVersionOld, hFresh, hN, hVersions⟩
  cases hop with
  | opUpdate hs hm recipients O' htrace hreps hbuf =>
      subst hm
      have hCoreN : C.core.N r = some xOld := by
        have hco := (C.core.head_coherent r vOld hHeadOld).1
        rw [hVersionOld] at hco
        simpa using hco.symm
      obtain ⟨xRelated, hxRelated, hMaterialized⟩ :=
        W.replicas_forward hs
      have hxEq : xRelated = xOld := by
        rw [hCoreN] at hxRelated
        exact (Option.some.inj hxRelated).symm
      subst xRelated
      intro replica state hstate
      by_cases hr : replica = r
      · subst replica
        rw [hreps] at hstate
        simp at hstate
        subst state
        refine ⟨xOld.prepare r op, ?_, ?_⟩
        · rw [hN]
          simp [updateRep, shapiroConditionedG, shapiroG, Op.rep, Op.op]
        · simp [hMaterialized]
      · rw [hreps] at hstate
        simp [hr] at hstate
        obtain ⟨x, hx, hmat⟩ := W.replicas_forward hstate
        exact ⟨x, by rw [hN]; simp [updateRep, hr, hx], hmat⟩

theorem update_replicas_backward
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp}
    (W : ShapiroCouplingWitness I O C)
    (hop : OpStep D hb O (.update r op) O')
    (hshape : NetworkUpdateShape I C C' t r op) :
    ∀ {replica x}, C'.core.N replica = some x →
      ∃ state, O'.replicas replica = some state ∧ x.materialized = state := by
  rcases hshape with ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadNew,
    hVersionOld, hFresh, hN, hVersions⟩
  have hCoreN : C.core.N r = some xOld := by
    have hco := (C.core.head_coherent r vOld hHeadOld).1
    rw [hVersionOld] at hco
    simpa using hco.symm
  cases hop with
  | opUpdate hs hm recipients O' htrace hreps hbuf =>
      subst hm
      obtain ⟨sourceState, hSourceState, hMaterialized⟩ :=
        W.replicas_backward hCoreN
      rw [hs] at hSourceState
      have hStateEq := Option.some.inj hSourceState
      subst sourceState
      rw [hStateEq] at hs hreps hbuf htrace
      intro replica x hx
      by_cases hr : replica = r
      · subst replica
        rw [hN] at hx
        simp [updateRep, shapiroConditionedG, shapiroG, Op.rep, Op.op] at hx
        subst x
        refine ⟨D.effect (D.prepare r op xOld.materialized)
          xOld.materialized, ?_, ?_⟩
        · rw [hreps]
          simp
        · rfl
      · rw [hN] at hx
        simp [updateRep, hr] at hx
        obtain ⟨state, hstate, hmat⟩ := W.replicas_backward hx
        exact ⟨state, by rw [hreps]; simp [hr, hstate], hmat⟩

end ShapiroCoupled

end Sal.Emulation
