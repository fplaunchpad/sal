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
  /-- Every other message in a broadcast snapshot causally precedes the
  message naming that snapshot. -/
  version_causal : ∀ {m v x E}, messageVersion m = some v →
    C.core.ver v = some (x, E) → ∀ p, p ∈ x.known → p = m ∨ hb p m
  messageVersion_injective : ∀ {m₁ m₂ v},
    messageVersion m₁ = some v → messageVersion m₂ = some v → m₁ = m₂
  op_packet : ∀ {r m}, (r, m) ∈ O.buffer →
    ∃ v, messageVersion m = some v ∧ (r, v) ∈ C.inFlight
  state_packet : ∀ {r v}, (r, v) ∈ C.inFlight →
    ∃ m, messageVersion m = some v ∧ (r, m) ∈ O.buffer
  packet_pending : ∀ {r m}, (r, m) ∈ O.buffer →
    ¬ incorporatedAt O.trace r m

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

theorem incorporatedAt_append_delivery (Γ : List (OpEvent D))
    (target replica : Replica) (message candidate : D.Msg) :
    incorporatedAt
        (Γ ++ [(target, OpInput.deliver message, OpOutput.none)])
        replica candidate ↔
      incorporatedAt Γ replica candidate ∨
        (replica = target ∧ candidate = message) := by
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
    version_causal := ?_
    messageVersion_injective := ?_
    op_packet := ?_
    state_packet := ?_
    packet_pending := ?_ }⟩
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
  · intro m v x E hm
    simp at hm
  · intro m₁ m₂ v h₁
    simp at h₁
  · intro r m hm
    exact absurd hm (by simp [opInitConfig])
  · intro r v hv
    exact absurd hv (by simp [conditionedNetworkInit])
  · intro r m hm
    exact absurd hm (by simp [opInitConfig])

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
        version_causal := ?_
        messageVersion_injective := W.messageVersion_injective
        op_packet := ?_
        state_packet := ?_
        packet_pending := ?_ }⟩
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
      · exact W.version_causal
      · intro r' m hm
        rw [hbuf] at hm
        exact W.op_packet hm
      · intro r' ver hver
        obtain ⟨m, hm, hopbuf⟩ := W.state_packet hver
        exact ⟨m, hm, by rw [hbuf]; exact hopbuf⟩
      · intro r' m hm
        rw [hbuf] at hm
        rw [htrace]
        simpa [incorporatedAt] using W.packet_pending hm

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

theorem update_incorporated_iff
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp}
    (W : ShapiroCouplingWitness I O C)
    (hop : OpStep D hb O (.update r op) O')
    (hshape : NetworkUpdateShape I C C' t r op) :
    ∀ {replica x}, C'.core.N replica = some x → ∀ m,
      incorporatedAt O'.trace replica m ↔ m ∈ x.delivered := by
  rcases hshape with ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadNew,
    hVersionOld, hFresh, hN, hVersions⟩
  have hCoreN : C.core.N r = some xOld := by
    have hco := (C.core.head_coherent r vOld hHeadOld).1
    rw [hVersionOld] at hco
    simpa using hco.symm
  cases hop with
  | opUpdate hs hm recipients O' htrace hreps hbuf =>
      subst hm
      obtain ⟨xRelated, hxRelated, hMaterialized⟩ := W.replicas_forward hs
      rw [hCoreN] at hxRelated
      have hxEq := (Option.some.inj hxRelated).symm
      subst xRelated
      rw [← hMaterialized] at htrace
      intro replica x hx m
      by_cases hr : replica = r
      · subst replica
        rw [hN] at hx
        simp [updateRep, shapiroConditionedG, shapiroG, Op.rep, Op.op] at hx
        subst x
        rw [htrace]
        exact incorporated_prepare_iff W hCoreN op m
      · rw [hN] at hx
        simp [updateRep, hr] at hx
        rw [htrace, incorporatedAt_append_update]
        have hnew : ¬ (replica = r ∧ m = D.prepare r op xOld.materialized) := by
          intro h
          exact hr h.1
        simp only [hnew, or_false]
        exact W.incorporated_iff hx m

theorem update_fullyDrained
    (I : OperationalTransferInput D hb)
    {O : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp}
    (W : ShapiroCouplingWitness I O C)
    (hshape : NetworkUpdateShape I C C' t r op) :
    ∀ {replica x}, C'.core.N replica = some x → x.known = x.delivered := by
  rcases hshape with ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadNew,
    hVersionOld, hFresh, hN, hVersions⟩
  have hCoreN : C.core.N r = some xOld := by
    have hco := (C.core.head_coherent r vOld hHeadOld).1
    rw [hVersionOld] at hco
    simpa using hco.symm
  intro replica x hx
  by_cases hr : replica = r
  · subst replica
    rw [hN] at hx
    simp [updateRep, shapiroConditionedG, shapiroG, Op.rep, Op.op] at hx
    subst x
    exact prepare_fullyDrained W hCoreN op
  · rw [hN] at hx
    simp [updateRep, hr] at hx
    exact W.fullyDrained hx

theorem update_new_version_carries
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp}
    (W : ShapiroCouplingWitness I O C)
    (hop : OpStep D hb O (.update r op) O')
    (hshape : NetworkUpdateShape I C C' t r op) :
    ∃ m vNew, C'.core.head r = some vNew ∧ C.core.ver vNew = none ∧
      VersionCarries I C' m vNew ∧
      O'.trace = O.trace ++ [(r, OpInput.update op, OpOutput.send m)] := by
  rcases hshape with ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadNew,
    hVersionOld, hFresh, hN, hVersions⟩
  have hCoreN : C.core.N r = some xOld := by
    have hco := (C.core.head_coherent r vOld hHeadOld).1
    rw [hVersionOld] at hco
    simpa using hco.symm
  cases hop with
  | opUpdate hs hm recipients O' htrace hreps hbuf =>
      subst hm
      obtain ⟨xRelated, hxRelated, hMaterialized⟩ := W.replicas_forward hs
      rw [hCoreN] at hxRelated
      have hxEq := (Option.some.inj hxRelated).symm
      subst xRelated
      let message := D.prepare r op xOld.materialized
      refine ⟨message, vNew, hHeadNew, hFresh, ?_, ?_⟩
      · refine ⟨(shapiroConditionedG D I.schedule).update xOld (t, r, op),
          eventsOld ∪ {(t, r, op)}, ?_, ?_⟩
        · rw [hVersions]
          simp
        · simp [message, shapiroConditionedG, shapiroG, Op.rep, Op.op,
            EmulatorState.prepare, EmulatorState.deliverOne]
      · simpa [message, hMaterialized] using htrace

theorem update_packet_correspondence
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    (W : ShapiroCouplingWitness I O C)
    {issuer : Replica} {message : D.Msg} {vNew : Version}
    {recipients : Set Replica}
    (hMessageFresh : W.messageVersion message = none)
    (hVersionFresh : ∀ m, W.messageVersion m ≠ some vNew)
    (hOpBuffer : O'.buffer = O.buffer ∪ broadcast recipients issuer message)
    (hStateBuffer : C'.inFlight = C.inFlight ∪
      {packet | packet.2 = vNew ∧ packet.1 ∈ recipients ∧
        packet.1 ≠ issuer}) :
    (∀ {r m}, (r, m) ∈ O'.buffer →
      ∃ v, extendMessageVersion W.messageVersion message vNew m = some v ∧
        (r, v) ∈ C'.inFlight) ∧
    (∀ {r v}, (r, v) ∈ C'.inFlight →
      ∃ m, extendMessageVersion W.messageVersion message vNew m = some v ∧
        (r, m) ∈ O'.buffer) := by
  constructor
  · intro r m hm
    rw [hOpBuffer] at hm
    rcases hm with hold | hnew
    · obtain ⟨v, hmap, hpacket⟩ := W.op_packet hold
      have hne : m ≠ message := by
        intro h
        subst m
        rw [hMessageFresh] at hmap
        simp at hmap
      refine ⟨v, extendMessageVersion_other W.messageVersion hne vNew |>.trans hmap,
        ?_⟩
      rw [hStateBuffer]
      exact Or.inl hpacket
    · rcases hnew with ⟨rfl, hr, hri⟩
      refine ⟨vNew, extendMessageVersion_same _ _ _, ?_⟩
      rw [hStateBuffer]
      exact Or.inr ⟨rfl, hr, hri⟩
  · intro r v hv
    rw [hStateBuffer] at hv
    rcases hv with hold | hnew
    · obtain ⟨m, hmap, hpacket⟩ := W.state_packet hold
      have hmv : v ≠ vNew := by
        intro h
        subst v
        exact hVersionFresh m hmap
      have hmm : m ≠ message := by
        intro h
        subst m
        rw [hMessageFresh] at hmap
        simp at hmap
      refine ⟨m, extendMessageVersion_other W.messageVersion hmm vNew |>.trans hmap,
        ?_⟩
      rw [hOpBuffer]
      exact Or.inl hpacket
    · rcases hnew with ⟨rfl, hr, hri⟩
      refine ⟨message, extendMessageVersion_same _ _ _, ?_⟩
      rw [hOpBuffer]
      exact Or.inr ⟨rfl, hr, hri⟩

/-- Allocating the update version preserves the causal meaning of every old
message/version entry and records that all older messages in the new snapshot
precede its freshly generated message. -/
theorem update_version_causal
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp} {vNew : Version}
    (W : ShapiroCouplingWitness I O C)
    (hsource : (disciplinedOpLabeledTS D hb).step O (.update r op) O')
    (hshape : NetworkUpdateShape I C C' t r op)
    (hhead : C'.core.head r = some vNew) :
    let message := D.prepare r op
      ((C.core.N r).getD (shapiroG D I.schedule).init).materialized
    ∀ {m v x E},
      extendMessageVersion W.messageVersion message vNew m = some v →
      C'.core.ver v = some (x, E) →
      ∀ p, p ∈ x.known → p = m ∨ hb p m := by
  rcases hsource with ⟨hdisc, hop⟩
  rcases hshape with ⟨vOld, allocated, xOld, eventsOld, hHeadOld,
    hHeadAllocated, hVersionOld, hFresh, hN, hVersions⟩
  have hvEq : allocated = vNew := by
    rw [hHeadAllocated] at hhead
    exact Option.some.inj hhead
  subst allocated
  have hCoreN : C.core.N r = some xOld := by
    have hco := (C.core.head_coherent r vOld hHeadOld).1
    rw [hVersionOld] at hco
    simpa using hco.symm
  cases hop with
  | opUpdate hs hm recipients O' htrace hreps hbuf =>
      obtain ⟨source, hsourceState, hgen⟩ := hdisc
      rw [hs] at hsourceState
      have hsourceEq := Option.some.inj hsourceState
      subst source
      obtain ⟨related, hrelated, hmat⟩ := W.replicas_forward hs
      rw [hCoreN] at hrelated
      have hrelatedEq := (Option.some.inj hrelated).symm
      subst related
      subst hm
      rw [← hmat] at hgen
      simp only [hCoreN, Option.getD_some]
      intro m v x E hmap hver p hp
      by_cases hmm : m = D.prepare r op xOld.materialized
      · subst m
        rw [extendMessageVersion_same] at hmap
        have hv : v = vNew := Option.some.inj hmap.symm
        subst v
        rw [hVersions] at hver
        simp at hver
        rcases hver with ⟨hx, hE⟩
        subst x
        simp only [shapiroConditionedG, shapiroG, Op.rep, Op.op,
          EmulatorState.prepare, EmulatorState.deliverOne,
          Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact Or.inl rfl
        · exact Or.inr (hgen.2.1 p ((W.incorporated_iff hCoreN p).2
            (W.fullyDrained hCoreN ▸ hp)))
      · rw [extendMessageVersion_other W.messageVersion hmm] at hmap
        have hvne : v ≠ vNew := by
          intro hv
          subst v
          exact (fresh_version_unmapped W hFresh m) hmap
        rw [hVersions] at hver
        simp [hvne] at hver
        exact W.version_causal hmap hver p hp

/-- A disciplined op update and the corresponding snapshot-network update
preserve the full concrete coupling. -/
theorem update_preserved
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {t : Timestamp} {r : Replica} {op : D.AppOp} {vNew : Version}
    {recipients : Set Replica}
    (h : ShapiroCoupled I O C)
    (hsource : (disciplinedOpLabeledTS D hb).step O (.update r op) O')
    (hnetwork : ConditionedNetworkStep (shapiroConditionedG D I.schedule)
      (fun core => I.verified.Honest
        (Sal.ConditionedMRDTs.Configuration.core core))
      C (.apply t r op) C')
    (hhead : C'.core.head r = some vNew)
    (hopBuffer : O'.buffer = O.buffer ∪ broadcast recipients r
      (D.prepare r op ((O.replicas r).getD D.init)))
    (hbuffer : C'.inFlight = C.inFlight ∪
      {packet | packet.2 = vNew ∧ packet.1 ∈ recipients ∧ packet.1 ≠ r})
    (hhonest : I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core C'.core)) :
    ShapiroCoupled I O' C' := by
  rcases h with ⟨W⟩
  have hshape := networkUpdateShape I hnetwork
  rcases hsource with ⟨hdisc, hop⟩
  rcases hshape with ⟨vOld, allocated, xOld, eventsOld, hHeadOld,
    hHeadAllocated, hVersionOld, hFreshVersion, hN, hVersions⟩
  have hvEq : allocated = vNew := by
    rw [hHeadAllocated] at hhead
    exact Option.some.inj hhead
  subst allocated
  have hCoreN : C.core.N r = some xOld := by
    have hco := (C.core.head_coherent r vOld hHeadOld).1
    rw [hVersionOld] at hco
    simpa using hco.symm
  have hopSaved := hop
  cases hop with
  | opUpdate hs hm opRecipients O' htrace hreps hOpBuffer =>
      obtain ⟨source, hsourceState, hgen⟩ := hdisc
      rw [hs] at hsourceState
      have hsourceEq := Option.some.inj hsourceState
      subst source
      obtain ⟨related, hrelated, hmat⟩ := W.replicas_forward hs
      rw [hCoreN] at hrelated
      have hrelatedEq := (Option.some.inj hrelated).symm
      subst related
      subst hm
      rw [← hmat] at hs hgen htrace hOpBuffer hreps
      have hRecipientsBuffer :
          O'.buffer = O.buffer ∪ broadcast recipients r
            (D.prepare r op xOld.materialized) := by
        simpa [hs, hmat] using hopBuffer
      let message := D.prepare r op xOld.materialized
      have hFreshMessage : W.messageVersion message = none :=
        fresh_message_unmapped W hgen.1
      have hFreshMapping : ∀ m, W.messageVersion m ≠ some vNew :=
        fresh_version_unmapped W hFreshVersion
      have hNewCarry : VersionCarries I C' message vNew := by
        refine ⟨(shapiroConditionedG D I.schedule).update xOld (t, r, op),
          eventsOld ∪ {(t, r, op)}, ?_, ?_⟩
        · rw [hVersions]
          simp
        · simp [message, shapiroConditionedG, shapiroG, Op.rep, Op.op,
            EmulatorState.prepare, EmulatorState.deliverOne]
      have hcarry_old {m : D.Msg} {v : Version}
          (hmap : W.messageVersion m = some v)
          (hcarry : VersionCarries I C m v) : VersionCarries I C' m v := by
        obtain ⟨x, E, hver, hmem⟩ := hcarry
        refine ⟨x, E, ?_, hmem⟩
        have hvne : v ≠ vNew := by
          intro hv
          subst v
          exact hFreshMapping m hmap
        rw [hVersions]
        simpa [hvne] using hver
      have hpacket := update_packet_correspondence I W hFreshMessage
        hFreshMapping hRecipientsBuffer hbuffer
      refine ⟨{
        messageVersion := extendMessageVersion W.messageVersion message vNew
        honest := hhonest
        replicas_forward := update_replicas_forward I W hopSaved
          ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadAllocated,
            hVersionOld, hFreshVersion, hN, hVersions⟩
        replicas_backward := update_replicas_backward I W hopSaved
          ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadAllocated,
            hVersionOld, hFreshVersion, hN, hVersions⟩
        incorporated_iff := update_incorporated_iff I W hopSaved
          ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadAllocated,
            hVersionOld, hFreshVersion, hN, hVersions⟩
        fullyDrained := update_fullyDrained I W
          ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadAllocated,
            hVersionOld, hFreshVersion, hN, hVersions⟩
        generated_has_version := ?_
        version_is_generated := ?_
        version_causal := ?_
        messageVersion_injective := ?_
        op_packet := hpacket.1
        state_packet := hpacket.2
        packet_pending := ?_ }⟩
      · intro replica app m hgenerated
        rw [htrace] at hgenerated
        rcases generated_append_update hgenerated with hold | hnew
        · obtain ⟨v, hmap, hcarry⟩ := W.generated_has_version hold
          have hne : m ≠ message := by
            intro heq
            subst m
            exact hgen.1 ⟨replica, Or.inl ⟨app, hold⟩⟩
          exact ⟨v, extendMessageVersion_other W.messageVersion hne vNew |>.trans hmap,
            hcarry_old hmap hcarry⟩
        · rcases hnew with ⟨rfl, rfl, rfl⟩
          exact ⟨vNew, extendMessageVersion_same _ _ _, hNewCarry⟩
      · intro m v hmap
        by_cases hmm : m = message
        · subst m
          rw [extendMessageVersion_same] at hmap
          have hv : v = vNew := Option.some.inj hmap.symm
          subst v
          exact ⟨r, op, by rw [htrace]; simp [message], hNewCarry⟩
        · rw [extendMessageVersion_other W.messageVersion hmm] at hmap
          obtain ⟨replica, app, hgenerated, hcarry⟩ := W.version_is_generated hmap
          exact ⟨replica, app, by rw [htrace]; simp [hgenerated],
            hcarry_old hmap hcarry⟩
      · intro m v x E
        simpa [message, hCoreN] using (update_version_causal I W
          ⟨⟨xOld.materialized, hs, hgen⟩, hopSaved⟩
          ⟨vOld, vNew, xOld, eventsOld, hHeadOld, hHeadAllocated,
            hVersionOld, hFreshVersion, hN, hVersions⟩ hhead
          (m := m) (v := v) (x := x) (E := E))
      · intro m₁ m₂ v h₁ h₂
        by_cases h₁m : m₁ = message
        · subst m₁
          rw [extendMessageVersion_same] at h₁
          have hv : v = vNew := Option.some.inj h₁.symm
          subst v
          by_cases h₂m : m₂ = message
          · exact h₂m.symm
          · rw [extendMessageVersion_other W.messageVersion h₂m] at h₂
            exact absurd h₂ (hFreshMapping m₂)
        · rw [extendMessageVersion_other W.messageVersion h₁m] at h₁
          by_cases h₂m : m₂ = message
          · subst m₂
            rw [extendMessageVersion_same] at h₂
            have hv : v = vNew := Option.some.inj h₂.symm
            subst v
            exact absurd h₁ (hFreshMapping m₁)
          · rw [extendMessageVersion_other W.messageVersion h₂m] at h₂
            exact W.messageVersion_injective h₁ h₂
      · intro target m hpacketOp
        rw [hRecipientsBuffer] at hpacketOp
        rw [htrace, incorporatedAt_append_update]
        rcases hpacketOp with hold | hnew
        · have hne : m ≠ message := by
            intro heq
            subst m
            obtain ⟨v, hmap, hflight⟩ := W.op_packet hold
            rw [hFreshMessage] at hmap
            simp at hmap
          intro hinc
          rcases hinc with hbefore | hlocal
          · exact W.packet_pending hold hbefore
          · exact hne hlocal.2
        · rcases hnew with ⟨rfl, hrecipient, hneIssuer⟩
          intro hinc
          rcases hinc with hbefore | hlocal
          · exact hgen.1 ⟨target, hbefore⟩
          · exact hneIssuer hlocal.1

/-! ## Historical delivery preservation -/

/-- Causal delivery turns the historical sender snapshot into exactly one
fresh pending message at the target. -/
theorem delivery_known_union
    (I : OperationalTransferInput D hb)
    {O : OpConfiguration D}
    {C : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    (W : ShapiroCouplingWitness I O C)
    {target : Replica} {m : D.Msg} {snapshot : Version}
    {xTarget xSnapshot : EmulatorState D} {events : Set (Op D.AppOp)}
    (hpacket : (target, m) ∈ O.buffer)
    (henabled : enabled hb O.trace target m)
    (htarget : C.core.N target = some xTarget)
    (hmap : W.messageVersion m = some snapshot)
    (hsnapshot : C.core.ver snapshot = some (xSnapshot, events)) :
    xTarget.known ∪ xSnapshot.known = insert m xTarget.known ∧
      m ∉ xTarget.delivered := by
  have hmFresh : ¬ incorporatedAt O.trace target m := W.packet_pending hpacket
  have hmNotDelivered : m ∉ xTarget.delivered := by
    intro hm
    exact hmFresh ((W.incorporated_iff htarget m).2 hm)
  have hmSnapshot : m ∈ xSnapshot.known := by
    obtain ⟨issuer, app, hgenerated, x, E, hver, hm⟩ :=
      W.version_is_generated hmap
    rw [hsnapshot] at hver
    have hxe := Prod.mk.inj (Option.some.inj hver)
    simpa [hxe.1] using hm
  constructor
  · apply Finset.Subset.antisymm
    · intro p hp
      simp only [Finset.mem_union] at hp
      rcases hp with hp | hp
      · simp [hp]
      · rcases W.version_causal hmap hsnapshot p hp with rfl | hcausal
        · simp
        · obtain ⟨out, hdelivered⟩ := henabled.2 p hcausal
          have hinc : incorporatedAt O.trace target p := Or.inr ⟨out, hdelivered⟩
          have hpDelivered := (W.incorporated_iff htarget p).1 hinc
          have hpKnown : p ∈ xTarget.known := by
            rw [W.fullyDrained htarget]
            exact hpDelivered
          simp [hpKnown]
    · intro p hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact Finset.mem_union_right _ hmSnapshot
      · exact Finset.mem_union_left _ hp
  · exact hmNotDelivered

/-- Consuming the matching immutable snapshot simulates exactly the source
message delivery and preserves the dynamic coupling. -/
theorem delivery_preserved
    (I : OperationalTransferInput D hb)
    {O O' : OpConfiguration D}
    {C C' : ConditionedNetworkConfig (shapiroConditionedG D I.schedule)}
    {target : Replica} {m : D.Msg} {snapshot : Version}
    (hsource : (disciplinedOpLabeledTS D hb).step O (.deliver target m) O')
    (hmatches : ∃ W : ShapiroCouplingWitness I O C,
      W.messageVersion m = some snapshot)
    (hsnapshot : SnapshotMerge (shapiroConditionedG D I.schedule)
      C.core target snapshot C'.core)
    (hStateBuffer : C'.inFlight = C.inFlight \ {(target, snapshot)})
    (hhonest : I.verified.Honest
      (Sal.ConditionedMRDTs.Configuration.core C'.core)) :
    ShapiroCoupled I O' C' := by
  obtain ⟨W, hmap⟩ := hmatches
  rcases hsource with ⟨hdisc, hop⟩
  cases hop with
  | opDeliver hpacket henabled hs O' htrace hreps hOpBuffer =>
          cases hsnapshot with
          | step hHead hTargetVersion hSnapshotVersion hFresh hRankTarget
              hRankSnapshot core' hN hL hvis hVersions hheads hparents =>
              rename_i vTarget vNew xTarget xSnapshot eventsTarget eventsSnapshot
              have hTargetN : C.core.N target = some xTarget := by
                have hco := (C.core.head_coherent target vTarget hHead).1
                rw [hTargetVersion] at hco
                simpa using hco.symm
              obtain ⟨related, hRelatedN, hMaterialized⟩ :=
                W.replicas_forward hs
              rw [hTargetN] at hRelatedN
              have hRelatedEq := (Option.some.inj hRelatedN).symm
              subst related
              have hunion := delivery_known_union I W hpacket henabled hTargetN
                hmap hSnapshotVersion
              have hmerge :
                  (shapiroG D I.schedule).merge xTarget xSnapshot =
                    xTarget.deliverOne m := by
                rw [show (shapiroG D I.schedule).merge xTarget xSnapshot =
                    xTarget.drain I.schedule (xTarget.known ∪ xSnapshot.known) from rfl,
                  hunion.1]
                exact EmulatorState.drain_insert_eq_deliverOne I.schedule
                  xTarget m (W.fullyDrained hTargetN) hunion.2
              have hVersionOld {msg : D.Msg} {v : Version}
                  (hmv : W.messageVersion msg = some v) : v ≠ vNew := by
                intro hv
                subst v
                obtain ⟨issuer, app, hgenerated, x, E, hver, hm⟩ :=
                  W.version_is_generated hmv
                rw [hFresh] at hver
                simp at hver
              refine ⟨{
                messageVersion := W.messageVersion
                honest := hhonest
                replicas_forward := ?_
                replicas_backward := ?_
                incorporated_iff := ?_
                fullyDrained := ?_
                generated_has_version := ?_
                version_is_generated := ?_
                version_causal := ?_
                messageVersion_injective := W.messageVersion_injective
                op_packet := ?_
                state_packet := ?_
                packet_pending := ?_ }⟩
              · intro replica state hstate
                by_cases hr : replica = target
                · subst replica
                  rw [hreps] at hstate
                  simp at hstate
                  subst state
                  refine ⟨xTarget.deliverOne m, ?_, ?_⟩
                  · rw [hN]
                    simp [updateRep, shapiroConditionedG, hmerge]
                  · simp [EmulatorState.deliverOne, hMaterialized]
                · rw [hreps] at hstate
                  simp [hr] at hstate
                  obtain ⟨x, hx, hmat⟩ := W.replicas_forward hstate
                  exact ⟨x, by rw [hN]; simp [updateRep, hr, hx], hmat⟩
              · intro replica x hx
                by_cases hr : replica = target
                · subst replica
                  rw [hN] at hx
                  simp [updateRep, shapiroConditionedG, hmerge] at hx
                  subst x
                  refine ⟨D.effect m xTarget.materialized, ?_, rfl⟩
                  rw [hreps]
                  simp [hMaterialized]
                · rw [hN] at hx
                  simp [updateRep, hr] at hx
                  obtain ⟨state, hs', hmat⟩ := W.replicas_backward hx
                  exact ⟨state, by rw [hreps]; simp [hr, hs'], hmat⟩
              · intro replica x hx candidate
                rw [htrace, incorporatedAt_append_delivery]
                by_cases hr : replica = target
                · subst replica
                  rw [hN] at hx
                  simp [updateRep, shapiroConditionedG, hmerge] at hx
                  subst x
                  simp only [EmulatorState.deliverOne, Finset.mem_insert]
                  rw [W.incorporated_iff hTargetN]
                  aesop
                · rw [hN] at hx
                  simp [updateRep, hr] at hx
                  rw [W.incorporated_iff hx]
                  simp [hr]
              · intro replica x hx
                by_cases hr : replica = target
                · subst replica
                  rw [hN] at hx
                  simp [updateRep, shapiroConditionedG, hmerge] at hx
                  subst x
                  simp [EmulatorState.deliverOne, W.fullyDrained hTargetN]
                · rw [hN] at hx
                  simp [updateRep, hr] at hx
                  exact W.fullyDrained hx
              · intro replica app msg hgenerated
                rw [htrace] at hgenerated
                simp at hgenerated
                obtain ⟨v, hmv, x, E, hver, hm⟩ := W.generated_has_version hgenerated
                refine ⟨v, hmv, x, E, ?_, hm⟩
                rw [hVersions]
                simp [hVersionOld hmv, hver]
              · intro msg v hmv
                obtain ⟨issuer, app, hgenerated, x, E, hver, hm⟩ :=
                  W.version_is_generated hmv
                refine ⟨issuer, app, by rw [htrace]; simp [hgenerated],
                  x, E, ?_, hm⟩
                rw [hVersions]
                simp [hVersionOld hmv, hver]
              · intro msg v x E hmv hver p hp
                rw [hVersions] at hver
                simp [hVersionOld hmv] at hver
                exact W.version_causal hmv hver p hp
              · intro replica msg hopacket
                rw [hOpBuffer] at hopacket
                obtain ⟨v, hmv, hvpacket⟩ := W.op_packet hopacket.1
                refine ⟨v, hmv, ?_⟩
                rw [hStateBuffer]
                refine ⟨hvpacket, ?_⟩
                intro heq
                have hr : replica = target := congrArg Prod.fst heq
                have hv : v = snapshot := congrArg Prod.snd heq
                subst replica
                subst v
                have hmEq := W.messageVersion_injective hmv hmap
                subst msg
                exact hopacket.2 rfl
              · intro replica v hvpacket
                rw [hStateBuffer] at hvpacket
                obtain ⟨msg, hmv, hopacket⟩ := W.state_packet hvpacket.1
                refine ⟨msg, hmv, ?_⟩
                rw [hOpBuffer]
                refine ⟨hopacket, ?_⟩
                intro heq
                have hr : replica = target := congrArg Prod.fst heq
                have hm : msg = m := congrArg Prod.snd heq
                subst replica
                subst msg
                rw [hmap] at hmv
                have hv := Option.some.inj hmv
                subst v
                exact hvpacket.2 rfl
              · intro replica msg hopacket
                rw [hOpBuffer] at hopacket
                rw [htrace, incorporatedAt_append_delivery]
                intro hinc
                rcases hinc with hold | hnew
                · exact W.packet_pending hopacket.1 hold
                · exact hopacket.2 (by rcases hnew with ⟨rfl, rfl⟩; rfl)

/-- The two constructive enablement facts not implied by a safety-only
`VerifiedMRDT` certificate. -/
structure ProgressCompatibility (I : OperationalTransferInput D hb)
    (P : ConditionedNetworkProgress I) where
  update : ∀ {O O' C r op}, ShapiroCoupled I O C →
    (disciplinedOpLabeledTS D hb).step O (.update r op) O' →
    P.CanUpdate C r op
  deliver : ∀ {C r v}, (r, v) ∈ C.inFlight → P.CanDeliver C r v

/-- All concrete invariant proofs assembled into the generic network-coupling
interface. -/
def networkCoupling (I : OperationalTransferInput D hb)
    (P : ConditionedNetworkProgress I) (A : ProgressCompatibility I P) :
    ShapiroNetworkCoupling I P where
  rel := ShapiroCoupled I
  deliveryMatches := fun O C m v =>
    ∃ W : ShapiroCouplingWitness I O C, W.messageVersion m = some v
  initial := initial I
  honest := by
    rintro O C ⟨W⟩
    exact W.honest
  replica := by
    rintro O C ⟨W⟩ r s hs
    exact W.replicas_forward hs
  updateEnabled := A.update
  updatePreserved := by
    intro O O' C C' r op t vNew recipients hrel hsource hstep hhead
      hopBuffer hbuffer hhonest
    exact update_preserved I hrel hsource hstep hhead hopBuffer hbuffer hhonest
  queryPreserved := by
    intro O O' C r q v hrel hsource
    exact query_preserved I hrel hsource
  deliveryEnabled := by
    intro O O' C r m hrel hsource
    rcases hrel with ⟨W⟩
    rcases hsource with ⟨hdisc, hop⟩
    cases hop with
    | opDeliver hpacket henabled hs O' htrace hreps hbuffer =>
        obtain ⟨v, hmap, hflight⟩ := W.op_packet hpacket
        exact ⟨v, A.deliver hflight, W, hmap⟩
  deliveryPreserved := by
    intro O O' C C' r m snapshot hrel hsource hcan hmatches hsnapshot
      hbuffer hhonest
    exact delivery_preserved I hsource hmatches hsnapshot hbuffer hhonest

/-- Datatype-generic forward weak simulation, with only constructive progress
left as an explicit deployment assumption. -/
def forwardSimulation (I : OperationalTransferInput D hb)
    (P : ConditionedNetworkProgress I) (A : ProgressCompatibility I P) :
    WeakSimM (disciplinedOpLabeledTS D hb)
      (conditionedNetworkObservedTS D I)
      (disciplinedOpToConditionedNetworkLabels D I) :=
  (networkCoupling I P A).forward

end ShapiroCoupled

end Sal.Emulation
