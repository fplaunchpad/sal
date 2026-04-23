import Sal.Emulation.CRDT_Signature

/-!
# Op-based CRDT labeled transition system

Port of Liittschwager et al. §3.3, Fig. op-global-rules. A state-based
CRDT can *emulate* an op-based CRDT (and vice versa); establishing the
emulation in Lean requires both TSs side-by-side. This file defines the
op-based side.

Differences from the state-based TS in `CRDT_TS.lean`:

* Two hooks per update: `prepare` generates a message, `effect` applies
  it locally. The system-level `OpUpdate` rule fires both.
* System carries a **message buffer** `β` of in-flight packets instead
  of per-replica event sets. Delivery is a separate silent transition
  (`OpDeliver`).
* Delivery must respect **causal order** (Fig. def:causal-delivery in
  the paper). We encode this with an `enabled` predicate on the
  trace `Γ`, as in Fig. def:enabled.

The signatures (`OpCRDTSig`) and the `CRDTSig` of `CRDT_Signature.lean`
share `State`, `init`, `Query`, `Value`, `Op`, `rc`, but differ on the
update/merge hooks. The canonical emulation $\mathcal{G}$ (step 9 of
PLAN.md) relates them.
-/

namespace Sal.Emulation

open LabeledTS

/-- Op-based CRDT signature: `⟨Σ, σ₀, prepare, effect, query, rc⟩`.

Glossary:
* `State`  — Σ, replica state space.
* `init`   — σ₀, initial state.
* `AppOp`  — set of abstract client-facing update operations.
* `Msg`    — set of messages; op-based CRDTs broadcast these rather
  than full states. Typically `Msg = AppOp × VectorClock` or similar.
* `Query` / `Value` — observable queries.
* `prepare` — `(r, op, s) ↦ m`: generates the message to broadcast when
  client issues `op` on replica `r` at state `s`.
* `effect`  — `(m, s) ↦ s'`: applies a delivered message.
* `query`   — `(s, q) ↦ v`: observable query.
* `rc`      — same as state-based: the linearization-order spec over ops.
-/
structure OpCRDTSig where
  State : Type
  dec_state : DecidableEq State
  init : State
  AppOp : Type
  dec_op : DecidableEq AppOp
  Msg : Type
  dec_msg : DecidableEq Msg
  Query : Type
  Value : Type
  prepare : Replica → AppOp → State → Msg
  effect : Msg → State → State
  query : State → Query → Value
  rc : Op AppOp → Op AppOp → RcRes

namespace OpCRDTSig
attribute [instance] dec_state dec_op dec_msg
end OpCRDTSig

/-- The *input event* recorded on an op-based replica transition.
Matches Liittschwager §3.3 grammar (Inputs `I`). -/
inductive OpInput (D : OpCRDTSig) where
  | update (op : D.AppOp)
  | query (q : D.Query)
  | deliver (m : D.Msg)

/-- The *output event*. -/
inductive OpOutput (D : OpCRDTSig) where
  | none
  | response (v : D.Value)
  | send (m : D.Msg)

/-- An event: replica + input + output. Matches the paper's
`(r, i, o)` tuples. -/
abbrev OpEvent (D : OpCRDTSig) := Replica × OpInput D × OpOutput D

/-- System configuration `⟨Γ, Σ, β⟩` (paper §3.2). -/
structure OpConfiguration (D : OpCRDTSig) where
  /-- Γ: event trace of all observed transitions. -/
  trace : List (OpEvent D)
  /-- Σ: per-replica state. `none` for replicas that haven't been
  initialized (we use dynamic creation for parity with `CRDT_TS`). -/
  replicas : Replica → Option D.State
  /-- β: message buffer, a set of in-flight packets `(rid, m)`
  destined for `rid`. -/
  buffer : Set (Replica × D.Msg)

/-- Labels on system-level transitions. The paper tags them with
replica + input + output; we collapse to a simpler label type that
carries just enough information to drive the step relation. `deliver`
labels are silent (see `isSilent` below). -/
inductive OpLabel (D : OpCRDTSig) where
  | update (r : Replica) (op : D.AppOp)
  | query (r : Replica) (q : D.Query) (v : D.Value)
  | deliver (r : Replica) (m : D.Msg)

/-- `deliver` is the only silent label (consumes a message from the
buffer, does not surface at the client). -/
def OpLabel.isSilent {D : OpCRDTSig} : OpLabel D → Prop
  | .deliver _ _ => True
  | _ => False

/-- Broadcast helper: given a sender `r` and message `m`, produce the
set of in-flight packets to be unioned into the buffer (one per
recipient ≠ sender). Matches Liittschwager §3.2's `bcast`. -/
def broadcast {D : OpCRDTSig} (senders : Set Replica) (r : Replica) (m : D.Msg) :
    Set (Replica × D.Msg) :=
  fun p => p.2 = m ∧ p.1 ∈ senders ∧ p.1 ≠ r

/-! ## Causal delivery

The op-based TS restricts `deliver` to respect causal order among
messages. We parameterise by an abstract *happens-before* predicate
`hb : Msg → Msg → Prop` and require that when `m' → m`, all causal
predecessors have already been delivered at the target replica.

This corresponds to Liittschwager §3.3 Definition
`def:causal-message-delivery` + `def:enabled`. Concrete instantiations
(e.g. vector-clock-backed) supply `hb` on construction of the
`OpCRDT` object. -/

/-- `enabled Γ hb r m` holds when `m` is ready to be delivered at
`r`: no earlier delivery, and all causal predecessors delivered. -/
def enabled {D : OpCRDTSig}
    (hb : D.Msg → D.Msg → Prop)
    (Γ : List (OpEvent D)) (r : Replica) (m : D.Msg) : Prop :=
  (∀ o, (r, OpInput.deliver m, o) ∉ Γ)
  ∧ (∀ m', hb m' m → ∃ o, (r, OpInput.deliver m', o) ∈ Γ)

/-- Step relation of the op-based system (Liittschwager Fig. op-global-rules).

Rules (one per constructor):
* **OpUpdate**: client issues `op` at `r`; `prepare` generates `m`,
  `effect` applies it locally, `m` is broadcast.
* **OpQuery**: client issues `q` at `r`, observes `query s q`.
* **OpDeliver**: deliver an enabled message from buffer.

Unlike the state-based TS, there is no fresh-timestamp premise on
`OpUpdate` — timestamps live inside messages (via vector clocks etc.)
and are the concern of the caller. -/
inductive OpStep (D : OpCRDTSig) (hb : D.Msg → D.Msg → Prop) :
    OpConfiguration D → OpLabel D → OpConfiguration D → Prop where
  /-- **OpUpdate**: local update + broadcast. -/
  | opUpdate {C : OpConfiguration D} {r : Replica} {op : D.AppOp}
      {s : D.State} {m : D.Msg}
      (h_s : C.replicas r = some s)
      (h_m : m = D.prepare r op s)
      (senders : Set Replica)
      (C' : OpConfiguration D)
      (htrace : C'.trace = C.trace ++ [(r, OpInput.update op, OpOutput.send m)])
      (hreps : C'.replicas = fun r' =>
        if r' = r then some (D.effect m s) else C.replicas r')
      (hbuf : C'.buffer = C.buffer ∪ broadcast senders r m) :
      OpStep D hb C (.update r op) C'
  /-- **OpQuery**: pure observation. -/
  | opQuery {C : OpConfiguration D} {r : Replica} {q : D.Query}
      {s : D.State} {v : D.Value}
      (h_s : C.replicas r = some s)
      (h_v : v = D.query s q)
      (C' : OpConfiguration D)
      (htrace : C'.trace = C.trace ++ [(r, OpInput.query q, OpOutput.response v)])
      (hreps : C'.replicas = C.replicas)
      (hbuf : C'.buffer = C.buffer) :
      OpStep D hb C (.query r q v) C'
  /-- **OpDeliver**: silent; consumes a message from the buffer. -/
  | opDeliver {C : OpConfiguration D} {r : Replica} {m : D.Msg}
      {s : D.State}
      (h_inbuf : (r, m) ∈ C.buffer)
      (h_enabled : enabled hb C.trace r m)
      (h_s : C.replicas r = some s)
      (C' : OpConfiguration D)
      (htrace : C'.trace = C.trace ++ [(r, OpInput.deliver m, OpOutput.none)])
      (hreps : C'.replicas = fun r' =>
        if r' = r then some (D.effect m s) else C.replicas r')
      (hbuf : C'.buffer = C.buffer \ {(r, m)}) :
      OpStep D hb C (.deliver r m) C'

/-- The initial op-based configuration: empty trace, replica 0 at σ₀,
empty buffer. (Dynamic replicas — matching `initConfig` in
`CRDT_TS.lean`. Paper pins all of `R` to σ₀ up front; we relax for
symmetry with the state-based side.) -/
def opInitConfig (D : OpCRDTSig) : OpConfiguration D where
  trace := []
  replicas := fun r => if r = 0 then some D.init else none
  buffer := ∅

/-- Lift to a `LabeledTS`. The `hb` parameter is bound at the call
site — different causal-delivery orderings (Lamport, vector clocks,
dotted versions) produce different TSs. -/
def opLabeledTS (D : OpCRDTSig) (hb : D.Msg → D.Msg → Prop) : LabeledTS where
  State := OpConfiguration D
  Label := OpLabel D
  step := OpStep D hb
  silent := OpLabel.isSilent

end Sal.Emulation
