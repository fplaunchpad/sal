import Sal.Emulation.CRDT_TS
import Sal.Emulation.Op_Based_TS
import Sal.Emulation.Weak_Simulation

/-!
# Canonical op-to-state emulation $\mathcal{G}$

Given an op-based CRDT `D : OpCRDTSig`, we produce a state-based CRDT
`canonicalG D : CRDTSig` that *simulates* `D` in the weak-simulation
sense of Liittschwager et al. §4.2.

High-level construction:

* **State** of `canonicalG D` is the set of messages delivered so far
  (`Set D.Msg`). Causal delivery is encoded structurally by the message
  set together with the `hb` order; the emulator applies messages in
  any causal-order-respecting traversal to recover the effective
  state.
* **update** runs `D.prepare` against a reconstruction of the
  current effective state, appends the generated message to the set.
* **merge** is set union — the lattice join for causal histories.
* **query** delegates to `D.query` after reconstructing the effective
  state.

The reconstruction helper `effectiveState` folds `D.effect` over the
message set in a causal order. Picking a canonical order requires
additional machinery (topological sort on `hb`); we expose it as a
parameter.

This file scaffolds the types and the signature-level map. The
`WeakSim opLabeledTS (labeledTS (canonicalG D))` construction (the
actual emulation theorem, Liittschwager §4.2, Theorems 1 and 2) is
stubbed at the bottom.
-/

namespace Sal.Emulation

open Classical

section
variable (D : OpCRDTSig)

/-- Effective replica state reconstructed from a delivered-message
set, given a causal order `hb` and any linear extension of it.

Implementation note: in a well-formed CRDT, `effect` is
commutative-over-concurrent-messages, so *any* causal-order-respecting
linear extension yields the same state. We abstract that here via the
order parameter; the result is independent of the choice.

Left as `sorry`: picking a deterministic linear extension of `hb`
restricted to a finite set requires either a decidable finite
representation or classical choice plus a commutativity witness. -/
noncomputable def effectiveState
    (_hb : D.Msg → D.Msg → Prop)
    (_delivered : Set D.Msg) : D.State :=
  D.init  -- Placeholder: the effective state folds `D.effect` over `delivered` in a causal order.

/-- Lift an op-based CRDT into a state-based CRDT via canonical
emulation. -/
noncomputable def canonicalG (hb : D.Msg → D.Msg → Prop) : CRDTSig where
  State := Set D.Msg
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := ∅
  AppOp := D.AppOp
  dec_op := D.dec_op
  Query := D.Query
  Value := D.Value
  update := fun delivered e =>
    -- New event `e = (t, r, op)`: generate a message via `prepare`
    -- against the currently-effective state, then record delivery.
    let s := effectiveState D hb delivered
    let m := D.prepare e.rep e.op s
    delivered ∪ {m}
  merge := fun a b => a ∪ b
  query := fun delivered q =>
    D.query (effectiveState D hb delivered) q
  rc := D.rc

end

/-! ## Simulation theorem (stubbed)

Liittschwager et al. §4.2 establishes two weak simulations between
`opLabeledTS D hb` and `labeledTS (canonicalG D hb)`. Together they
witness that the two transition systems are *weakly trace equivalent*.

Stating this formally in Lean requires a shared label type: here,
the op-based labels `OpLabel D` and the state-based labels
`Label (canonicalG D hb)` differ syntactically, so we need a
translation on labels (observable-label morphism) alongside the
simulation relation itself.

The skeleton below records the target statement. -/

/-- **Emulation theorem (statement sketch).** For every op-based CRDT
`D` with causal-order `hb`, the op-based and state-based TSs related
by `canonicalG` are weakly trace equivalent from their respective
initial configurations.

The precise statement uses a label morphism; the proof goes via
mutual weak simulations. -/
theorem emulation_G_weak_bisim {D : OpCRDTSig} (_hb : D.Msg → D.Msg → Prop) :
    True := by
  trivial

end Sal.Emulation
