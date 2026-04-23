import Sal.Emulation.CRDT_Signature

/-!
# Labeled transition system for state-based CRDTs

A minimal TS for a state-based CRDT $\mathcal{D} =
\langle\Sigma, \sigma_0, \mathsf{do}, \mathsf{merge}, \mathsf{query},
\mathsf{rc}\rangle$. Configurations track, for each active replica, its
current state and the set of events it has seen. There is no version
graph and no LCA — 2-way merge acts pointwise.

Transition rules (one per constructor of `Step`):

* **CreateReplica**: introduce a fresh replica at state $\sigma_0$ with
  an empty event set.
* **Apply**: apply op `o` at replica `r`, generating an event
  `e = (t, r, o)` with a globally-fresh timestamp `t`.
* **Merge**: merge `r₂`'s state and event set into `r₁` pointwise; the
  visibility relation is unchanged.
* **Query**: observe replica `r` at query `q`; does not modify the
  configuration.

No transitions are silent; weak traces coincide with ordinary traces.
-/

namespace Sal.Emulation

open LabeledTS

/-- A configuration: per-replica head state, per-replica event set,
visibility relation over events. Invariant (not enforced at the type
level; enforced by the transition rules): `C.N r` is `some` iff
`C.L r` is `some`. -/
structure Configuration (D : CRDTSig) where
  N : Replica → Option D.State
  L : Replica → Option (Set (Op D.AppOp))
  vis : Op D.AppOp → Op D.AppOp → Prop

namespace Configuration

/-- Set of all events witnessed anywhere in the configuration. -/
def events {D : CRDTSig} (C : Configuration D) : Set (Op D.AppOp) :=
  fun e => ∃ r s, C.L r = some s ∧ s e

end Configuration

/-- Transition labels, one per transition rule. The `Query` label
carries its return value on the arrow. -/
inductive Label (D : CRDTSig) where
  | createReplica (r : Replica)
  | apply (t : Timestamp) (r : Replica) (o : D.AppOp)
  | merge (r₁ r₂ : Replica)
  | query (r : Replica) (q : D.Query) (v : D.Value)

/-- Point update of a `Replica → Option α` partial function. -/
def updateRep {α} (f : Replica → Option α) (r : Replica) (x : α) :
    Replica → Option α :=
  fun r' => if r' = r then some x else f r'

/-- The step relation. Source data (head state, event set) are passed
as `some _` witnesses in the premises, so no `Inhabited` assumption on
`D.State` is needed. -/
inductive Step (D : CRDTSig) : Configuration D → Label D → Configuration D → Prop where
  /-- **CreateReplica**: introduce a fresh replica at state σ₀. -/
  | createReplica {C : Configuration D} {r : Replica}
      (h_fresh : C.N r = none)
      (C' : Configuration D)
      (hN   : C'.N = updateRep C.N r D.init)
      (hL   : C'.L = updateRep C.L r ∅)
      (hvis : C'.vis = C.vis) :
      Step D C (.createReplica r) C'
  /-- **Apply**: apply op `o` at replica `r` with fresh timestamp `t`,
  generating an event `e = (t, r, o)`. -/
  | apply {C : Configuration D} {t : Timestamp} {r : Replica} {o : D.AppOp}
      {s : D.State} {ev : Set (Op D.AppOp)}
      (h_s       : C.N r = some s)
      (h_ev      : C.L r = some ev)
      (h_fresh_t : ∀ e, e ∈ C.events → Op.time e ≠ t)
      (C' : Configuration D)
      (hN   : C'.N = updateRep C.N r (D.update s (t, r, o)))
      (hL   : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
      (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o))) :
      Step D C (.apply t r o) C'
  /-- **Merge**: merge `r₂`'s state and event set into `r₁` pointwise. -/
  | merge {C : Configuration D} {r₁ r₂ : Replica}
      {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
      (h_s₁  : C.N r₁ = some s₁)
      (h_s₂  : C.N r₂ = some s₂)
      (h_ev₁ : C.L r₁ = some ev₁)
      (h_ev₂ : C.L r₂ = some ev₂)
      (C' : Configuration D)
      (hN   : C'.N = updateRep C.N r₁ (D.merge s₁ s₂))
      (hL   : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
      (hvis : C'.vis = C.vis) :
      Step D C (.merge r₁ r₂) C'
  /-- **Query**: observe replica `r` with query `q`. The return value
  `v` is recorded on the label; configuration is unchanged. -/
  | query {C : Configuration D} {r : Replica} {q : D.Query}
      {v : D.Value} {s : D.State}
      (h_s   : C.N r = some s)
      (h_val : v = D.query s q) :
      Step D C (.query r q v) C

/-- Initial configuration: a single replica `r₀ = 0` at state σ₀ with no
events seen and empty visibility. -/
def initConfig (D : CRDTSig) : Configuration D where
  N := fun r => if r = 0 then some D.init else none
  L := fun r => if r = 0 then some ∅ else none
  vis := fun _ _ => False

/-- Bundle the configuration/label/step data into a `LabeledTS`. -/
def labeledTS (D : CRDTSig) : LabeledTS where
  State := Configuration D
  Label := Label D
  step := Step D
  silent := fun _ => False

end Sal.Emulation
