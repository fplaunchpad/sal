import Sal.ConditionedMRDTs.MRDT_Instances.ORSetCore.ORSetCore

/-!
# The Peritext mark store: an `ORSetCore` instantiation (composition level L0)

The flat component of the tombstone-free Peritext composite
`Peritext_Composed := RGA_TF ⊗ MarkStore` (memo `Development/COMPOSITION_PENPAPER.md`
§4). A mark record is inert data:

* `markId`, the identity `remMark` targets (production OR-set semantics:
  removing a mark kills every live record of its id, adds win over concurrent
  removes);
* `markType`, bold/italic/comment/… (an opaque `ℕ` code);
* two endpoints, each a **character id plus its recorded ancestor path**, read
  off the issuer's RGA component at generation time. The store never
  dereferences them, resolution happens at read time against the RGA
  component (`Render.lean`), which is exactly what makes the coupling free
  (memo §3.4): no update, merge, or guard reads across components.

Everything below is instantiation: the payload-parametric OR-set core
(`ORSetCore.lean`) supplies the full convergence discharge
(`CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3 ⇒ JoinLemma3`), and the
closure ladder (`joinLemma3F_of_joinLemma3`, `joinLemma3C_full`) repackages it
as the `JoinLemma3C _ (fullClosure _)` certificate the product `≈`-capstone's
`hJoin₂` premise consumes. `Inv` and `applicable` are `⊤` (the store is
unguarded, mark convergence needs no contract; memo §4 "mark ops are
unguarded for convergence").
-/

namespace Sal.ConditionedMRDTs.Peritext_Composed

open Sal.Emulation

/-- A mark record:
`(markId, markType, (startChar, startPath), (endChar, endPath))`, the
endpoint character **ids plus their recorded paths** (data, not references;
the paths feed the RGA's own `resolve` at read time). -/
abbrev MarkPayload : Type := ℕ × ℕ × (ℕ × List ℕ) × (ℕ × List ℕ)

/-- The removal key of a mark record: its `markId`. `remMark k` removes every
live record of id `k`; concurrent `addMark`/`remMark` on the same id is
add-wins (`osRc`). -/
def markKey (m : MarkPayload) : ℕ := m.1

/-- Mark-store operations: `OSOp.add record` / `OSOp.rem markId`. -/
abbrev MarkOp : Type := OSOp MarkPayload

/-- Mark-store state: the finite set of live `(ts, rep, record)` instances. -/
abbrev MarkState : Type := OSState MarkPayload

/-- **The mark store**: the payload-parametric OR-set core at `MarkPayload`,
keyed by `markId`. The query observes the live record set (the read layer's
input); `Inv = applicable = ⊤`. -/
def MarkStore : ConditionedMRDTSig :=
  OSCore MarkPayload markKey Unit MarkState (fun s _ => s)

/-- `Inv` is total, the product capstone's `hInvT₂`. -/
theorem markInvT : ∀ s : MarkStore.State, MarkStore.Inv s := fun _ => trivial

/-- `applicable` is total, mark delivery is unguarded. -/
theorem markAppT : ∀ (o : Op MarkStore.AppOp) (s : MarkStore.State),
    MarkStore.applicable o s := fun _ _ => trivial

/-- The mark store's ternary Join Lemma, pure `ORSetCore` instantiation,
zero new convergence obligations (composition level L0). -/
theorem markStore_joinLemma3 : JoinLemma3 MarkStore :=
  OSCore_joinLemma3

/-- **The `hJoin₂` certificate**: the mark store's Join Lemma at full closure,
via the closure ladder (`JoinLemma3 → JoinLemma3F → JoinLemma3C fullClosure`,
both steps definitional). This is the exact premise shape
`prod_ra_linearizable_up_to_eq_H` consumes for the flat component. -/
theorem markStore_joinLemma3C_full :
    JoinLemma3C MarkStore (fullClosure MarkStore.toCRDTSig) :=
  (joinLemma3C_full MarkStore).mpr (joinLemma3F_of_joinLemma3 markStore_joinLemma3)

/-! ## Axiom audit -/

#print axioms markStore_joinLemma3C_full

end Sal.ConditionedMRDTs.Peritext_Composed
