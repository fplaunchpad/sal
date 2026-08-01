import Sal.Emulation.Emulation
import Sal.ConditionedMRDTs.Metatheory.VerifiedMRDT

/-!
# Conditioned endpoint of the Shapiro emulator

The construction itself remains a reusable binary state-based machine. This
module embeds it as a flat ternary MRDT and makes the representation invariant
the conditioned state invariant. A completed emulation proof will consume a
`VerifiedMRDT` for this signature, never the retired 24-VC bridge.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs

variable (D : OpCRDTSig) {hb : D.Msg → D.Msg → Prop}

/-- The Shapiro state machine as a conditioned MRDT. Its ternary merge is the
binary state-based merge (the LCA is irrelevant to this emulation layer), and
its invariant is exactly `D ⊆ M`. -/
def shapiroConditionedG (sched : CausalSchedule D hb) : ConditionedMRDTSig where
  toMRDTSig :=
    { toCRDTSig := shapiroG D sched
      mergeL := fun _l a b => (shapiroG D sched).merge a b
      merge_init_slice := fun _ _ => rfl }
  Inv := EmulatorState.Invariant hb
  applicable := fun e x =>
    EmulatorState.PrepareEnabled hb x (D.prepare e.rep e.op x.materialized)

/-- The required certification endpoint for operation-to-state transfer. -/
abbrev ShapiroVerified (sched : CausalSchedule D hb) :=
  VerifiedMRDT (shapiroConditionedG D sched)

theorem shapiroConditioned_initInv (sched : CausalSchedule D hb) :
    (shapiroConditionedG D sched).Inv (shapiroConditionedG D sched).init := by
  constructor
  · exact EmulatorState.wellFormed_init
  · intro m hm
    change m ∈ (∅ : Finset D.Msg) at hm
    simp at hm

theorem shapiroConditioned_updateInv (sched : CausalSchedule D hb)
    {x : EmulatorState D} (hx : (shapiroConditionedG D sched).Inv x)
    (e : Op D.AppOp) :
    (shapiroConditionedG D sched).applicable e x →
    (shapiroConditionedG D sched).Inv
      ((shapiroConditionedG D sched).update x e) := by
  intro he
  exact EmulatorState.invariant_prepare hx he

theorem shapiroConditioned_mergeInv (sched : CausalSchedule D hb)
    (x y : EmulatorState D) :
    (shapiroConditionedG D sched).Inv
      ((shapiroConditionedG D sched).merge x y) :=
  EmulatorState.invariant_drain sched x _

end Sal.Emulation
