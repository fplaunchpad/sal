import Sal.MRDTs.Paper1.Automation.GenericMaskCanonical
import Sal.MRDTs.Paper1.Automation.PolicyExpansionAutomation

/-! A mask description contains only carrier, update, birth and kill mappings.
The proof fields are derived from their registered definitions. No datatype
correctness theorem, canonical replay adapter or history invariant is selected.
-/
register_simp_attr mask_implementation

namespace Sal.MRDTs.Paper1.Automation.MaskKitAutomation
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1

structure Description (D : MRDTSig) (P : OperationPolicy D.AppOp) (Record : Type)
    [DecidableEq Record] where
  carrier : D.State → Finset Record
  step : Finset Record → Op D.AppOp → Finset Record
  birth : Record → Op D.AppOp
  kill : Record → Op D.AppOp → Prop

theorem irreflexive_of_strictStamp {Event : Type} (vis : Event → Event → Prop)
    (stamp : Event → Nat) (mono : ∀ a b, vis a b → stamp a < stamp b) :
    ∀ a, ¬vis a a := by
  intro a self
  exact Nat.lt_irrefl _ (mono a a self)

open Lean Elab Tactic Meta in
elab "mask_open_certificate" : tactic => do
  let target ← getMainTarget
  if target.getAppFn.isConstOf ``InductiveMask.UpdateCertificate then
    evalTactic (← `(tactic| constructor))

/-- Definition-driven finite mask laws; the shared policy backend handles
constructor decomposition, pointwise equalities and noncommutation witnesses. -/
macro "mask_auto" : tactic => `(tactic| (
  mask_open_certificate
  policy_preprocess
  all_goals try simp_all [mask_implementation, Function.Injective]
  all_goals first
  | (solve | simp [mask_implementation, Function.Injective])
  | policy_auto))

/-- Synthesize all seven proof fields from a four-mapping description. -/
macro "derive_mask_kit" " using " description:term : tactic => `(tactic| (
  refine {
    carrier := ($description).carrier
    step := ($description).step
    birth := ($description).birth
    kill := ($description).kill
    injective := ?_
    empty := ?_
    projection := ?_
    update := ?_
    commutes_notkill := ?_
    noncomm_kill := ?_
    killer_shape := ?_ }
  all_goals mask_auto))

/-- Project existing semantic representation evidence by definition unfolding
and ordinary structural logic. Timestamp decrease supplies irreflexivity. -/
macro "mask_shape" : tactic => `(tactic| (
  intros
  simp (config := { zetaDelta := true }) only
    [MaskCanonical.Shape, InductiveMask.Alive, ConcreteMRDT.Supported,
      Sal.MRDTs.Foundation.Op.time, mask_implementation] at *
  first
  | (solve | aesop (add safe apply irreflexive_of_strictStamp))
  | grind))

end Sal.MRDTs.Paper1.Automation.MaskKitAutomation
