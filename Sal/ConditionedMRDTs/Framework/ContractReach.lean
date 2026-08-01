/-!
# Contract-indexed reachability

The generic reflexive-transitive closure used by both ordinary and virtual-LCA
honest reachability.  Keeping this independent of the MRDT execution model
makes it reusable by paired simulations and future internal runtime steps.
-/

namespace Sal.ConditionedMRDTs

/-- Reachability whose every outgoing step is licensed by a predicate on its
source configuration. -/
inductive ContractReach {Cfg Label : Type} (init : Cfg)
    (Step : Cfg → Label → Cfg → Prop) (H : Cfg → Prop) : Cfg → Prop where
  | init : ContractReach init Step H init
  | step {C C' : Cfg} {ℓ : Label} :
      ContractReach init Step H C → H C → Step C ℓ C' →
      ContractReach init Step H C'

/-- The generic invariant induction consumed by all specialized reachability
metatheorems. -/
theorem ContractReach.invariant {Cfg Label : Type} {init : Cfg}
    {Step : Cfg → Label → Cfg → Prop} {H I : Cfg → Prop}
    (hInit : I init)
    (hStep : ∀ {C C' ℓ}, I C → H C → Step C ℓ C' → I C')
    {C : Cfg} (hReach : ContractReach init Step H C) : I C := by
  induction hReach with
  | init => exact hInit
  | step _ hH hs ih => exact hStep ih hH hs

end Sal.ConditionedMRDTs
