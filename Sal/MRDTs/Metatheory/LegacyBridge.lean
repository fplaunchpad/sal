import Sal.MRDTs.Framework.StateGC
import Sal.ConditionedMRDTs.Metatheory.LCA_Lemma

/-!
# Temporary migration bridge

This module is permitted only on the refactoring branch.  It establishes that
dropping vacuous signature conditioning and the stored `ver_inv` proof does
not change operational data.  Production modules must not depend on it at the
final cutover.
-/

namespace Sal.MRDTs

open Sal.Emulation

namespace LegacyBridge

abbrev OldSig := Sal.ConditionedMRDTs.ConditionedMRDTSig
abbrev OldConfiguration := Sal.ConditionedMRDTs.Configuration

/-- Forget signature-level conditioning without changing the datatype. -/
def signature (D : OldSig) : MRDTSig where
  toCRDTSig := D.toCRDTSig
  mergeL := D.mergeL
  merge_init_slice := D.merge_init_slice

/-- Forget only the proof that every registered state satisfies `D.Inv`. -/
def eraseConfiguration {D : OldSig}
    (C : OldConfiguration D) : Configuration (signature D) where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  ver := C.ver
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := C.ver_init
  head_coherent := C.head_coherent
  lca_events := C.lca_events

/-- Flat signatures can temporarily recover the old proof-carrying
configuration.  The need for `invEverywhere` is exactly why this bridge must
not become the new public API. -/
def liftConfiguration (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (C : Configuration (signature D)) : OldConfiguration D where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  ver := C.ver
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := C.ver_init
  head_coherent := C.head_coherent
  ver_inv := fun _ s _ _ => invEverywhere s
  lca_events := C.lca_events

@[simp] theorem erase_lift (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (C : Configuration (signature D)) :
    eraseConfiguration (liftConfiguration D invEverywhere C) = C := rfl

@[simp] theorem lift_erase_data {D : OldSig} (invEverywhere : ∀ s, D.Inv s)
    (C : OldConfiguration D) :
    eraseConfiguration (liftConfiguration D invEverywhere
      (eraseConfiguration C)) = eraseConfiguration C := rfl

@[simp] theorem erase_init (D : OldSig) (hInit : D.Inv D.init) :
    eraseConfiguration (Sal.ConditionedMRDTs.initConfig D hInit) =
      initConfig (signature D) := rfl

/-- Erasing proof-only conditioning maps every old raw step to the new raw
step with the same label and operational data. -/
theorem erase_step {D : OldSig} {C C' : OldConfiguration D}
    {l : Sal.ConditionedMRDTs.Label3 D}
    (h : Sal.ConditionedMRDTs.Step3 D C l C') :
    Step (signature D) (eraseConfiguration C)
      (match l with
        | .createReplica r => .createReplica r
        | .apply t r o => .apply t r o
        | .merge r₁ r₂ => .merge r₁ r₂
        | .query r q v => .query r q v)
      (eraseConfiguration C') := by
  cases h with
  | createReplica fresh C' hN hL hvis hver hhead hparents =>
      exact .createReplica fresh _ hN hL hvis hver hhead hparents
  | apply hhead hver ht hs hv hr C' hN hL hvis hver' hhead' hparents =>
      exact .apply hhead hver ht hs hv hr _ hN hL hvis hver' hhead' hparents
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT
      hh₁ hh₂ hv₁ hv₂ hlca hvT hvm hr₁ hr₂ C'
      hN hL hvis hver hhead hparents =>
      have hlca' : IsLCA C.parents v₁ v₂ vT := by
        simpa [IsLCA, Reaches, Sal.ConditionedMRDTs.IsLCA,
          Sal.ConditionedMRDTs.Reaches] using hlca
      exact .merge hh₁ hh₂ hv₁ hv₂ hlca' hvT hvm hr₁ hr₂ _
        hN hL hvis hver hhead hparents
  | query hs hv => exact .query hs hv

/-- For a flat legacy signature, every new raw step can be reflected into the
old proof-carrying semantics. -/
theorem lift_step (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    {C C' : Configuration (signature D)} {l : Label (signature D)}
    (h : Step (signature D) C l C') :
    Sal.ConditionedMRDTs.Step3 D
      (liftConfiguration D invEverywhere C)
      (match l with
        | .createReplica r => .createReplica r
        | .apply t r o => .apply t r o
        | .merge r₁ r₂ => .merge r₁ r₂
        | .query r q v => .query r q v)
      (liftConfiguration D invEverywhere C') := by
  cases h with
  | createReplica fresh C' hN hL hvis hver hhead hparents =>
      exact .createReplica fresh _ hN hL hvis hver hhead hparents
  | apply hhead hver ht hs hv hr C' hN hL hvis hver' hhead' hparents =>
      exact .apply hhead hver ht hs hv hr _ hN hL hvis hver' hhead' hparents
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT
      hh₁ hh₂ hv₁ hv₂ hlca hvT hvm hr₁ hr₂ C'
      hN hL hvis hver hhead hparents =>
      have hlca' : Sal.ConditionedMRDTs.IsLCA C.parents v₁ v₂ vT := by
        simpa [IsLCA, Reaches, Sal.ConditionedMRDTs.IsLCA,
          Sal.ConditionedMRDTs.Reaches] using hlca
      exact .merge hh₁ hh₂ hv₁ hv₂ hlca' hvT hvm hr₁ hr₂ _
        hN hL hvis hver hhead hparents
  | query hs hv => exact .query hs hv

end LegacyBridge

end Sal.MRDTs
