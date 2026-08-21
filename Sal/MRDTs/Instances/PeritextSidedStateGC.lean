import Sal.MRDTs.Metatheory.LegacyBridge
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Sided.PeritextSided_Interaction

/-!
# Sided Peritext state-GC capability

Temporary adapter during the source-tree cutover.  The public result has the
new `StateGCProtocol` type; its body reuses the existing checked combined
commit-GC/state-GC/virtual-LCA interaction proof.
-/

namespace Sal.MRDTs.Instances.PeritextSided

open Sal.MRDTs Sal.MRDTs.LegacyBridge
open Sal.EmbedRGA

noncomputable def invEverywhere (Γ : OrderedPrefixCode) :
    ∀ s, (Sal.ConditionedMRDTs.PeritextSided.Core Γ).Inv s := by
  intro s
  exact ⟨trivial, trivial, trivial⟩

abbrev D (Γ : OrderedPrefixCode) : MRDTSig :=
  signature (Sal.ConditionedMRDTs.PeritextSided.Core Γ)

noncomputable def resolver (Γ : OrderedPrefixCode) : VirtualLCAResolver (D Γ) :=
  virtualLCA (Sal.ConditionedMRDTs.PeritextSided.Core Γ) (invEverywhere Γ)

def mapLabel {Γ : OrderedPrefixCode} :
    Option (Sal.ConditionedMRDTs.Label3
      (Sal.ConditionedMRDTs.PeritextSided.Core Γ)) → Option (Label (D Γ)) :=
  Option.map eraseLabel

def PhysicalStep (Γ : OrderedPrefixCode)
    (S : Sal.ConditionedMRDTs.PeritextSided.Interaction.CombinedConfig Γ)
    (l : Option (Label (D Γ)))
    (T : Sal.ConditionedMRDTs.PeritextSided.Interaction.CombinedConfig Γ) : Prop :=
  ∃ old, mapLabel old = l ∧
    Sal.ConditionedMRDTs.PeritextSided.Interaction.CombinedStepV Γ S old T

noncomputable def stateGC (Γ : OrderedPrefixCode) :
    StateGCProtocol (D Γ) (resolver Γ) where
  Physical := Sal.ConditionedMRDTs.PeritextSided.Interaction.CombinedConfig Γ
  semantic := fun S => eraseConfiguration S.semantic.core
  Valid := Sal.ConditionedMRDTs.PeritextSided.Interaction.CombinedConfig.WellFormed
  PhysicalStep := PhysicalStep Γ
  valid_preserved := by
    intro S T l hvalid hstep
    obtain ⟨old, _, hold⟩ := hstep
    exact hold.wellFormed
  silent_stutters := by
    intro S T hvalid hstep
    obtain ⟨old, hmap, hold⟩ := hstep
    cases old with
    | none =>
        exact congrArg eraseConfiguration hold.core_step
    | some old => simp [mapLabel] at hmap
  visible_refines := by
    intro S T l hvalid hstep
    obtain ⟨old, hmap, hold⟩ := hstep
    cases old with
    | none => simp [mapLabel] at hmap
    | some old =>
        simp [mapLabel] at hmap
        subst l
        exact erase_stepV (Sal.ConditionedMRDTs.PeritextSided.Core Γ)
          (invEverywhere Γ)
          hold.core_step

#print axioms stateGC

end Sal.MRDTs.Instances.PeritextSided
