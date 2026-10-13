import Sal.MRDTs.Paper1.Automation.PolicyExpansionAutomation
import Sal.MRDTs.Paper1.Automation.GenericPolicyExpansion
import Sal.MRDTs.Paper1.Automation.MaskKitAutomation
import Sal.MRDTs.Paper1.Automation.PolicyKitAutomation
import Sal.MRDTs.Paper1.GuardedRawORSetReplay

/-! Efficient OR-set descriptions and raw-definition annotations. Shared
automation constructs the template certificates and discharges their finite
laws; no datatype correctness theorem or replay adapter is supplied. -/
namespace Sal.MRDTs.Paper1.Automation.AutomatedEfficientORSet
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Instances.EfficientORSet
open ConcreteMRDT
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000

def signature : Signature := LocalAssembly.ofMRDT (D α) rc.order
attribute [local policy_expansion_simps] signature LocalAssembly.ofMRDT D update merge rc
  EfficientORSet.EventSpec.conflict Op.op Op.rep Op.time

theorem diagonal (l a : State α) : merge l a l = a := by
  policy_auto

theorem comm (l a b : State α) : merge l a b = merge l b a := by
  policy_auto

theorem initial (s : State α) : (D α).merge (D α).init (D α).init s = s := by
  policy_auto

theorem fresh_base : (signature (α := α)).fresh_base := by
  policy_auto

theorem fresh_step : (signature (α := α)).fresh_step := by
  policy_auto

theorem local_common : (signature (α := α)).local_common_opposite := by
  policy_auto

theorem local_opposite : (signature (α := α)).local_opposite_fresh := by
  policy_auto

theorem local_empty : (signature (α := α)).local_empty_past := by
  policy_auto

theorem local_singleton : (signature (α := α)).local_past_singleton := by
  policy_auto

theorem causal_common : (signature (α := α)).causal_common_kernel := by
  policy_auto

theorem causal_commuting : (signature (α := α)).causal_commuting_kernel := by
  policy_auto

theorem causal_strict : (signature (α := α)).causal_strict_kernel := by
  policy_auto

theorem causal_absorber : (signature (α := α)).causal_absorber_kernel := by
  policy_auto

def birth (p : Record α) : Event α := (p.2.1,p.1,.add p.2.2)
attribute [local policy_expansion_simps] birth kills
attribute [local mask_implementation] birth kills
attribute [local mask_implementation] D update
attribute [local mask_implementation] EfficientORSet.RawReplay.representation
  EfficientORSet.ConcreteRep.representation Represents live dead

theorem mask_update : InductiveMask.UpdateCertificate (update (α := α))
     (fun p e => e = birth p) (fun p e => kills p.1 p.2.2 e) := by
  mask_auto

theorem mask_commuting (p : Record α) (e : Event α)
     (no : ¬kills p.1 p.2.2 e) : (D α).toUpdateSig.commutes (birth p) e := by
  mask_auto

theorem mask_noncomm (p : Record α) (e : Event α)
     (different : (birth p).time ≠ e.time) (kill : kills p.1 p.2.2 e) :
     ¬ (D α).toUpdateSig.commutes (birth p) e := by
  mask_auto

def maskDescription : MaskKitAutomation.Description (D α) (EfficientORSet.EventSpec.conflict α) (Record α) where
  carrier := id
  step := update
  birth := birth
  kill := fun p e => kills p.1 p.2.2 e
attribute [local mask_implementation] maskDescription
attribute [local policy_expansion_simps] maskDescription

def maskKit : MaskCanonical.Kit (D α) (EfficientORSet.EventSpec.conflict α) (Record α) := by
  derive_mask_kit using maskDescription
attribute [local mask_implementation] maskKit

theorem semantic_shape (C : ReplayContext (D α).toUpdateSig) (H : Set (Event α)) (s : State α)
     (rep : EfficientORSet.RawReplay.representation C H s) :
     MaskCanonical.Shape (maskKit (α := α)) C H s := by
  mask_shape

def element : SetOp α → α
  | .add x | .remove x => x
attribute [local policy_expansion_simps] element

theorem commute_distinct_elements (a b : Op (SetOp α))
    (ne : element a.2.2 ≠ element b.2.2) : (D α).toUpdateSig.commutes a b := by
  policy_auto

theorem conflict_classification (a b : Op (SetOp α))
    (nc : ¬ (D α).toUpdateSig.commutes a b) :
    rc.order a b = .Fst_then_snd ∨ rc.order b a = .Fst_then_snd ∨ a.rep = b.rep := by
  policy_auto

theorem remove_add_noncomm (et er ct cr : Nat) (x : α) :
    ¬ (D α).toUpdateSig.commutes (et,er,.remove x) (ct,cr,.add x) := by
  policy_auto

theorem absorber_classification (e h c : Op (SetOp α))
    (prior : rc.order e h = .Fst_then_snd)
    (nc : ¬ (D α).toUpdateSig.commutes h c) :
    rc.order c h = .Fst_then_snd ∨
      (rc.order e c = .Fst_then_snd ∧ ¬ (D α).toUpdateSig.commutes e c) := by
  policy_auto

theorem strict_asymmetric (a b : Op (SetOp α)) (prior : rc.order a b = .Fst_then_snd) :
    rc.order b a ≠ .Fst_then_snd := by
  policy_auto

theorem policy_order (a b : Op (SetOp α)) :
    rc.order a b = .Fst_then_snd ↔ (EfficientORSet.EventSpec.conflict α).before a.op b.op := by
  policy_auto

omit [DecidableEq α] in
theorem no_chain (a b c : Op (SetOp α)) :
    ¬ ((EfficientORSet.EventSpec.conflict α).before a.op b.op ∧ (EfficientORSet.EventSpec.conflict α).before b.op c.op) := by
  policy_auto

theorem commute_nonconflict (a b : Op (SetOp α))
    (absent : ¬ ((EfficientORSet.EventSpec.conflict α).before a.op b.op ∨ (EfficientORSet.EventSpec.conflict α).before b.op a.op))
    (ne : a.rep ≠ b.rep) : (D α).toUpdateSig.commutes a b := by
  policy_auto

theorem guarded_noncomm (a b : Event α) (ne : a.rep ≠ b.rep) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      (EfficientORSet.EventSpec.conflict α).before a.op b.op ∨ (EfficientORSet.EventSpec.conflict α).before b.op a.op := by
  policy_auto

theorem conditional_base : (signature (α := α)).ConditionalBase := by
  policy_auto

theorem kernel_stable : (signature (α := α)).KernelStable := by
  policy_auto

def kit : PolicyExpansion.Kit (D α) (EfficientORSet.EventSpec.conflict α) rc.order := by
  derive_policy_kit

end Sal.MRDTs.Paper1.Automation.AutomatedEfficientORSet
