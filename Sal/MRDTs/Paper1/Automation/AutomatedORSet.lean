import Sal.MRDTs.Paper1.Automation.PolicyKitAutomation
import Sal.MRDTs.Paper1.Automation.GenericPolicyExpansion
import Sal.MRDTs.Paper1.GuardedRawORSetReplay

/-! Ordinary OR-set: raw-definition annotations feed shared finite proof search.
The shared tactic discovers operation cases and instantiates the templates. -/
namespace Sal.MRDTs.Paper1.Automation.AutomatedORSet
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ORSet
open ConcreteMRDT
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000

def signature : Signature := LocalAssembly.ofMRDT (D α) ORSet.order
attribute [local policy_expansion_simps] signature LocalAssembly.ofMRDT D step merge ORSet.order

theorem diagonal (l a : State α) : merge l a l = a := by policy_auto
theorem comm (l a b : State α) : merge l a b = merge l b a := by policy_auto
theorem initial (s : State α) : (D α).merge (D α).init (D α).init s = s := by policy_auto

theorem fresh_base : (signature (α := α)).fresh_base := by policy_auto

theorem fresh_step : (signature (α := α)).fresh_step := by policy_auto

theorem local_common : (signature (α := α)).local_common_opposite := by policy_auto

theorem local_opposite : (signature (α := α)).local_opposite_fresh := by policy_auto

theorem local_empty : (signature (α := α)).local_empty_past := by policy_auto

theorem local_singleton : (signature (α := α)).local_past_singleton := by policy_auto

theorem causal_common : (signature (α := α)).causal_common_kernel := by policy_auto

theorem causal_commuting : (signature (α := α)).causal_commuting_kernel := by policy_auto

theorem causal_strict : (signature (α := α)).causal_strict_kernel := by policy_auto

theorem causal_absorber : (signature (α := α)).causal_absorber_kernel := by policy_auto

attribute [local policy_expansion_simps] conflict Op.op Op.rep
theorem policy_order (a b : Op (Update α)) :
    ORSet.order a b = .Fst_then_snd ↔ (conflict α).before a.op b.op := by policy_auto

omit [DecidableEq α] in
theorem no_chain (a b c : Op (Update α)) :
    ¬ ((conflict α).before a.op b.op ∧ (conflict α).before b.op c.op) := by policy_auto

theorem commute_nonconflict (a b : Op (Update α))
    (absent : ¬ ((conflict α).before a.op b.op ∨ (conflict α).before b.op a.op)) :
    (D α).toUpdateSig.commutes a b := by policy_auto

theorem noncomm_full (a b : Op (Update α)) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      (conflict α).before a.op b.op ∨ (conflict α).before b.op a.op := by policy_auto

theorem conditional_base : (signature (α := α)).ConditionalBase := by policy_auto

theorem kernel_stable : (signature (α := α)).KernelStable := by policy_auto

def kit : PolicyExpansion.Kit (D α) (conflict α) ORSet.order := by
  derive_policy_kit

end Sal.MRDTs.Paper1.Automation.AutomatedORSet
