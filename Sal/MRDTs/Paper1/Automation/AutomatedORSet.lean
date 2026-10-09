import Sal.MRDTs.Paper1.Automation.PolicyExpansionAutomation
import Sal.MRDTs.Paper1.Automation.GenericPolicyExpansion
import Sal.MRDTs.Paper1.GuardedRawORSetReplay

/-! Ordinary OR-set: explicit raw-definition annotations and finite operation
cases feed reusable equation templates. No old datatype VC or invariant proof. -/
namespace Sal.MRDTs.Paper1.Automation.AutomatedORSet
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ORSet
open ConcreteMRDT
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000

def signature : Signature := LocalAssembly.ofMRDT (D α) ORSet.order
attribute [local policy_expansion_simps] signature LocalAssembly.ofMRDT D step merge ORSet.order

theorem diagonal (l a : State α) : merge l a l = a := by policy_finite
theorem comm (l a b : State α) : merge l a b = merge l b a := by policy_finite
theorem initial (s : State α) : (D α).merge (D α).init (D α).init s = s := by policy_finite

theorem fresh_base : (signature (α := α)).fresh_base := by
  rintro ⟨t,r,op⟩; cases op <;> policy_finite
theorem fresh_step : (signature (α := α)).fresh_step := by
  rintro s ⟨t,r,op⟩ ⟨u,q,other⟩ distinct previous
  cases op <;> cases other <;> policy_finite
theorem local_common : (signature (α := α)).local_common_opposite := by
  rintro l B b ⟨t,r,op⟩ ⟨u,q,other⟩ previous s
  have base := previous (∅ : State α)
  cases op <;> cases other <;> policy_finite
theorem local_opposite : (signature (α := α)).local_opposite_fresh := by
  rintro l B b ⟨t,r,op⟩ ⟨u,q,other⟩ freshE freshH previous s
  have base := previous (∅ : State α)
  cases op <;> cases other <;> policy_finite
theorem local_empty : (signature (α := α)).local_empty_past := by
  rintro l b ⟨t,r,op⟩ fresh s
  cases op <;> policy_finite
theorem local_singleton : (signature (α := α)).local_past_singleton := by
  rintro l B b ⟨t,r,op⟩ ⟨u,q,other⟩ fresh previous singleton s
  have base := previous (∅ : State α)
  have one := singleton (∅ : State α)
  cases op <;> cases other <;> policy_finite
theorem causal_common : (signature (α := α)).causal_common_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ previous
  cases op <;> cases other <;> policy_finite
theorem causal_commuting : (signature (α := α)).causal_commuting_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ commuting previous
  have commuteEmpty := commuting (∅ : State α)
  cases op <;> cases other <;> policy_finite
theorem causal_strict : (signature (α := α)).causal_strict_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ fresh previous strict
  cases op <;> cases other <;> policy_finite
theorem causal_absorber : (signature (α := α)).causal_absorber_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ ⟨v,z,last⟩ strict reset
  cases op <;> cases other <;> cases last <;> policy_finite

attribute [local policy_expansion_simps] conflict Op.op Op.rep
theorem policy_order (a b : Op (Update α)) :
    ORSet.order a b = .Fst_then_snd ↔ (conflict α).before a.op b.op := by
  rcases a with ⟨t,r,op⟩; rcases b with ⟨u,q,other⟩
  cases op <;> cases other <;> simp [ORSet.order,conflict,Op.op,ite_eq_iff]
  exact eq_comm
omit [DecidableEq α] in
theorem no_chain (a b c : Op (Update α)) :
    ¬ ((conflict α).before a.op b.op ∧ (conflict α).before b.op c.op) := by
  rcases a with ⟨t,r,op⟩; rcases b with ⟨u,q,other⟩; rcases c with ⟨v,z,last⟩
  cases op <;> cases other <;> cases last <;> simp [conflict,Op.op]
theorem commute_nonconflict (a b : Op (Update α))
    (absent : ¬ ((conflict α).before a.op b.op ∨ (conflict α).before b.op a.op)) :
    (D α).toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨t,r,op⟩; rcases b with ⟨u,q,other⟩
  cases op <;> cases other <;> policy_finite
theorem noncomm_full (a b : Op (Update α)) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      (conflict α).before a.op b.op ∨ (conflict α).before b.op a.op := by
  classical
  constructor
  · intro nc; by_contra absent; exact nc (commute_nonconflict a b absent)
  · rintro (⟨x,remove,add⟩ | ⟨x,remove,add⟩) commuting
    all_goals simp only [Op.op] at remove add
    all_goals have empty := commuting (∅ : State α)
    · have member := Finset.ext_iff.mp empty (x,b.1)
      simp [D,step,remove,add] at member
    · have member := Finset.ext_iff.mp empty (x,a.1)
      simp [D,step,remove,add] at member
theorem conditional_base : (signature (α := α)).ConditionalBase := by
  rintro s a b c before nc
  have strict := (policy_order a b).mp before
  have clash := (noncomm_full b c).mp nc
  rcases a with ⟨t,r,op⟩; rcases b with ⟨u,q,other⟩; rcases c with ⟨v,z,last⟩
  cases op <;> cases other <;> cases last <;> policy_finite
theorem kernel_stable : (signature (α := α)).KernelStable := by
  rintro s t ⟨u,q,op⟩ ⟨v,z,other⟩ previous
  cases op <;> cases other <;> policy_finite

def kit : PolicyExpansion.Kit (D α) (conflict α) ORSet.order where
  comm := comm
  initial := initial
  shared := fun t₀ t₁ t₂ B e => collection_shared t₀ t₁ t₂ B ((D α).update B e)
  localKernels := ⟨Signature.local_empty_sides_of_diagonal signature diagonal,
    local_common,local_opposite,fresh_base,fresh_step,local_empty,local_singleton⟩
  causalKernels := ⟨Signature.causal_base_of_diagonal signature comm diagonal,
    causal_common,causal_commuting,causal_strict,causal_absorber,fresh_base,fresh_step⟩
  eventCertificate := by
    constructor
    · intro a b nc
      rcases (noncomm_full a b).mp nc with ab | ba
      · exact Or.inl ((policy_order a b).mpr ab)
      · exact Or.inr (Or.inl ((policy_order b a).mpr ba))
    · intro e h c eh nc
      rcases (noncomm_full h c).mp nc with hc | ch
      · exact False.elim (no_chain e h c ⟨(policy_order e h).mp eh,hc⟩)
      · exact Or.inl ((policy_order c h).mpr ch)
    · intro a b ab ba
      exact no_chain a b a ⟨(policy_order a b).mp ab,(policy_order b a).mp ba⟩
  noncomm_exact := fun a b _ _ => noncomm_full a b
  noChain := no_chain
  policy_order := policy_order
  conditionalBase := conditional_base
  kernelStable := kernel_stable


end Sal.MRDTs.Paper1.Automation.AutomatedORSet
