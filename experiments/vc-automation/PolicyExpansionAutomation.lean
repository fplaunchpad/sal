import PolicyExpansionRules
import CausalCoverage
import SharedExpansion

/-! Only generic equation definitions belong to this registry. Instances
register raw implementation definitions locally; no datatype proof is selected. -/
open NeemExpansion
attribute [policy_expansion_simps]
  Signature.distinct Signature.comm Signature.CausalEquation
  Signature.LocalEquation Signature.FreshEquation Signature.Commutes
  Signature.commutes Signature.KernelStable Signature.ConditionalBase

/-- Convert finite-set equality assumptions into membership formulas before
solving the finite Boolean equations. Constructor splitting stays explicit. -/
macro "policy_finite" : tactic => `(tactic| (
  try simp only [policy_expansion_simps] at *
  all_goals ext p
  all_goals try simp only [Finset.ext_iff] at *
  all_goals try simp_all [policy_expansion_simps]
  all_goals grind (splits := 20) only))
