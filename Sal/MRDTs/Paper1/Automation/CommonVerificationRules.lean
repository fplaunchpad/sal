import Mathlib.Tactic

/-! The common command selects declarative inputs, never completed VC proofs. -/
declare_aesop_rule_sets [MRDTVerification]
register_simp_attr mrdt_algebra
register_simp_attr mrdt_implementation
