import Mathlib.Tactic

/-! Shared bounded registry for finite raw list primitives. -/
declare_aesop_rule_sets [OrderedRecord]
register_simp_attr ordered_record_simps

declare_aesop_rule_sets [OrderedGeneric]
register_simp_attr ordered_generic_simps

register_simp_attr ordered_algorithm_simps

register_label_attr ordered_order
