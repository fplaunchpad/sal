import Mathlib.Tactic

/-! Representation reasoning over extensional carriers. The caller supplies
raw definitions; the solver uses only generic equality, membership, Boolean
and integer rules. Constructor and conditional branches are exposed by `split`.
No completed datatype law or verification condition is registered here. -/
macro "mrdt_representation" "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    intros
    try simp only [$defs,*]
    all_goals try ext
    all_goals repeat' (split <;> simp only [$defs,*])
    all_goals try ext
    all_goals try simp only [$defs,*, Set.mem_union, Set.mem_inter_iff, Set.mem_diff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false,
      Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, Finset.mem_filter,
      List.mem_cons, List.mem_append, List.mem_filter, List.mem_map,
      decide_eq_true_eq, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm,
      Bool.false_or, Bool.or_false, Bool.or_self]
    all_goals first | omega | grind))
