import Sal.MRDTs.Framework.GuardedStateProjection
import Mathlib.Tactic

/-! Goal-directed local law selection. Definitions and preservation lemmas are
explicit inputs and remain part of the datatype's measured description. No
datatype namespace or completed simulation certificate is selected implicitly. -/
macro "guarded_projection_step" "[" defs:Lean.Parser.Tactic.simpLemma,* "]"
    " using " "[" laws:ident,* "]" : tactic => do
  let search ← laws.getElems.mapM fun law => `(Lean.Parser.Tactic.SolveByElim.arg| $law:ident)
  `(tactic| (
    intros
    try dsimp only [$defs,*] at *
    try subst_vars
    all_goals first
    | solve_by_elim (config := {maxDepth := 8}) [$search,*]
    | simp_all only [List.toFinset_append, List.toFinset_cons,
        List.toFinset_nil, Finset.union_singleton, Finset.union_empty, Finset.insert_empty]))
