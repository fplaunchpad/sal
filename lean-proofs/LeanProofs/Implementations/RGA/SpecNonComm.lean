import LeanProofs1.Implementations.RGA.VCs

/-!
# RGA cannot satisfy SPEC-NON-COMM

The reason `Obligations` is `Spec`-free, recorded as a theorem.

SPEC-NON-COMM says an implementation commutation never erases a
specification conflict:

```
  not (o1 <->_Spec o2)  ->  not (e1 <-> e2)
```

RGA proves `all_commute`, so the conclusion is never satisfiable. The law
therefore collapses to the demand that **every** pair of specification
updates commute. RGA's `Spec` is the strict identified machine, where two
root insertions do not: taking them in one order reads `[2, 1]`, in the
other `[1, 2]`.

So this is not a row that merely leaves the fourth law unproved. The law is
false here, which is why RGA reaches Definition 4 through
`Soundness.certifiedRA_scoped`, and why SPEC-NON-COMM cannot be a field of
`Obligations`: four other rows of the paper are in the same position, since
each proves `all_commute` against an ordered specification.
-/

namespace LeanProofs1.Implementations.RGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- Two root insertions do not commute in `Spec`: the order decides which
ends up first in the list. -/
theorem spec_not_commutes :
    ¬ historySpec.Commutes (AppOp.addAfter 1 0) (AppOp.addAfter 2 0) := by
  intro hc
  have hyes : historySpec.admits
      ([] ++ [SeqLabel.update (AppOp.addAfter 1 0),
              SeqLabel.update (AppOp.addAfter 2 0)]
        ++ [SeqLabel.query () [2, 1]]) := by
    refine ⟨([2, 1], {1, 2}), ?_⟩
    refine Runs.cons (m := ([1], {1})) ⟨by norm_num, by decide, Or.inl rfl, rfl⟩
      (Runs.cons (m := ([2, 1], {1, 2}))
        ⟨by norm_num, by decide, Or.inl rfl, by decide⟩
        (Runs.cons ⟨rfl, rfl⟩ (Runs.nil _)))
  obtain ⟨final, run⟩ := (hc [] [SeqLabel.query () [2, 1]]).mp hyes
  cases run with
  | cons h1 r1 => cases r1 with
    | cons h2 r2 => cases r2 with
      | cons h3 _ =>
          obtain ⟨-, -, -, e1⟩ := h1
          subst e1
          obtain ⟨-, -, -, e2⟩ := h2
          subst e2
          exact absurd h3.2 (by decide)

/-- **SPEC-NON-COMM is false for this row.** Every pair of its events
commutes, so the law would force every pair of specification updates to
commute too, and `spec_not_commutes` says they do not. -/
theorem no_spec_non_comm : ¬ Interface.spec_non_comm D historySpec := fun h =>
  h (1, 0, AppOp.addAfter 1 0) (2, 1, AppOp.addAfter 2 0)
    spec_not_commutes (all_commute _ _)

end LeanProofs1.Implementations.RGA
