import LeanProofs1.Implementations.MVRegister.Definition
import LeanProofs1.Interface.Laws

/-!
# No `rc` satisfies `Laws(D_type)` for the multi-value register

RC-NON-COMM relates a fact about **events** to a fact about **operations**:

```
  time(e1) /= time(e2) -> rep(e1) /= rep(e2) ->
    ( not (e1 <-> e2)  and  o1 /= o2 )  <->  o1 --rc--> o2  or  o2 --rc--> o1
```

The right-hand side reads the labels alone. So if two pairs of events carry
the **same** two labels, are both concurrent in the law's sense, and one pair
commutes while the other does not, then no `rc` can satisfy the law. The MVR
has such pairs, because a write's tag is its timestamp and `do` drops the
tags a write names. Whether `write 2 [5]` disturbs `write 1 []` depends on
whether the first write happened to be stamped `5`.

```
  pair A   e1 = (5, 0, write 1 [])    e2 = (6, 1, write 2 [5])   do not commute
  pair B   e1 = (7, 0, write 1 [])    e2 = (8, 1, write 2 [5])   commute
```

Both pairs carry the labels `write 1 []` and `write 2 [5]`, both have
distinct timestamps and distinct replicas, and the labels differ, so the
law's own exemptions do not apply to either. In pair A the second write
supersedes the first; in pair B it names a tag that nobody holds.

This is the root obstruction, and it is prior to NO-RC-CHAIN. Even if the
operation carried its own tag, so that an `rc` could be written down at all,
three writes in sequence, each superseding the one before, would give
`rc o1 o2` and `rc o2 o3` and break NO-RC-CHAIN.
-/

namespace LeanProofs1.Implementations.MVRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

variable (rc : AppOp → AppOp → OrderResult)

/-! ## The two pairs -/

/-- The plain write, carried by both pairs. -/
def oA : AppOp := .write 1 []
/-- The superseding write, carried by both pairs. It names tag `5`. -/
def oB : AppOp := .write 2 [5]

/-- Pair A: the first write is stamped `5`, which is the tag `oB` names.
The events do not mention `rc`, and neither does `do`. -/
def a1 : Op AppOp := (5, 0, oA)
def a2 : Op AppOp := (6, 1, oB)
/-- Pair B: the first write is stamped `7`, which `oB` does not name. -/
def b1 : Op AppOp := (7, 0, oA)
def b2 : Op AppOp := (8, 1, oB)

/-! ## Pair A does not commute -/

/-- At the empty state the two orders differ: performed first, the write
stamped `5` is dropped by the write that names tag `5`; performed second it
survives. -/
theorem step_A_ne : step (step (∅ : St) a1) a2 ≠ step (step (∅ : St) a2) a1 := by decide

theorem not_commutes_A : ¬ (D rc).Commutes a1 a2 :=
  fun hc => step_A_ne (hc (∅ : St))

/-! ## Pair B commutes -/

theorem commutes_B : (D rc).Commutes b1 b2 := by
  intro s
  show step (step s b1) b2 = step (step s b2) b1
  have hfilt : ∀ t : St, t.filter (fun p => p.1 ∉ overwrites oA) = t := by
    intro t; simp [overwrites, oA]
  show insert ((8 : Nat), 2)
      ((insert ((7 : Nat), 1) (s.filter (fun p => p.1 ∉ overwrites oA))).filter
        (fun p => p.1 ∉ overwrites oB))
    = insert ((7 : Nat), 1)
      ((insert ((8 : Nat), 2) (s.filter (fun p => p.1 ∉ overwrites oB))).filter
        (fun p => p.1 ∉ overwrites oA))
  rw [hfilt s, hfilt (insert ((8 : Nat), 2) (s.filter (fun p => p.1 ∉ overwrites oB)))]
  rw [Finset.filter_insert, if_pos (by simp [overwrites, oB])]
  exact Finset.insert_comm _ _ _

/-! ## The result -/

/-- **No `rc` makes the multi-value register satisfy `Laws(D_type)`.** The
two pairs carry one pair of labels between them, so RC-NON-COMM would have
to give them the same answer, and they do not commute alike. -/
theorem times_A : (D rc).time a1 ≠ (D rc).time a2 := by
  show (5 : Nat) ≠ 6; decide

theorem reps_A : (D rc).rep a1 ≠ (D rc).rep a2 := by
  show (0 : Nat) ≠ 1; decide

theorem times_B : (D rc).time b1 ≠ (D rc).time b2 := by
  show (7 : Nat) ≠ 8; decide

theorem reps_B : (D rc).rep b1 ≠ (D rc).rep b2 := by
  show (0 : Nat) ≠ 1; decide

theorem ops_ne : a1.op ≠ a2.op := by
  show oA ≠ oB
  decide

theorem no_rc_satisfies_laws : ¬ Laws (D rc) := by
  intro h
  have hA := h.rc_non_comm a1 a2 (times_A rc) (reps_A rc)
  have hB := h.rc_non_comm b1 b2 (times_B rc) (reps_B rc)
  have hedge := hA.mp ⟨not_commutes_A rc, ops_ne⟩
  exact (hB.mpr hedge).1 (commutes_B rc)

/-- So the row has no obligation bundle, whatever `rc` it is given. -/
theorem no_obligations : ¬ Obligations (D rc) := fun h => no_rc_satisfies_laws rc h.laws

end LeanProofs1.Implementations.MVRegister
