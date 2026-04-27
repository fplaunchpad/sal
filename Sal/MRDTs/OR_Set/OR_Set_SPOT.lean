import Sal.Interfaces.Set_Extended
import Sal.MRDTs.OR_Set.OR_Set_MRDT
import Sal.MRDTs.OR_Set.OR_Set_ReadSide

set_option linter.mathlibStandardSet false

open Classical

/-! # OR-Set (MRDT) — SPOTs

Small Proof-Oriented Tests: concrete `do`/`merge` scenarios with
expected `lookup` outcomes, machine-checked. MRDT counterpart to
`Sal/CRDTs/OR_Set/OR_Set_SPOT.lean` — same scenarios, three-way
merge against an LCA replaces the tombstone component.

Reference: Shapiro et al. INRIA RR-7506 §3.3.5; the three-way set
merge `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)` realises Add-Wins via the
`a \ l` term. -/

namespace OR_Set_MRDT_SPOT

/-- **SPOT 1 — Add makes element live.**

A single `Add 5` at ts = 1 from the empty initial state stakes the
tag `(1, 5)`, making `5` live. -/
example :
    lookup (do_ init_st (1, 0, app_op_t.Add 5)) 5 :=
  lookup_after_add init_st 5 1 0

/-- **SPOT 2 — concurrent Add wins over Rem (headline).**

LCA `init_st` is empty. Branch `a` issues `Add 5` at ts = 1; branch
`b` issues `Rem 5` at ts = 2. After the three-way merge, `(1, 5)`
sits in `a \ l` and survives, while `b`'s filter retracts nothing
(the LCA had no `(_, 5)` tag). -/
example :
    lookup
      (merge init_st
        (do_ init_st (1, 0, app_op_t.Add 5))
        (do_ init_st (2, 1, app_op_t.Rem 5)))
      5 :=
  add_wins_over_concurrent_remove init_st 5 1 2 0 1 (by decide)

/-- **SPOT 3 — sequential Add then Rem extinguishes.**

`Add 5` then `Rem 5` on a single replica leaves `5` not-live: the
`Rem` filter strips every `(_, 5)` tag, including the just-added
one. -/
example :
    ¬ lookup
        (do_ (do_ init_st (1, 0, app_op_t.Add 5)) (2, 0, app_op_t.Rem 5))
        5 :=
  add_then_remove_extinguishes init_st 5 1 2 0 0

/-- **SPOT 4 — Add-wins through a non-trivial LCA.**

LCA `l = do_ init_st (1, 0, Add 7)` already has `(1, 7)` live.
Branch `a` adds `5` at ts = 2; branch `b` removes `7` at ts = 3.
After the three-way merge, the new tag `(2, 5)` survives via
`a \ l`, and `7` is correctly removed (no `a \ l` survival because
the Add for `7` predates the LCA). -/
example :
    let l : concrete_st := do_ init_st (1, 0, app_op_t.Add 7)
    let σ : concrete_st :=
      merge l
        (do_ l (2, 0, app_op_t.Add 5))
        (do_ l (3, 1, app_op_t.Rem 7))
    lookup σ 5 ∧ ¬ lookup σ 7 := by
  refine ⟨⟨2, ?_⟩, ?_⟩
  · decide
  · rintro ⟨ts, h_mem⟩
    simp [do_, merge] at h_mem

end OR_Set_MRDT_SPOT
