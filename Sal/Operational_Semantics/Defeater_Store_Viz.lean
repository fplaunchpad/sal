import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Std

import Sal.Counterexample_Visualization.Trace
import Sal.Counterexample_Visualization.WriterMonad_Set

/-!
# The defeater's store operations, drawn

`Sal/Operational_Semantics/Defeater_Store_Execution.lean` proves
`defeater_obtainable`: the defeater is reachable from the initial configuration
by ten transitions of the store semantics. This file draws those ten
transitions, using the repo's own trace visualizer
(`Sal/Counterexample_Visualization/Trace.lean`).

What the diagrams show that the sibling add-wins-set drawing does not: every
node is a *version* of the store, and every edge is a *store transition* with
its rule and label — `createBranch`, `apply`, `merge` — rather than a bare
`do_`/`merge` step. The forks are visible, and each merge carries the version
that supplied its LCA slot.

## The ten operations

| # | transition | new version |
|---|---|---|
| 1 | `createBranch q p` | `v1` |
| 2 | `apply 1 p add` | `v2` = `p₁` |
| 3 | `apply 2 q add` | `v3` = `q₁` |
| 4 | `createBranch s p` | `v4` |
| 5 | `merge s q` | `v5` = `v_s` |
| 6 | `apply 3 p rem` | `v6` = `p₂` |
| 7 | `apply 4 q rem` | `v7` = `q₂` |
| 8 | `merge p s` | `v8` = `head_p` |
| 9 | `merge q s` | `v9` = `head_q` |
| 10 | `merge p q` | `v10` |

`createBranch` installs a new version with the *same state* as the head it forks
from, so its edges are state-preserving — visible in the diagrams as a repeated
box, which is the honest picture: a fork creates a version, not a value.

This is a rendering file, not a proof file: it carries no theorems. Every state
below is computed by the `do_` and `merge` retyped verbatim from
`Sal/MRDTs/Add_Wins_Set/Add_Wins_Set_MRDT.lean`, never hand-set. The expected
values to check the `#eval`s against are the kernel-checked `vp_eq`, `vq_eq`,
`sp_eq`, `sq_eq`, `LCA_eq`, `head_p_eq`, `head_q_eq`, `mergedState_eq` of
`Sal/ConditionedMRDTs/Refutations/InterLca2op_Defeater_Arbiter.lean`.

## Namespacing

`WriterMonad_Set.lean` supplies the display types (`pair_set_with_universe` and
its `ToString`) and declares `concrete_st` / `do_` / `merge` in the *root*
namespace. Everything below therefore lives in its own namespace under its own
names (`VSt`, `vdo`, `vmerge`), so importing that module is unambiguous — the
sibling `WriterMonad_Add_Wins_Set.lean` solves the same clash by retyping into
the root namespace instead.
-/

namespace Sal.Operational_Semantics.Viz

open Classical Std

/-! ## §1. The MRDT, retyped verbatim over a computable set

`Set_Extended`'s `set α = α → Bool`, so states are computable and the renderer
can print them. -/

/-- Σ = (adds, tombstones), both sets of tags. -/
abbrev VSt := set ℕ × set ℕ

/-- Initial state: both components empty. -/
def vinit : VSt := (empty, empty)

/-- Two unit-payload ops; `Rem` targets no specific element. -/
inductive VOp : Type where
  | Add
  | Rem

/-- An event: `(timestamp, replica, op)`. -/
abbrev VEv := ℕ × ℕ × VOp

/-- Effect: `Add` stakes its timestamp; `Rem` sweeps every live tag into
tombstones. -/
def vdo (s : VSt) (o : VEv) : VSt :=
  match o with
  | (ts, (_, VOp.Add)) => (add ts s.1, s.2)
  | (_,  (_, VOp.Rem)) => (s.1, union s.1 s.2)

/-- Three-way merge: per-component union; the LCA slot `l` is not read. -/
def vmerge (_l : VSt) (a : VSt) (b : VSt) : VSt :=
  (union a.1 b.1, union a.2 b.2)

/-! ## §2. Display plumbing -/

/-- The visualized state: the `(adds, tombstones)` pair over a shared universe. -/
abbrev St := pair_set_with_universe ℕ

/-- Every tag in this execution is 1 or 2 (`A_p` stakes 1, `A_q` stakes 2), and
tombstones only ever hold tags that were added, so this universe is complete.
The `Rem` timestamps 3 and 4 are not tags and never enter either component. -/
def tags : HashSet ℕ := (({} : HashSet ℕ).insert 1).insert 2

/-- Attach the display universe to a raw state. -/
def viz (s : VSt) : St := {_fst := s.1, _snd := s.2, _universe := tags}

/-- The live set `adds ∖ tombstones` — the read side, and where the defeater
does its damage. -/
def live (s : VSt) : set_with_universe ℕ :=
  {_set := difference s.1 s.2, _universe := tags}

/-! ## §3. The events -/

def A_p : VEv := (1, 0, VOp.Add)
def R_p : VEv := (3, 0, VOp.Rem)
def A_q : VEv := (2, 1, VOp.Add)
def R_q : VEv := (4, 1, VOp.Rem)

/-! ## §4. The versions, as the ten transitions build them

Replicas `p = 0`, `q = 1`, `s = 2`. Each definition is exactly what the matching
rule of Fig. `sem` installs at the new version. -/

/-- `v0` — the initial version, replica `p`'s head in `C₀`. -/
def v0 : VSt := vinit
/-- `v1` — transition 1, `createBranch q p`: `q` forks from `p`'s head `v0`.
State copied, no event. -/
def v1 : VSt := v0
/-- `v2 = p₁` — transition 2, `apply 1 p add`. -/
def v2 : VSt := vdo v0 A_p
/-- `v3 = q₁` — transition 3, `apply 2 q add`. -/
def v3 : VSt := vdo v1 A_q
/-- `v4` — transition 4, `createBranch s p`: the staging replica forks from
`p`'s head, which is now `v2`. State copied. -/
def v4 : VSt := v2
/-- `v5 = v_s` — transition 5, `merge s q`, LCA `v0`. The staging version:
both adds, no removes. -/
def v5 : VSt := vmerge v0 v4 v3
/-- `v6 = p₂` — transition 6, `apply 3 p rem`, from `p`'s own head `v2`.
`p` has *not* seen `v5`. -/
def v6 : VSt := vdo v2 R_p
/-- `v7 = q₂` — transition 7, `apply 4 q rem`, from `q`'s own head `v3`. -/
def v7 : VSt := vdo v3 R_q
/-- `v8 = head_p` — transition 8, `merge p s`, LCA `v2`. Its own tag died; the
tag it merged in from the staging version lives. -/
def v8 : VSt := vmerge v2 v6 v5
/-- `v9 = head_q` — transition 9, `merge q s`, LCA `v3`. The mirror image. -/
def v9 : VSt := vmerge v3 v7 v5
/-- `v10` — transition 10, the critical merge `merge p q`, LCA `v5`. Two heads
that each had something alive merge to a version with nothing alive. -/
def v10 : VSt := vmerge v5 v8 v9

/-! ## §5. Check the computed states against the kernel

Expected, from the refutation file's theorems: `v2 = ⟨#[1]#,#[]#⟩` (`vp_eq`),
`v3 = ⟨#[2]#,#[]#⟩` (`vq_eq`), `v5 = ⟨#[1,2]#,#[]#⟩` (`LCA_eq`),
`v6 = ⟨#[1]#,#[1]#⟩` (`sp_eq`), `v7 = ⟨#[2]#,#[2]#⟩` (`sq_eq`),
`v8 = ⟨#[1,2]#,#[1]#⟩` (`head_p_eq`), `v9 = ⟨#[1,2]#,#[2]#⟩` (`head_q_eq`),
`v10 = ⟨#[1,2]#,#[1,2]#⟩` (`mergedState_eq`). -/

#eval viz v0
#eval viz v1
#eval viz v2
#eval viz v3
#eval viz v4
#eval viz v5
#eval viz v6
#eval viz v7
#eval viz v8
#eval viz v9
#eval viz v10

-- The forks copy state: `v1` is `v0` and `v4` is `v2`, so these agree.
#eval viz v1
#eval viz v4

-- Live sets: `#[1,2]#` at the LCA, nonempty at both heads, empty after the
-- critical merge (`LCA_live`, `head_p_live`, `head_q_live`, `mergedState_live`).
#eval live v5
#eval live v8
#eval live v9
#eval live v10

/-! ## §6. Transition labels -/

def opString (o : VEv) : String :=
  match o with
  | (ts, (rid, VOp.Add)) => s!"apply {ts} r{rid} add — stakes tag {ts}"
  | (ts, (rid, VOp.Rem)) => s!"apply {ts} r{rid} rem — sweeps all live tags"

/-- An `apply` edge, labelled with its transition number and the version it
installs. -/
def applyEdge (n : Nat) (o : VEv) (v : Nat) : String :=
  s!"[{n}] {opString o}   ⟹  v{v}"

/-- A `createBranch` edge: a new version with the head's state, no event. -/
def forkEdge (n : Nat) (r' r : String) (v : Nat) : String :=
  s!"[{n}] createBranch {r'} {r} — state copied, no event   ⟹  v{v}"

/-! ## §7. Diagrams

`leaf` marks the node a branch descends from — drawn once, at the merge's apex,
and suppressed at the top of each branch. `ref` marks a version drawn elsewhere
in the execution, which is how the DAG's shared versions (`v5`, and the two
heads) appear in more than one picture. -/

def tV0 : Trace St := .leaf (viz v0)

/-- `p`'s path to the staging fork: `v0 → v2 → v4`. -/
def tSBranch : Trace St :=
  .step (.step tV0 (applyEdge 2 A_p 2) (viz v2)) (forkEdge 4 "s" "p" 4) (viz v4)

/-- `q`'s path: `v0 → v1 → v3`. -/
def tQBranch : Trace St :=
  .step (.step tV0 (forkEdge 1 "q" "p" 1) (viz v1)) (applyEdge 3 A_q 3) (viz v3)

/-- **Diagram 1 — transitions 1–5.** The staging merge `merge s q`, LCA `v0`.
Left branch is `s`'s history, right branch is `q`'s. Nothing has been removed,
so `v5` has an empty tombstone set and both tags are live. -/
def tStaging : Trace St := .mrg tV0 tSBranch tQBranch (viz v5)

/-- `p`'s remove, off its own head `v2`. -/
def tP2 : Trace St := .step (.leaf (viz v2)) (applyEdge 6 R_p 6) (viz v6)
/-- `q`'s remove, off its own head `v3`. -/
def tQ2 : Trace St := .step (.leaf (viz v3)) (applyEdge 7 R_q 7) (viz v7)

/-- **Diagram 2 — transitions 6 and 8.** `merge p s`, LCA `v2`. Left: `p`
removes, killing its own tag. Right: the staging version arrives. The result's
tombstone set is `{1}` but its add set is `{1,2}`, so tag 2 survives — `v8` is
live on a tag it never added. -/
def tHeadP : Trace St :=
  .mrg (.leaf (viz v2)) tP2 (.ref "v5  (staging version, LCA slot of [5])" (viz v5))
    (viz v8)

/-- **Diagram 3 — transitions 7 and 9.** `merge q s`, LCA `v3`. The mirror
image: live on tag 1. -/
def tHeadQ : Trace St :=
  .mrg (.leaf (viz v3)) tQ2 (.ref "v5  (staging version)" (viz v5)) (viz v9)

/-- **Diagram 4 — transition 10, the critical merge.** `merge p q`, and the
`Merge` rule's LCA premise resolves to `v5` (`lca_critical`). Both heads have
something alive; the result has nothing alive. -/
def tCritical : Trace St :=
  .mrg (.ref "v5  = LCA(v8, v9),  live #[1,2]#" (viz v5))
       (.ref "v8 = head_p  — live #[2]#" (viz v8))
       (.ref "v9 = head_q  — live #[1]#" (viz v9))
       (viz v10)

/-- **Diagram 5 — all ten transitions in one picture.** The staging merge at the
apex, each head's merge nested inside its branch, the critical merge at the
bottom. -/
def tAll : Trace St :=
  .mrg tStaging
       (.mrg (.ref "v2" (viz v2)) tP2 (.ref "v5" (viz v5)) (viz v8))
       (.mrg (.ref "v3" (viz v3)) tQ2 (.ref "v5" (viz v5)) (viz v9))
       (viz v10)

#html renderTrace tStaging
#html renderTrace tHeadP
#html renderTrace tHeadQ
#html renderTrace tCritical
#html renderTrace tAll

end Sal.Operational_Semantics.Viz
