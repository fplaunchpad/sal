import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import ProofWidgets


import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Std

import Sal.Counterexample_Visualization.WriterMonad_Set


open Classical Std

/-!
# The Add-Wins Set defeater, drawn

The *defeater* is a fully LCA-legal add-wins-set execution whose critical merge
cannot be linearized by peeling a `Rem` last. It is proved in
`Sal/ConditionedMRDTs/Refutations/InterLca2op_Defeater_Arbiter.lean` and walked
through in `Sal/ConditionedMRDTs/defeater-walkthrough.pdf`; this file renders it.

Three replicas. `p` and `q` each add a tag; a staging replica `s` merges the two
adds into `v_s`; `p` and `q` then each issue a `Rem` *without* having seen `v_s`,
and afterwards each merges `v_s` in. That leaves two heads

  head_p = ⟨{1,2}, {1}⟩   live {2}      head_q = ⟨{1,2}, {2}⟩   live {1}

whose unique LCA is `v_s`, with `L(v_s) = {1,2} = L(head_p) ∩ L(head_q)` — so the
merge is LCA-legal. Merging them kills everything: `v_⊤ = ⟨{1,2},{1,2}⟩`, live `∅`.

The obstruction the picture shows: AWSet's `Rem` sweeps *all* live tags into the
tombstone set, so any state in the image of `Rem` has an empty live set. Both heads
have a **nonempty** live set, so neither is `do_ s Rem` for any `s` — no bottom-up
interchange rule can peel a `Rem` off either side of the critical merge
(`no_rem_peelable_from_defeater_heads`, `no_inter_lca_2op_rem_peel_of_defeater`).

The last two diagrams show the second crack: `w = [A_p,R_p,A_q,R_q]` is a valid
linearization of the merged version, but restricted to head_q's own event set,
`[A_p,A_q,R_q]`, it folds to the *wrong* state — not `head_q` (`crack1_witness`).

This is a rendering file, not a proof file: it carries no theorems. Every state
below is computed by the `do_` and `merge` copied verbatim from
`Sal/MRDTs/Add_Wins_Set/Add_Wins_Set_MRDT.lean`, never hand-set. The expected
values to check the `#eval`s against are the kernel-checked `sp_eq`, `LCA_eq`,
`head_p_eq`, `head_q_eq`, `mergedState_eq` of the refutation file.
-/


/-! ## The MRDT, verbatim from `Sal/MRDTs/Add_Wins_Set/Add_Wins_Set_MRDT.lean`

Retyped rather than imported, as the sibling `WriterMonad_*` clients do: that
module declares `concrete_st` / `do_` / `merge` in the root namespace, as does
this one, so importing it would make every one of those names ambiguous. -/

/-- Σ = (adds, tombstones), both sets of tags. -/
abbrev concrete_st := set ℕ × set ℕ

/-- Initial state: both components empty. -/
@[simp]
def init_st: concrete_st := (empty, empty)

/-- Two unit-payload ops: `Rem` targets no specific element. -/
inductive app_op_t : Type where
| Add
| Rem

abbrev op_t:= ℕ × ℕ × app_op_t

/-- Effect:
  * `Add` at `ts`: stake `ts` into `adds`.
  * `Rem`: sweep every currently-live `adds` tag into `tombstones`. -/
@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (ts, (_, app_op_t.Add)) => (add ts s.1, s.2)
| (_, (_, app_op_t.Rem)) => (s.1, union s.1 s.2)

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

/-- `rc` orders every `Add`/`Rem` pair so `Rem` always precedes `Add`
in the reconciled order, whichever argument position it's in. Every
other pair is `Either`. -/
@[simp, grind]
def rc (o1 o2: op_t) :=
match (Prod.snd (Prod.snd o1)), (Prod.snd (Prod.snd o2)) with
| app_op_t.Add, app_op_t.Rem => rc_res.Snd_then_fst
| app_op_t.Rem, app_op_t.Add => rc_res.Fst_then_snd
| _, _ => rc_res.Either

/-- Three-way merge: plain per-component union; `l` unused. -/
@[simp, grind]
def merge (_l: concrete_st) (a: concrete_st) (b: concrete_st) : concrete_st :=
  (union a.1 b.1, union a.2 b.2)


/-! ## Display plumbing -/

/-- The visualized state: the `(adds, tombstones)` pair over a shared universe. -/
abbrev St := pair_set_with_universe ℕ

/-- Every tag in this execution is 1 or 2 (`A_p` stakes 1, `A_q` stakes 2), and
tombstones only ever hold tags that were added, so this universe is complete: no
member of any displayed component falls outside it. The `Rem` timestamps 3 and 4
are not tags and never enter either component. -/
def tags : HashSet ℕ := (({} : HashSet ℕ).insert 1).insert 2

/-- Attach the display universe to a raw MRDT state. -/
def viz (s : concrete_st) : St :=
  {_fst := s.1, _snd := s.2, _universe := tags}

/-- The live set `adds ∖ tombstones` — this MRDT's read side, and where the
defeater does its damage. Shown as its own node so it can be read off directly. -/
def live (s : concrete_st) : set_with_universe ℕ :=
  {_set := difference s.1 s.2, _universe := tags}

def op_string (o : op_t) : String :=
match o with
| (ts, (rid, app_op_t.Add)) => s! "Add — stakes tag {ts}  (replica {rid})"
| (ts, (rid, app_op_t.Rem)) => s! "Rem @{ts} — sweeps all live tags  (replica {rid})"


/-! ## The defeater's events

Transcribed from `InterLca2op_Defeater_Arbiter.lean`: `A_p = add@1` and
`R_p = rem@3` on replica 0, `A_q = add@2` and `R_q = rem@4` on replica 1. -/

def A_p : op_t := (1, 0, app_op_t.Add)
def R_p : op_t := (3, 0, app_op_t.Rem)
def A_q : op_t := (2, 1, app_op_t.Add)
def R_q : op_t := (4, 1, app_op_t.Rem)


/-! ## The versions, as folds of `do_` and `merge` -/

/-- `p1` — replica p after its own add. Expect `⟨#[1]#, #[]#⟩` (`vp_eq`). -/
def p1 : concrete_st := do_ init_st A_p
/-- `q1` — replica q after its own add. Expect `⟨#[2]#, #[]#⟩` (`vq_eq`). -/
def q1 : concrete_st := do_ init_st A_q

/-- `v_s` — the staging replica merges the two adds. This is the honest LCA of
the critical merge. Expect `⟨#[1,2]#, #[]#⟩`, live `#[1,2]#` (`LCA_eq`, `LCA_live`). -/
def v_s : concrete_st := merge init_st p1 q1

/-- `p2` — replica p removes, having seen only its own add. Expect
`⟨#[1]#, #[1]#⟩` (`sp_eq`). -/
def p2 : concrete_st := do_ p1 R_p
/-- `q2` — replica q removes, having seen only its own add. Expect
`⟨#[2]#, #[2]#⟩` (`sq_eq`). -/
def q2 : concrete_st := do_ q1 R_q

/-- `head_p = merge(p2, v_s)` over their LCA `p1`. Expect `⟨#[1,2]#, #[1]#⟩`,
live `#[2]#` (`head_p_eq`, `head_p_live`). Its own tag died; the tag it merged
in from the staging version is alive. -/
def head_p : concrete_st := merge p1 p2 v_s
/-- `head_q = merge(q2, v_s)` over their LCA `q1`. Expect `⟨#[1,2]#, #[2]#⟩`,
live `#[1]#` (`head_q_eq`, `head_q_live`). -/
def head_q : concrete_st := merge q1 q2 v_s

/-- The critical merge, LCA `v_s`. Expect `⟨#[1,2]#, #[1,2]#⟩`, live `#[]#`
(`mergedState_eq`, `mergedState_live`). Two heads that each had something alive
merge to a version with nothing alive. -/
def v_top : concrete_st := merge v_s head_p head_q


-- Check these against the expectations in the doc comments above, which come from
-- the refutation file's kernel-checked theorems.
#eval viz p1
#eval viz q1
#eval viz v_s
#eval viz p2
#eval viz q2
#eval viz head_p
#eval viz head_q
#eval viz v_top

-- The live sets: {1,2} at the LCA, nonempty at both heads, empty after the merge.
#eval live v_s
#eval live head_p
#eval live head_q
#eval live v_top

-- The obstruction, at the two states that matter: `Rem`'s output is always
-- all-dead, so a state with anything live is not in the image of `Rem`.
-- Both of these are empty, while the heads' live sets just above are not.
#eval live (do_ head_p R_p)
#eval live (do_ head_q R_q)


/-! ## Diagrams

`leaf` marks the node a branch descends from — it is drawn once, at the merge's
apex, and suppressed at the top of each branch. `ref` marks a version that lives
elsewhere in the execution and gets its own captioned box. -/

def tInit : Trace St := .leaf (viz init_st)
def tP1 : Trace St := .step tInit (op_string A_p) (viz p1)
def tQ1 : Trace St := .step tInit (op_string A_q) (viz q1)

/-- **Diagram 1 — the staging merge.** `p` and `q` each add; replica `s` merges
both into `v_s`. Nothing is removed yet, so `v_s` has an empty tombstone set and
both tags are live. -/
def tStaging : Trace St := .mrg tInit tP1 tQ1 (viz v_s)

def tP2 : Trace St := .step (.leaf (viz p1)) (op_string R_p) (viz p2)
def tQ2 : Trace St := .step (.leaf (viz q1)) (op_string R_q) (viz q2)

/-- **Diagram 2 — `head_p`.** LCA `p1`. Left: `p` removes, killing its own tag.
Right: the staging version arrives. The merge's tombstone set is `{1}` but its
add set is `{1,2}`, so tag 2 survives — `head_p` is live on a tag it never added. -/
def tHeadP : Trace St :=
  .mrg (.leaf (viz p1)) tP2 (.ref "v_s  (staging version)" (viz v_s)) (viz head_p)

/-- **Diagram 3 — `head_q`.** The mirror image: live on tag 1. -/
def tHeadQ : Trace St :=
  .mrg (.leaf (viz q1)) tQ2 (.ref "v_s  (staging version)" (viz v_s)) (viz head_q)

/-- **Diagram 4 — the critical merge.** The LCA is `v_s`, and
`L(v_s) = {1,2} = L(head_p) ∩ L(head_q)`, so this merge is LCA-legal. Both heads
have something alive; the result has nothing alive. Neither head is in the image
of `Rem`, so no bottom-up rule can peel a `Rem` off either side. -/
def tCritical : Trace St :=
  .mrg (.ref "v_s  = LCA(head_p, head_q),  live #[1,2]#" (viz v_s))
       (.ref "head_p  — live #[2]#" (viz head_p))
       (.ref "head_q  — live #[1]#" (viz head_q))
       (viz v_top)

/-- **Diagram 5 — the whole execution in one picture.** The staging merge at the
apex, each head's merge nested inside its branch, the critical merge at the
bottom — four merges in one diagram. -/
def tDefeater : Trace St :=
  .mrg tStaging
       (.mrg (.ref "p1" (viz p1)) tP2 (.ref "v_s" (viz v_s)) (viz head_p))
       (.mrg (.ref "q1" (viz q1)) tQ2 (.ref "v_s" (viz v_s)) (viz head_q))
       (viz v_top)

#html renderTrace tStaging
#html renderTrace tHeadP
#html renderTrace tHeadQ
#html renderTrace tCritical
#html renderTrace tDefeater


/-! ## The second crack: a valid witness that does not restrict correctly

`w = [A_p, R_p, A_q, R_q]` folds to the merged version, so it is a valid
linearization of it. But `head_q`'s own event set is `{A_p, A_q, R_q}` (it merged
in `v_s`, which carries `A_p`; `R_p` is not one of its events), and `w` restricted
to those events folds to `⟨#[1,2]#, #[1,2]#⟩` — not `head_q = ⟨#[1,2]#, #[2]#⟩`.
A valid merged witness that is not assembled from state-correct side witnesses
(`crack1_witness`). These are plain `do_` chains, no merge. -/

def foldOps (s : concrete_st) : List op_t → concrete_st :=
  List.foldl do_ s

def traceOps (t : Trace St) : List op_t → Trace St :=
  List.foldl (fun acc o =>
    let s : concrete_st := (acc.result._fst, acc.result._snd)
    .step acc (op_string o) (viz (do_ s o))) t

/-- `w`, the merged version's linearization. Folds to `v_top`. -/
def w : List op_t := [A_p, R_p, A_q, R_q]

/-- `w` restricted to head_q's event set `{A_p, A_q, R_q}`. -/
def wRestrQ : List op_t := [A_p, A_q, R_q]

-- Expect the first to equal `viz v_top` above, and the second to *differ* from
-- `viz head_q` above.
#eval viz (foldOps init_st w)
#eval viz (foldOps init_st wRestrQ)

/-- **Diagram 6 — `w` folds to the merged version.** ✓ -/
def tW : Trace St := traceOps (.leaf (viz init_st)) w

/-- **Diagram 7 — `w` restricted to head_q's events folds to the wrong state.**
Compare its last node against `head_q = ⟨#[1,2]#, #[2]#⟩`: the restriction has
tag 1 dead, `head_q` has it live. ✗ -/
def tWRestrQ : Trace St := traceOps (.leaf (viz init_st)) wRestrQ

#html renderTrace tW
#html renderTrace tWRestrQ
