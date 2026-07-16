import Sal.Interfaces.Map_Extended
import Sal.Interfaces.Set_Extended

open Classical

/-!
# A prefix-free, tombstone-free RGA — complete implementation (runs; not VC-verifiable)

This is the concrete data type behind the impossibility result in
`RGA_PrefixFree_Impossible.lean`. It is a *complete* MRDT — state `σ₀`, `do_`,
3-way `merge`, `rc` — that is genuinely **prefix-free** (operations carry only an
immediate anchor / target, no ancestor path) and **tombstone-free** (`Del`
physically removes the id; no graveyard).

The point of having it as runnable code:

* **(a) The 3-way `merge` converges concurrent insert-vs-delete.** The merge reads
  parents from the lowest-common-ancestor state `l`, so when one branch inserts
  after a node the other branch deleted, the LCA still has that node live with its
  parent, and `climb` recovers it. `merge_converges_concurrent` checks this: the
  inserted node is rehomed to the deleted node's parent, order-independently.
  The merge is *identical* to the path-carrying flagship's — it never needed paths.

* **(b) The single-replica `do_` VC fails.** There is no LCA at `do_`. Reordering
  the same insert/delete on one replica diverges (`single_replica_do_diverges`),
  and that is exactly a `cond_comm_base` violation (`cond_comm_base_fails`).

So the information the VC needs (the deleted anchor's parent) lives in the LCA, but
the single-replica `do_`-commutation VC never looks there. That gap — *merge can
converge, the VC cannot see it* — is why a prefix-free tombstone-free RGA runs and
yet cannot be certified by Sal's current VCs. Cf. `RGA_PrefixFree_Impossible.lean`
(the `rc = Either` horn) and `RGA_Splice_Counterexample.lean` (the `cond_comm_base`
horn). This file supplies the missing `merge` and exhibits the convergence the
impossibility analysis predicted.
-/

/-! ## State -/

abbrev concrete_st := map ℕ (ℕ × ℕ)

@[simp] def el  (s : concrete_st) (t : ℕ) : ℕ := (sel s t).1
@[simp] def anc (s : concrete_st) (t : ℕ) : ℕ := (sel s t).2
@[simp] def init_st : concrete_st := const_on empty (0, 0)

/-! ## Operations (prefix-free) -/

/-- `Ins e a` (element, immediate anchor) and `Del x` (target). No path. -/
inductive app_op_t : Type where
| Ins : ℕ → ℕ → app_op_t       -- element, anchor
| Del : ℕ → app_op_t           -- target
deriving DecidableEq

abbrev op_t := ℕ × ℕ × app_op_t

/-- Effect.
* `Ins e a` at ts `t`: store `(e, a)` if `a` is live, else fall to root `0` — with
  no path there is nothing to climb (this is the prefix-free choice that the
  impossibility theorem shows cannot commute).
* `Del x`: reparent `x`'s children to its stored parent `anc s x`, then remove `x`. -/
@[simp] def do_ (s : concrete_st) (o : op_t) : concrete_st :=
  match o with
  | (t, _, .Ins e a) => upd s t (e, if contains s a then a else 0)
  | (_, _, .Del x)   =>
      del (iter_upd (fun _ ea => if ea.2 = x then (ea.1, anc s x) else ea) s) x

/-! ## Merge (identical to the flagship; LCA-driven, path-free) -/

/-- climb worker: walk `ancL` to the root or a survivor. -/
def climb_aux (ancL : ℕ → ℕ) (I : set ℕ) : ℕ → ℕ → ℕ
  | 0,        x => x
  | (fuel+1), x => if x = 0 || I x then x else climb_aux ancL I fuel (ancL x)

@[simp] def climb (ancL : ℕ → ℕ) (I : set ℕ) (x : ℕ) : ℕ := climb_aux ancL I x x

/-- Three-way merge: OR-set survival on identities, then `climb` each survivor's
birth-anchor up the **LCA** `l`'s parent chain. Reads parents from `l` only —
needs no operation paths, and recovers a concurrently-deleted node's parent. -/
@[simp] def merge (l a b : concrete_st) : concrete_st :=
  let dl := domain l
  let da := domain a
  let db := domain b
  let I : set ℕ := union (intersection (intersection dl da) db)
                         (union (difference da dl) (difference db dl))
  let ancL : ℕ → ℕ := fun y => anc l y
  let elf : ℕ → ℕ := fun t =>
    if contains l t then el l t else if contains a t then el a t else el b t
  let betaf : ℕ → ℕ := fun t =>
    if contains l t then anc l t else if contains a t then anc a t else anc b t
  map.mk (fun t => (elf t, climb ancL I (betaf t))) I

/-! ## Conflict resolution -/

inductive rc_res : Type where
| Fst_then_snd | Snd_then_fst | Either
deriving DecidableEq

/-- Order the only non-commuting pair — insert-at-`x` vs delete-`x` — and leave
everything else `Either`. (Prefix-free forces an ordering here; with `rc = Either`
the pair would have to commute, which `RGA_PrefixFree_Impossible.lean` refutes.) -/
@[simp] def rc (o1 o2 : op_t) : rc_res :=
  match o1, o2 with
  | (_,_,.Ins _ a1), (_,_,.Del x2) => if a1 = x2 then rc_res.Fst_then_snd else rc_res.Either
  | (_,_,.Del x1), (_,_,.Ins _ a2) => if a2 = x1 then rc_res.Snd_then_fst else rc_res.Either
  | _, _ => rc_res.Either

@[simp] def eq (a b : concrete_st) : Prop :=
  ∀ k, (contains a k = contains b k) ∧ (contains a k → sel a k = sel b k)

/-! ## Operational oracle -/

def mk (recs : List (ℕ × ℕ × ℕ)) : concrete_st :=
  recs.foldl (fun s r => upd s r.1 (r.2.1, r.2.2)) init_st

def dump (s : concrete_st) (ids : List ℕ) : List (ℕ × ℕ × ℕ) :=
  ids.filterMap (fun t => if contains s t then some (t, el s t, anc s t) else none)

/-! ## (a) The 3-way merge CONVERGES concurrent insert-vs-delete

LCA `l`: node `5` lives under `7` under the root. Branch `a` inserts `10` after
`5`; concurrently branch `b` deletes `5`. The merge recovers `5`'s parent `7` from
the LCA and rehomes `10` to `7` — order-independently. The insert anchored at a
node the other branch deleted, and convergence still happened: **no path needed.**

Caveat: the `merge` (copied verbatim from the flagship) uses `climb` with fuel =
node id, so this convergence relies on **id-monotone anchors** (`anc t < t`); it
holds here because the ids are monotone and the chains short. Non-monotone ids can
break `wf` under merge — see `RGA_Reachability_Invariant.lean` (`merge_breaks_wf`).
So `merge_converges_concurrent` is a verified fact about *this example*, not a
general convergence theorem. -/

def l_st : concrete_st := mk [(7,70,0),(5,83,7)]
def br_a : concrete_st := do_ l_st (10, 1, .Ins 65 5)   -- insert 10 after 5
def br_b : concrete_st := do_ l_st (11, 2, .Del 5)       -- delete 5

#eval dump (merge l_st br_a br_b) [5,7,10]   -- [(7,70,0),(10,65,7)]
#eval dump (merge l_st br_b br_a) [5,7,10]   -- same (order-independent)

theorem merge_converges_concurrent :
    dump (merge l_st br_a br_b) [5,7,10] = dump (merge l_st br_b br_a) [5,7,10]
      ∧ dump (merge l_st br_a br_b) [5,7,10] = [(7,70,0),(10,65,7)] := by
  native_decide

/-! ## (b) The single-replica `do_` VC FAILS

No LCA at `do_`. Reordering the same insert/delete on one replica diverges: `10`
lands under `7` one way, under the root `0` the other. -/

def s_seq : concrete_st := mk [(7,70,0),(5,83,7)]
def ins5  : op_t := (10, 1, .Ins 65 5)
def del5  : op_t := (11, 2, .Del 5)
def ins5' : op_t := (12, 3, .Ins 90 5)

#eval dump (do_ (do_ s_seq ins5) del5) [5,7,10]   -- [(7,70,0),(10,65,7)]
#eval dump (do_ (do_ s_seq del5) ins5) [5,7,10]   -- [(7,70,0),(10,65,0)]

theorem single_replica_do_diverges :
    dump (do_ (do_ s_seq ins5) del5) [5,7,10] ≠ dump (do_ (do_ s_seq del5) ins5) [5,7,10] := by
  native_decide

/-- And it is exactly a `cond_comm_base` violation: `rc ins5 del5 = Fst_then_snd`,
`rc del5 ins5' ≠ Either`, yet the swap (under the trailing ordered `ins5'`)
diverges at node `10`. The merge could fix this; the merge-free VC cannot. -/
theorem cond_comm_base_fails :
    rc ins5 del5 = rc_res.Fst_then_snd ∧ rc del5 ins5' ≠ rc_res.Either
      ∧ dump (do_ (do_ (do_ s_seq ins5) del5) ins5') [5,7,10,12]
          ≠ dump (do_ (do_ (do_ s_seq del5) ins5) ins5') [5,7,10,12] := by
  native_decide
