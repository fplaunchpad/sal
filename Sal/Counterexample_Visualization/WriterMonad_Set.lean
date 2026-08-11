import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

import Std.Tactic.BVDecide
import Sal.Interfaces.Set_Extended
import Std

import Sal.Counterexample_Visualization.Trace



open Classical Std


structure set_with_universe (α: Type) [ToString α] [DecidableEq α] [Hashable α] where
_set : set α
_universe : HashSet α

/-- Display an abstract `set` (an `α → Bool` predicate, possibly infinite) concretely,
by filtering a universe of candidate elements down to the members. Shared by the
single-set and the product-of-sets displays. -/
def showSet {α : Type} [ToString α] [DecidableEq α] [Hashable α]
(univ : HashSet α) (s : set α) : String :=
  let members := univ.fold (fun acc elem => if mem elem s then (toString elem)::acc else acc) []
  -- `HashSet.fold` runs in hash order, so sort the rendered members: a state's
  -- display should not depend on which elements happen to share a bucket.
  -- Shorter-first, then lexicographic, so numeric elements come out in numeric
  -- order (`7,8,9,10`, not the plain-lexicographic `10,7,8,9`).
  let members := (members.toArray.qsort
    (fun x y => x.length < y.length || (x.length == y.length && x < y))).toList
  let rec str_process_fun (l : List String) :=  (match l with
  | [] => ""
  | [x] => x
  | x::xs => x ++ "," ++ (str_process_fun xs))
  s! "#[{str_process_fun members}]#"

instance {α} [ToString α] [DecidableEq α] [Hashable α] : ToString (set_with_universe α) where
  toString a := showSet a._universe a._set


abbrev concrete_st_viz (α : Type) [ToString α] [DecidableEq α] [Hashable α] := set_with_universe α


@[simp]
def init_st_viz {α: Type} [ToString α] [DecidableEq α] [Hashable α] (init_st : set α): concrete_st_viz α := {_set := init_st, _universe:={}}


/-! ## Product-of-two-sets states

MRDTs whose Σ is a *pair* of sets rather than a single set (the add-wins set's
`(adds, tombstones)`, the OR-set CRDT's `(adds, tombstones)`, the MVR's
`(writes, removed)`) do not fit `set_with_universe`. They get the same
universe-tracking treatment over a shared universe, and display as `⟨#[…]#, #[…]#⟩`.
-/

structure pair_set_with_universe (α : Type) [ToString α] [DecidableEq α] [Hashable α] where
_fst : set α
_snd : set α
_universe : HashSet α

instance {α} [ToString α] [DecidableEq α] [Hashable α] : ToString (pair_set_with_universe α) where
  toString a := s!"⟨{showSet a._universe a._fst}, {showSet a._universe a._snd}⟩"

@[simp]
def init_pair_viz {α : Type} [ToString α] [DecidableEq α] [Hashable α]
(init_st : set α × set α) : pair_set_with_universe α :=
{_fst := init_st.1, _snd := init_st.2, _universe := {}}




structure WithLog (logged : Type) (α : Type) [ToString α] [ToString logged] where
  log : List logged
  val : α

instance {α logged} [ToString α] [ToString logged] : ToString (WithLog logged α) where
  toString x := "{" ++ s!"log := {toString x.log}, val := {toString x.val}" ++ "}"


def andThen {α β γ} [ToString α] [ToString β] [ToString γ] (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}


def ok {α}  [ToString α] [DecidableEq α] [Hashable α]  (x : concrete_st_viz α) : WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α) := {log := [], val := x}

def save {α} [ToString α] (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => andThen

def do_viz {β : Type} {α: Type} [ToString α] [DecidableEq α] [Hashable α] (do_: set α → (ℕ × ℕ × β) → set α)
(ls:  WithLog (concrete_st_viz α × String × concrete_st_viz α)
(concrete_st_viz α)) (o: ℕ × ℕ ×  β) (univ_add : (ℕ × ℕ × β) → α) (op_string : (ℕ × ℕ × β) → String)
: WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α)
:=
let s := ls.val
let _set := s._set
let _universe := s._universe
let final_set := do_ _set o
let final_universe := _universe.insert (univ_add o)
let structure_toret : concrete_st_viz α := {_set := final_set, _universe := final_universe}
{log := ls.log, val := ()} ~~> fun () =>
  save (s, s!"{op_string o}", structure_toret) ~~> fun () =>
  ok (structure_toret)



def merge_viz {α : Type} [ToString α] [DecidableEq α] [Hashable α] (merge : set α → set α → set α → set α) (l a b: WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α)) :
WithLog (concrete_st_viz α × String × concrete_st_viz α) (concrete_st_viz α) :=
let lval := l.val
let aval := a.val
let bval := b.val
let lset := lval._set
let aset := aval._set
let bset := bval._set
let l_univ := lval._universe
let a_univ := aval._universe
let b_univ := bval._universe
let set_result := merge lset aset bset
let universe_result := l_univ.union (a_univ.union b_univ)
let result : concrete_st_viz α := {_set:=set_result, _universe:= universe_result}
{log := l.log ++ [(lval, "LMerge", result)] ++
 a.log ++ [(aval, "AMerge", result)] ++
 b.log ++ [(bval, "BMerge", result)]
 val := ()} ~~> fun () => ok (result)


/-! ## Trace adapters for set-valued states

`Sal/Counterexample_Visualization/Trace.lean` holds the state-agnostic trace and
its renderer. A set state carries a display universe alongside the set itself, so
the transition a client wants (`do_ : set α → op → set α`) is not the transition
the trace needs (`concrete_st_viz α → op → concrete_st_viz α`) — these two adapt
one to the other by threading the universe, then defer to `stepWith`/`mergeWith`.

Argument order matches `do_viz`/`merge_viz`, so porting a client off the flat log
is mechanical. -/

/-- `do_viz` for traces: extend a trace by one `do_` edge, growing the universe by
the element the operation touches. -/
def do_trace {β : Type} {α : Type} [ToString α] [DecidableEq α] [Hashable α]
(do_ : set α → (ℕ × ℕ × β) → set α) (t : Trace (concrete_st_viz α)) (o : ℕ × ℕ × β)
(univ_add : (ℕ × ℕ × β) → α) (op_string : (ℕ × ℕ × β) → String) : Trace (concrete_st_viz α) :=
stepWith
  (fun s o => {_set := do_ s._set o, _universe := s._universe.insert (univ_add o)})
  op_string t o

/-- `merge_viz` for traces: a three-way merge node, over the union of the three
display universes. -/
def merge_trace {α : Type} [ToString α] [DecidableEq α] [Hashable α]
(merge : set α → set α → set α → set α)
(l a b : Trace (concrete_st_viz α)) : Trace (concrete_st_viz α) :=
mergeWith
  (fun ls as bs => {_set := merge ls._set as._set bs._set,
                    _universe := ls._universe.union (as._universe.union bs._universe)})
  l a b
