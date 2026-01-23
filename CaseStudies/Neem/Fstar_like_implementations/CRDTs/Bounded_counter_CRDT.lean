import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Std.Tactic.BVDecide
import CaseStudies.Neem_interfaces.Map_extended
import CaseStudies.Neem.Tactics.Sal
import Blaster
import Std.Data

open Classical

instance Ord (ℕ × ℕ) :=

@[simp] abbrev concrete_st := ℕ × Std.ExtTreeMap (ℕ × ℕ) Int
-- Increment map, decrement map, transfer map

@[simp]
def mysel {α : Type} [DecidableEq α] (s: map α Int) (k: α) : Int :=
if (contains s k) then (sel s k) else 0

@[simp]
def init_st : concrete_st:= (const_on empty 0, const_on empty 0, const_on empty 0)

@[simp]
def eq (a b: concrete_st) :=
(forall id, (contains (Prod.fst a) id = contains (Prod.fst b) id) ∧ (mysel (Prod.fst a) id = mysel (Prod.fst b) id)) ∧
(forall id, (contains (Prod.fst (Prod.snd a)) id = contains (Prod.fst (Prod.snd b)) id) ∧ (mysel (Prod.fst (Prod.snd a)) id = mysel (Prod.fst (Prod.snd b)) id)) ∧
(forall id, (contains (Prod.snd (Prod.snd a)) id = contains (Prod.snd (Prod.snd b)) id) ∧ (mysel (Prod.snd (Prod.snd a)) id = mysel (Prod.snd (Prod.snd b)) id))



-- Helper to get increment map from state
@[simp]
def get_inc (s: concrete_st) : map ℕ Int := Prod.fst s

-- Helper to get decrement map from state
@[simp]
def get_dec (s: concrete_st) : map ℕ Int := Prod.fst (Prod.snd s)

-- Helper to get transfer map from state
@[simp]
def get_transfers (s: concrete_st) : map (ℕ × ℕ) Int := Prod.snd (Prod.snd s)

-- Calculate a simplified value for the bounded counter
-- For a specific replica: its increments minus its decrements
@[simp]
def replica_value (replica: ℕ) (s: concrete_st) : Int :=
  mysel (get_inc s) replica - mysel (get_dec s) replica

-- Calculate the quota available for a replica
-- This is a simplified version: replica's own value plus net transfers
@[simp]
def quota (replica: ℕ) (s: concrete_st) : Int :=
  replica_value replica s

-- Increment operation - always succeeds (increment by 1)
@[simp]
def inc (replica: ℕ) (s: concrete_st) : concrete_st :=
  let inc_map := get_inc s
  let new_inc_map := upd inc_map replica (mysel inc_map replica + 1)
  (new_inc_map, get_dec s, get_transfers s)

-- Decrement operation - may fail if insufficient quota (decrement by 1)
def dec (replica: ℕ) (s: concrete_st) : Option concrete_st :=
  let q := quota replica s
  if q >= 1 then
    let dec_map := get_dec s
    let new_dec_map := upd dec_map replica (mysel dec_map replica + 1)
    some (get_inc s, new_dec_map, get_transfers s)
  else
    none

-- Transfer quota from sender to receiver - may fail if insufficient quota
def transfer (sender: ℕ) (receiver: ℕ) (amount: Int) (s: concrete_st) : Option concrete_st :=
  let q := quota sender s
  if q >= amount then
    let transfers := get_transfers s
    let pair := (sender, receiver)
    let new_transfers := upd transfers pair (mysel transfers pair + amount)
    some (get_inc s, get_dec s, new_transfers)
  else
    none

-- Merge operation for bounded counters
@[simp]
def merge (a b: concrete_st) : concrete_st :=
  -- Merge increment maps (take max like PN-Counter)
  let keys_inc := union (domain (get_inc a)) (domain (get_inc b))
  let u_inc := const_on keys_inc 0
  let merged_inc := iter_upd (fun k _ => max (mysel (get_inc a) k) (mysel (get_inc b) k)) u_inc

  -- Merge decrement maps (take max like PN-Counter)
  let keys_dec := union (domain (get_dec a)) (domain (get_dec b))
  let u_dec := const_on keys_dec 0
  let merged_dec := iter_upd (fun k _ => max (mysel (get_dec a) k) (mysel (get_dec b) k)) u_dec

  -- Merge transfer maps (take max - transfers are monotonically increasing)
  let keys_transfer := union (domain (get_transfers a)) (domain (get_transfers b))
  let u_transfer := const_on keys_transfer 0
  let merged_transfer := iter_upd (fun k _ => max (mysel (get_transfers a) k) (mysel (get_transfers b) k)) u_transfer

  (merged_inc, merged_dec, merged_transfer)

-- Operation types for the CRDT framework
inductive app_op_t : Type where
| Inc
| Dec
| Transfer (receiver: ℕ) (amount: ℕ)

abbrev op_t := ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s: concrete_st) (o: op_t) : concrete_st :=
match o with
| (_, (replica, app_op_t.Inc)) => inc replica s
| (_, (replica, app_op_t.Dec)) =>
    match dec replica s with
    | some s' => s'
    | none => s  -- If dec fails, state remains unchanged
| (_, (sender, app_op_t.Transfer receiver amount)) =>
    match transfer sender receiver amount s with
    | some s' => s'
    | none => s  -- If transfer fails, state remains unchanged

inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (_ _ : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)
