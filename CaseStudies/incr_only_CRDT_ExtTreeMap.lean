import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Linarith
import Std



@[simp]
abbrev concrete_st := Std.ExtTreeMap ℕ Int

@[simp]
def sel (s : concrete_st) (k : ℕ) : Int := match (Std.ExtTreeMap.get? s k) with
| some n => n
| none => 0

#check sel

@[simp]
def init_st : concrete_st := {}

@[simp]
def eq (a b : concrete_st) := a = b


inductive app_op_t : Type where
| Incr

abbrev op_t:= ℕ × ℕ × app_op_t

@[simp]
def distinct_ops (op1 op2 : op_t) := Prod.fst op1 != Prod.fst op2

@[simp]
def get_rid (o : op_t) :=
match o with
| (_, (rid, _)) => rid

@[simp]
def do_ (s : concrete_st) (o : op_t) :=
match o with
| (_, (r, _)) => Std.ExtTreeMap.insert s r (sel s r + 1)


inductive rc_res : Type where
| Fst_then_snd
| Snd_then_fst
| Either

@[simp]
def rc (o1 o2 : op_t) := rc_res.Either

@[simp]
def commutes_with (o1 o2 : op_t) :=
    forall s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)

@[simp, grind]
def merge_helper (klist : List ℕ) (a b : concrete_st) : concrete_st :=
match klist with
| [] => {}
| key::keys => Std.ExtTreeMap.insert (merge_helper keys a b) key (max (sel a key) (sel b key))

@[simp, grind]
def merge (a b : concrete_st) : concrete_st :=
let keys1 := Std.ExtTreeMap.keys a
let keys2 := Std.ExtTreeMap.keys b
let keys:= keys1 ∪ keys2
merge_helper keys a b



@[simp, grind]
theorem merge_helper_max (k: ℕ) (klist: List ℕ) (a b: concrete_st) :
List.contains klist k → (merge_helper klist a b)[k]? = some (max (sel a k) (sel b k)) := by
  intros h
  aesop
  all_goals (
    induction klist with
        | nil => contradiction
        | cons a b ih => ( dsimp [merge_helper]  <;>
        first
          | grind
          | aesop )
  )

@[simp, grind]
theorem merge_helper_contains (k: ℕ) (klist: List ℕ) (a b : concrete_st) :
List.contains klist k = false → (merge_helper klist a b)[k]? = none := by
intros h
aesop
induction klist <;> aesop

@[grind, simp]
theorem key_no_contains (k: ℕ) (s: concrete_st) :
k ∉ (Std.ExtTreeMap.keys s) ↔ s[k]? = none := by
  aesop

@[grind, simp]
theorem key_contains (k: ℕ) (s: concrete_st) :
k ∈ (Std.ExtTreeMap.keys s) ↔ ∃ n, s[k]? = some n := by
  dsimp
  grind

@[grind, simp]
theorem emptyset_emptykeys (s: concrete_st) :
s = {} → Std.ExtTreeMap.keys s = [] := by
  aesop


syntax tactic " and_then " tactic : tactic

macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; $b:tactic)





theorem no_rc_chain (o1 : op_t) (o2 : op_t) (o3 : op_t) :
(distinct_ops o1 o2 ∧ distinct_ops o2 o3)
→ (¬(rc o1 o2 = rc_res.Fst_then_snd ∧ rc o2 o3 = rc_res.Fst_then_snd))
:= by
    dsimp
    grind

theorem cond_comm_base (s: concrete_st) (o1: op_t) (o2: op_t) (o3: op_t):
(distinct_ops o1 o2 ∧ distinct_ops o2 o3 ∧ distinct_ops o1 o3
    ∧ rc o1 o2 = rc_res.Fst_then_snd ∧ ¬(rc o2 o3 = rc_res.Either))
→
eq (do_ (do_ (do_ s o1) o2) o3) (do_ (do_ (do_ s o2) o1) o3)
:= by
  dsimp
  grind


-- some example theorems to motivate extensionality


theorem insert_useless (s: Std.ExtTreeMap ℕ Int) (n: ℕ) (m: ℕ) (val: Int):
¬ m = n → (s.insert n val)[m]? = s[m]? := by
intros h
grind

theorem insert_insert (s: Std.ExtTreeMap ℕ Int) (k1 k2 : ℕ) (v1 v2: Int) :
¬ k1 = k2 → (s.insert k1 v1).insert k2 v2 = (s.insert k2 v2).insert k1 v1 := by
  intros h
  ext
  grind



@[simp]
lemma List.Subset.union_left {α : Type*} [DecidableEq α] {xs ys : List α} : xs ⊆ xs ∪ ys := by
  simp +contextual [List.subset_def]

@[simp]
lemma List.Subset.union_eq_right_iff {α : Type*} [DecidableEq α] {xs ys : List α} : xs ∪ ys = ys ↔ xs ⊆ ys :=
  ⟨fun h => h ▸ List.Subset.union_left, List.Subset.union_eq_right⟩

@[simp]
lemma List.Subset.union_self {α : Type*} [DecidableEq α] {xs : List α} : xs ∪ xs = xs := by simp


theorem rc_non_comm (o1: op_t) (o2: op_t) :
distinct_ops o1 o2 ∧ get_rid o1 != get_rid o2 →
(rc o1 o2 = rc_res.Either ↔ commutes_with o1 o2) := by
  dsimp
  sorry -- TODO: Blaster removed in v4.28 bump; re-close with grind or Aristotle


theorem merge_comm (a b:concrete_st) :
(eq (merge a b) (merge b a)) :=
by
  dsimp
  grind


theorem merge_idem_prime (s: Std.ExtTreeMap ℕ Int) (k: ℕ) (a: Int):
(merge_helper (Std.ExtTreeMap.keys s ∪ Std.ExtTreeMap.keys s) s s)[k]? = some a
→  s[k]? = some a := by
simp
intros





theorem merge_idem (s: concrete_st):
eq (merge s s) s := by
  dsimp
  sorry -- TODO: Blaster removed in v4.28 bump; re-close with grind or Aristotle

theorem base_2op (o1 o2:op_t) :
 ((rc o2 o1) = rc_res.Fst_then_snd ∨ (rc o2 o1) = rc_res.Either) ∧ get_rid o1 != get_rid o2 ∧
                    distinct_ops o1 o2
  →
   eq (merge (do_ init_st o1) (do_ init_st o2)) (do_ (merge init_st (do_ init_st o2)) o1)
   := by
    dsimp
    aesop
    grind
    ext
    aesop
    grind

theorem lem_0op (a b:concrete_st) (ol:op_t) :
eq (merge (do_ a ol) (do_ b ol)) (do_ (merge a b) ol) :=
  by
  dsimp
  aesop
  {
    ext
    aesop
    auto [*]
  }
