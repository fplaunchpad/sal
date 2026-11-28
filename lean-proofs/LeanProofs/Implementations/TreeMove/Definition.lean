import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Relation

/-!
# Tree move: the implementation and the specification

The tuple the obligations are stated about, and the definitions and
coherence facts it is built from. Every obligation is in `VCs.lean`.

```
  Sigma  = { s = (Q, T) | s = C(events(s)) }     the coherent states
  sigma0 = ([], T0)
  e(s)   = receive(s, e)
  merge(l, a, b) = foldl(receive, a, events(b))
  q((Q,T), ()) = visible(T)
```

`Sigma` is the **coherent** state space, exactly as the appendix defines it.
That is what makes `rc` empty a theorem here rather than a hedge: the
appendix's "complete deliveries commute on the coherent state space" is
`VCs.lean`'s `all_commute`, over the whole of `Sigma`.

Unlike every other row, this file is not proof-free, and it cannot be. The
state space is a **subtype**, `St = {s : Raw // Coherent s}`, so `step` and
`mergeState` have to carry a coherence proof to land in it at all. The three
parts below are the parts that used to be three files.

## 1. The raw algorithm

The undo/insert/redo machinery of Appendix `app:dt-tree-move`, before the
state space is cut down.

```
  T : Nat -> Option (Nat × Nat)      parent and metadata of each child
  root = 0, trash = 1
  f(T, o) = T                              when c = p or p ->+ c
          = T[c |-> some (p, m)]           otherwise
```

A log entry stores its move and the previous parent/metadata of that move's
child. Both accepted and rejected moves record it, and redo calls `push`
again, recomputing that old parent.

## 2. Coherence

The one theorem this row turns on. On a coherent state, `receive` and
`merge` return the `build` of a key-descending list, and that list is
determined by its **set** of moves. So delivery order does not matter, which
is the appendix's claim that complete deliveries commute on the coherent
state space, including their undo metadata.

```
  undo_push        undo inverts push, recomputing the old parent
  applyRaw_build   applyRaw o (build E) = build (insertDesc o E)
  receive_eq       receive s o = build (ins o (events s))   on coherent s
  desc_unique      two descending lists with the same members are equal
  coh_ext          two coherent states with the same moves are equal
```

`applyRaw_build` needs no hypothesis at all: `build` keeps the log and the
tree in lockstep, so undoing the newest entry recovers the older tree
exactly.

## 3. The tuple and the specification

`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3,
with `rc` empty; `historySpec` is the `Spec` of Section 4, a plain tree with
no undo log; `issuance` is the guard `G`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.TreeMove

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-! ## 1. The raw algorithm -/
/-- `O_type`: attach child `c` to parent `p` with metadata `m`, under the
issuing event's timestamp and replica. -/
structure AppOp where
  time : Nat
  rep : Nat
  parent : Nat
  mdata : Nat
  child : Nat
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event := Op AppOp

/-- `T(c)` stores the parent and metadata of child `c`. -/
abbrev Tree := Nat → Option (Nat × Nat)

/-- The empty tree. -/
def T0 : Tree := fun _ => none

/-- The key type, ordered lexicographically. -/
abbrev KeyT := Nat ×ₗ Nat ×ₗ Nat ×ₗ Nat ×ₗ Nat

/-- `k(e) = (t, r, p, m, c)`. The full key totalises timestamp collisions;
with globally unique timestamps, comparison is exactly the source
algorithm's timestamp test. -/
def key (o : AppOp) : KeyT :=
  toLex (o.time, toLex (o.rep, toLex (o.parent, toLex (o.mdata, o.child))))

/-- `x ->_T y`. -/
def Edge (T : Tree) (x y : Nat) : Prop := ∃ m, T x = some (y, m)

/-- `x ->_T^+ y`: a nonempty finite path. -/
def Path (T : Tree) (x y : Nat) : Prop := Relation.TransGen (Edge T) x y

open Classical in
/-- `f(T, e)`. The first branch is the rejection test: the child is its own
parent, or the parent already has a path to the child. -/
noncomputable def f (T : Tree) (o : AppOp) : Tree :=
  if o.child = o.parent ∨ Path T o.parent o.child then T
  else Function.update T o.child (some (o.parent, o.mdata))

/-- A log entry `q = (o, u)`. -/
abbrev LogEntry := AppOp × Option (Nat × Nat)

/-- A raw state: a newest-first log and a maintained tree. -/
abbrev Raw := List LogEntry × Tree

/-- `push((Q,T), o)`. -/
noncomputable def push (s : Raw) (o : AppOp) : Raw :=
  ((o, s.2 o.child) :: s.1, f s.2 o)

/-- `undo((o,u), T) = T[c |-> u]`. -/
def undo (q : LogEntry) (T : Tree) : Tree :=
  Function.update T q.1.child q.2

/-- `build`: the oldest-first result of a newest-first list. -/
noncomputable def build : List AppOp → Raw
  | [] => ([], T0)
  | o :: E => push (build E) o

/-- `events(Q, T)`, in log order. -/
def ops (s : Raw) : List AppOp := s.1.map Prod.fst

/-- `applyRaw(e, Q, T)`: undo the newer entries, insert `e`, redo. -/
noncomputable def applyRaw (o : AppOp) : List LogEntry → Tree → Raw
  | [], T => push ([], T) o
  | q :: Q, T =>
      if key o < key q.1 then push (applyRaw o Q (undo q T)) q.1
      else push (q :: Q, T) o

open Classical in
/-- `receive(s, e)`: a duplicate is suppressed. -/
noncomputable def receive (s : Raw) (o : AppOp) : Raw :=
  if o ∈ ops s then s else applyRaw o s.1 s.2

/-- `merge(l, a, b)` on raw states: deliver the other branch's log to the
first branch. The ancestor is ignored. -/
noncomputable def mergeRaw (a b : Raw) : Raw := (ops b).foldl receive a

/-! ## The query -/

/-- `hidden(T, x)`. -/
def hidden (T : Tree) (x : Nat) : Prop := x = 1 ∨ Path T x 1

open Classical in
/-- `visible(T)`: hide the trash node and its descendants. -/
noncomputable def visible (T : Tree) : Tree :=
  fun x => if hidden T x then none else T x

/-! ## Descending insertion

`applyRaw` is an insertion into a key-descending list. These are the list
operations it performs, stated separately so that `Coherence.lean` can prove
the correspondence.
-/

/-- Insert into a key-descending list. -/
def insertDesc (o : AppOp) : List AppOp → List AppOp
  | [] => [o]
  | a :: E => if key o < key a then a :: insertDesc o E else o :: a :: E

open Classical in
/-- Insertion that suppresses a duplicate, matching `receive`. -/
noncomputable def ins (o : AppOp) (E : List AppOp) : List AppOp :=
  if o ∈ E then E else insertDesc o E

/-- Deliver a whole list. -/
noncomputable def insAll (L E : List AppOp) : List AppOp :=
  L.foldl (fun E' o => ins o E') E

/-- The log is strictly descending in the key. -/
def Desc (E : List AppOp) : Prop := E.Pairwise (fun a b => key b < key a)

/-- The appendix's log-consistency invariant, as it glosses it. Logs have
distinct moves in descending key order, each undo edge is consistent with
its older log suffix, and the maintained tree is their oldest-first result.
The second and third are exactly `s = build(events s)`, since `build`
recomputes both. -/
def Coherent (s : Raw) : Prop := Desc (ops s) ∧ s = build (ops s)

/-! ## 2. Coherence -/
/-! ## The key -/

/-- The full key is the whole move, so it determines it. -/
theorem key_inj {o o' : AppOp} (h : key o = key o') : o = o' := by
  obtain ⟨t, r, p, m, c⟩ := o
  obtain ⟨t', r', p', m', c'⟩ := o'
  simp only [key, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  subst h1; subst h2; subst h3; subst h4; subst h5; rfl

/-- Distinct moves have distinct keys. -/
theorem key_ne {o o' : AppOp} (h : o ≠ o') : key o ≠ key o' :=
  fun hk => h (key_inj hk)

/-! ## `build` and its log -/

theorem ops_push (s : Raw) (o : AppOp) : ops (push s o) = o :: ops s := rfl

/-- `build` lays down exactly the list it is given. -/
theorem ops_build : ∀ E : List AppOp, ops (build E) = E
  | [] => rfl
  | o :: E => by rw [build, ops_push, ops_build E]

/-- **`undo` inverts `push`.** Both branches of `f` move only the child's
own entry, and the entry `push` records is that child's previous value. -/
theorem undo_push (T : Tree) (o : AppOp) :
    undo (o, T o.child) (f T o) = T := by
  simp only [undo, f]
  split_ifs with h
  · exact Function.update_eq_self _ _
  · rw [Function.update_idem, Function.update_eq_self]

/-- **`applyRaw` is descending insertion.** Undo, insert, redo on the state
`build E` returns the state of the list `E` with `o` inserted in key
order. -/
theorem applyRaw_build (o : AppOp) : ∀ E : List AppOp,
    applyRaw o (build E).1 (build E).2 = build (insertDesc o E)
  | [] => rfl
  | a :: E => by
      have hb : build (a :: E) = push (build E) a := rfl
      rw [hb]
      show applyRaw o ((a, (build E).2 a.child) :: (build E).1)
          (f (build E).2 a) = _
      rw [applyRaw, insertDesc]
      by_cases h : key o < key a
      · simp only [h, if_true, undo_push]
        rw [applyRaw_build o E]
        rfl
      · simp only [h, if_false]
        rfl

/-! ## Descending lists -/

theorem mem_insertDesc (o x : AppOp) : ∀ E : List AppOp,
    x ∈ insertDesc o E ↔ x = o ∨ x ∈ E
  | [] => by simp [insertDesc]
  | a :: E => by
      by_cases h : key o < key a
      · simp only [insertDesc, h, if_true, List.mem_cons, mem_insertDesc o x E]
        tauto
      · simp only [insertDesc, h, if_false, List.mem_cons]

/-- A head of a descending list does not recur in its tail. -/
theorem notMem_of_desc {a : AppOp} {E : List AppOp} (h : Desc (a :: E)) :
    a ∉ E := by
  intro hm
  exact absurd ((List.pairwise_cons.mp h).1 a hm) (lt_irrefl _)

/-- Descending insertion preserves the invariant. -/
theorem desc_insertDesc {o : AppOp} : ∀ {E : List AppOp}, Desc E → o ∉ E →
    Desc (insertDesc o E)
  | [], _, _ => by simp [insertDesc, Desc]
  | a :: E, hd, hne => by
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hd
      have hea : o ≠ a := fun hq => hne (hq ▸ List.mem_cons_self ..)
      have heE : o ∉ E := fun hm => hne (List.mem_cons_of_mem _ hm)
      by_cases h : key o < key a
      · simp only [insertDesc, h, if_true]
        refine List.pairwise_cons.mpr ⟨?_, desc_insertDesc htail heE⟩
        intro x hx
        rcases (mem_insertDesc o x E).mp hx with rfl | hx'
        · exact h
        · exact hhead x hx'
      · have hak : key a < key o :=
          lt_of_le_of_ne (not_lt.mp h) (key_ne (Ne.symm hea))
        simp only [insertDesc, h, if_false]
        refine List.pairwise_cons.mpr ⟨?_, hd⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hak
        · exact lt_trans (hhead x hx') hak

/-- **Two descending lists with the same members are equal.** -/
theorem desc_unique : ∀ {E₁ E₂ : List AppOp}, Desc E₁ → Desc E₂ →
    (∀ x, x ∈ E₁ ↔ x ∈ E₂) → E₁ = E₂
  | [], [], _, _, _ => rfl
  | [], b :: E₂, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | a :: E₁, [], _, _, h => absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
  | a :: E₁, b :: E₂, h₁, h₂, h => by
      obtain ⟨g₁, t₁⟩ := List.pairwise_cons.mp h₁
      obtain ⟨g₂, t₂⟩ := List.pairwise_cons.mp h₂
      have hab : a = b := by
        by_contra hne
        have ha2 : a ∈ E₂ :=
          (List.mem_cons.mp ((h a).mp (List.mem_cons_self ..))).resolve_left hne
        have hb1 : b ∈ E₁ :=
          (List.mem_cons.mp ((h b).mpr (List.mem_cons_self ..))).resolve_left
            (Ne.symm hne)
        exact absurd (lt_trans (g₂ a ha2) (g₁ b hb1)) (lt_irrefl _)
      subst hab
      have hmem : ∀ x, x ∈ E₁ ↔ x ∈ E₂ := by
        intro x
        constructor
        · intro hx
          rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
          · exact absurd hx (notMem_of_desc h₁)
          · exact hx'
        · intro hx
          rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
          · exact absurd hx (notMem_of_desc h₂)
          · exact hx'
      rw [desc_unique t₁ t₂ hmem]

/-! ## Duplicate-suppressing insertion -/

theorem mem_ins (o x : AppOp) (E : List AppOp) :
    x ∈ ins o E ↔ x = o ∨ x ∈ E := by
  unfold ins
  split_ifs with h
  · constructor
    · exact Or.inr
    · rintro (rfl | hx) <;> [exact h; exact hx]
  · exact mem_insertDesc o x E

theorem desc_ins {o : AppOp} {E : List AppOp} (hd : Desc E) : Desc (ins o E) := by
  unfold ins
  split_ifs with h
  · exact hd
  · exact desc_insertDesc hd h

theorem mem_insAll (x : AppOp) : ∀ (L E : List AppOp),
    x ∈ insAll L E ↔ x ∈ L ∨ x ∈ E
  | [], E => by simp [insAll]
  | o :: L, E => by
      show x ∈ insAll L (ins o E) ↔ _
      rw [mem_insAll x L (ins o E), mem_ins, List.mem_cons]
      tauto

theorem desc_insAll : ∀ (L : List AppOp) {E : List AppOp}, Desc E →
    Desc (insAll L E)
  | [], _, hd => hd
  | _ :: L, _, hd => desc_insAll L (desc_ins hd)

/-! ## Coherence -/

theorem coherent_build {E : List AppOp} (hd : Desc E) : Coherent (build E) :=
  ⟨by rw [ops_build]; exact hd, by rw [ops_build]⟩

theorem coherent_init : Coherent (([], T0) : Raw) :=
  ⟨by simp [ops, Desc], rfl⟩

/-- **The delivery equation.** -/
theorem receive_eq {s : Raw} (hc : Coherent s) (o : AppOp) :
    receive s o = build (ins o (ops s)) := by
  unfold receive ins
  split_ifs with h
  · exact hc.2
  · conv_lhs => rw [hc.2]
    exact applyRaw_build o (ops s)

/-- **`receive` lands in the coherent state space.** -/
theorem receive_coherent {s : Raw} (hc : Coherent s) (o : AppOp) :
    Coherent (receive s o) := by
  rw [receive_eq hc]; exact coherent_build (desc_ins hc.1)

theorem ops_receive {s : Raw} (hc : Coherent s) (o : AppOp) :
    ops (receive s o) = ins o (ops s) := by
  rw [receive_eq hc, ops_build]

/-- **The merge equation.** -/
theorem mergeRaw_eq : ∀ (L : List AppOp) {a : Raw}, Coherent a →
    L.foldl receive a = build (insAll L (ops a))
  | [], _, ha => ha.2
  | o :: L, a, ha => by
      show L.foldl receive (receive a o) = _
      rw [mergeRaw_eq L (receive_coherent ha o), ops_receive ha]
      rfl

/-- **`merge` lands in the coherent state space.** -/
theorem mergeRaw_coherent {a : Raw} (ha : Coherent a) (b : Raw) :
    Coherent (mergeRaw a b) := by
  rw [mergeRaw, mergeRaw_eq _ ha]
  exact coherent_build (desc_insAll _ ha.1)

theorem ops_mergeRaw {a : Raw} (ha : Coherent a) (b : Raw) (x : AppOp) :
    x ∈ ops (mergeRaw a b) ↔ x ∈ ops b ∨ x ∈ ops a := by
  rw [mergeRaw, mergeRaw_eq _ ha, ops_build, mem_insAll]

/-- **A coherent state is its move set.** -/
theorem coh_ext {s t : Raw} (hs : Coherent s) (ht : Coherent t)
    (h : ∀ x, x ∈ ops s ↔ x ∈ ops t) : s = t := by
  rw [hs.2, ht.2, desc_unique hs.1 ht.1 h]

/-! ## 3. The tuple and the specification -/
/-- `type = < O_type, Q_type, Val_type >`. The query returns the visible
tree. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Tree

/-- `Sigma`: the coherent states, as the appendix's `Sigma` is defined. -/
abbrev St := {s : Raw // Coherent s}

/-- `do(sigma, t, r, o)`: deliver the move, suppressing a duplicate. -/
noncomputable def step (s : St) (e : Event) : St :=
  ⟨receive s.1 e.op, receive_coherent s.2 e.op⟩

/-- `merge(l, a, b)`: deliver the other branch's log. The ancestor is
ignored. -/
noncomputable def mergeState (_l a b : St) : St :=
  ⟨mergeRaw a.1 b.1, mergeRaw_coherent a.2 b.1⟩

/-- The tree the client sees, with the trash branch hidden. -/
noncomputable def view (s : St) : Tree := visible s.1.2

/-- `rc` is empty. For this row that is a claim about the coherent state
space, and `VCs.lean` proves it. -/
def rc : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

Reducible so that `D.Sigma` unfolds to `St` during instance search. -/
@[reducible] noncomputable def D : Impl type where
  Sigma := St
  decSigma := fun _ _ => Classical.propDecidable _
  sigma0 := ⟨([], T0), coherent_init⟩
  do_ := step
  merge := mergeState
  query s _ := view s
  rc := rc

/-! ## `Spec`

The independent state is a tree together with an update prefix used for
admission. The specification tests the resulting graph directly: it has no
undo log and does not call the implementation's ancestor test. Its states
remain acyclic from `T0`.
-/

/-- `Acyclic(T)`. -/
def Acyclic (T : Tree) : Prop := ∀ x, ¬ Path T x x

open Classical in
/-- `move_spec(T, o)`: the ordinary in-place move, kept only when the
resulting graph is acyclic. A cycle-rejected move still extends the
prefix. -/
noncomputable def moveSpec (T : Tree) (o : AppOp) : Tree :=
  let T' := Function.update T o.child (some (o.parent, o.mdata))
  if Acyclic T' then T' else T

/-- `Legal(h)`: distinct moves in nondecreasing key order, none naming the
root or the trash as its child. -/
def Legal (h : List AppOp) : Prop :=
  h.Nodup ∧ h.Pairwise (fun a b => key a ≤ key b)
    ∧ ∀ o ∈ h, o.child ≠ 0 ∧ o.child ≠ 1

/-- `Spec`: a plain tree, with no log and no ancestor test. -/
noncomputable def specMachine :
    HistoryMachine type.OType type.QType type.ValType where
  State := List AppOp × Tree
  initial := ([], T0)
  transition s label t :=
    match label with
    | .update o => Legal (s.1 ++ [o]) ∧ t = (s.1 ++ [o], moveSpec s.2 o)
    | .query _ answer => t = s ∧ answer = visible s.2

/-- `Spec` as a history language. -/
noncomputable def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- Issuance: the wrapper reserves root and trash as children and requires a
fresh event identifier. A destination need not exist or be visible, and a
hidden child may be moved out of trash; there is no additional visibility
guard. The first two conjuncts are the deviation `Raw.lean` documents: they
pin the operation's copy of the key to the issuing event's own, so that on
every certified execution the key is the appendix's `k(e)`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun e s =>
    e.op.time = e.time ∧ e.op.rep = e.rep
      ∧ (∀ o ∈ ops (s : St).1, (o.time, o.rep) ≠ (e.time, e.rep))
      ∧ e.op.child ≠ 0 ∧ e.op.child ≠ 1

end LeanProofs.NoSpecNonComm.Implementations.TreeMove
