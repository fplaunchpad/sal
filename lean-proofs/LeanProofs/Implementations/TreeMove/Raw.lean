import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Relation

/-!
# Tree move: the raw algorithm

The undo/insert/redo machinery of Appendix `app:dt-tree-move`, before the
state space is cut down to the coherent states. Everything here is a
definition; `Coherence.lean` proves the two facts `Definition.lean` needs to
build the tuple, and every obligation is in `VCs.lean`.

```
  T : Nat -> Option (Nat × Nat)      parent and metadata of each child
  root = 0, trash = 1
  f(T, o) = T                              when c = p or p ->+ c
          = T[c |-> some (p, m)]           otherwise
```

A log entry stores its move and the previous parent/metadata of that move's
child. Both accepted and rejected moves record it, and redo calls `push`
again, recomputing that old parent.

## Where the key lives

The appendix writes `k(e) = (t, r, p, m, c)` and reads the timestamp and
replica off the **event**. Definition 4 hands the specification the
operation, not the event, and the specification's `Legal` compares keys, so
the key has to sit in the operation for the specification to be stated at
all. `AppOp` therefore carries `time` and `rep` beside `p`, `m` and `c`, and
`Definition.lean`'s `issuance` closes the gap by admitting a move only when
those two fields are the issuing event's own. On every certified execution
this is the appendix's tuple, with the appendix's key. It is the same
deviation RGA makes for the identity an insertion allocates.

Because the key is now the whole operation, it is injective, which is what
the appendix means by "the full key defines collision behaviour on all
states".
-/

namespace LeanProofs1.Implementations.TreeMove

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

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

end LeanProofs1.Implementations.TreeMove
