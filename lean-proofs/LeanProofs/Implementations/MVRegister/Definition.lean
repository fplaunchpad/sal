import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Finset.Basic

/-!
# The multi-value register: the implementation tuple

The MVR row of Table 1, as the compact implementation of
`LeanProofs/Implementations/MVRegister/Definition.lean`: the state holds the
live tagged writes, a write records its own tag and drops the tags it names,
and the query returns the surviving values.

```
  o = write v O        value v, overwriting the tags in O
  do(s, e)             = insert (time(e), v) (s without the tags of O)
  merge(l, a, b)       = (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)
```

A write's tag is its **timestamp**. That is the fact `Negative.lean` turns
on: the tuple below is parameterised by an arbitrary `rc`, because no choice
of one satisfies `Laws(D_type)`.

No proof appears in this file.
-/

namespace LeanProofs1.Implementations.MVRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- `O_type`: write a value and name the tags it supersedes. -/
inductive AppOp where
  | write (value : Nat) (overwrites : List Nat)
  deriving DecidableEq, Repr

/-- The tags a write supersedes. -/
def overwrites : AppOp → List Nat
  | .write _ O => O

/-- The value a write carries. -/
def writeValue : AppOp → Nat
  | .write v _ => v

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Finset Nat

/-- `Sigma`: the live tagged writes. A tag is a timestamp. -/
abbrev St := Finset (Nat × Nat)

/-- `do`: record this write under its own timestamp, and drop every tag it
names. -/
def step (s : St) (e : Op AppOp) : St :=
  insert (e.time, writeValue e.op) (s.filter (fun p => p.1 ∉ overwrites e.op))

/-- `merge`: the OR-shape, keeping what both kept and what either added. -/
def mergeState (l a b : St) : St := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, at an arbitrary
`rc`. Everything but `rc` is the row's own. -/
def D (rc : AppOp → AppOp → OrderResult) : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := ∅
  do_ := step
  merge := mergeState
  query s _ := s.image Prod.snd
  rc := rc

end LeanProofs1.Implementations.MVRegister
