import LeanProofs.Interface.Implementation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image

/-!
# The multi-value register: its implementation tuple

The Multivalue register row of Table 1, Appendix `app:dt-mvr`.

This row is **defined but not certified here**. `Obstruction.lean` records
why, with a machine-checked proof.

A write carries the timestamps it supersedes: `write(v, W)` installs its own
tagged value and drops every entry whose timestamp `W` names. Concurrent
writes survive together, because neither names the other.

`rc` is empty, as the appendix states. The tuple below takes `rc` as a
parameter all the same, because the obstruction is about *every* choice of
it, not only the empty one.
-/

namespace LeanProofs.Implementations.MVRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- `O_type`: write a value, superseding the writes whose timestamps `W`
names. List order and duplicates do not matter. -/
inductive Act where
  | write (v : Nat) (W : List Timestamp)
  deriving DecidableEq, Repr

/-- `type = < O_type, Q_type, Val_type >`. The query returns every value
still present. -/
@[reducible] def type : MRDTType where
  OType := Act
  decOType := inferInstance
  QType := Unit
  ValType := Finset Nat

/-- `Sigma`: tagged writes, a timestamp paired with its value. -/
abbrev St := Finset (Timestamp × Nat)

/-- `do(sigma, t, r, write(v, W)) = {(t,v)} union {(n,w) in S | n not in W}`.
The replica identifier does not enter. -/
def step (S : St) (e : Op Act) : St :=
  match e.op with
  | .write v W => insert (e.time, v) (S.filter (fun p => p.1 ∉ W))

/-- `merge(l,a,b)`, the same three-way shape as the OR-set. -/
def mergeState (l a b : St) : St := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- The values the client sees. -/
def values (S : St) : Finset Nat := S.image Prod.snd

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, for an arbitrary
`rc`. -/
@[reducible] def Dwith (rc : Act → Act → OrderResult) : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := ∅
  do_ := step
  merge := mergeState
  query S _ := values S
  rc := rc

/-- The tuple the paper gives, whose `rc` is empty. -/
@[reducible] def D : Impl type := Dwith (fun _ _ => OrderResult.Either)

end LeanProofs.Implementations.MVRegister
