import LeanProofs.Interface.Implementation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image

/-!
# The set-wins multimap: its implementation tuple

The Set-wins multimap row of Table 1, Appendix `app:dt-set-wins-map`.

A `set k v` records the binding `(k,v)` under its own timestamp; a `del k`
erases every binding for `k`, whatever set it. Concurrent `set` wins over
`del`, which is where the name comes from, and it is also why `rc` orders
`del k` before `set k v`.

The lookup is accumulating rather than overwriting, because the state keeps
older bindings for a key alongside newer ones. This is the first row here
whose `Val_type` is a collection assembled from the state rather than a
component of it.
-/

namespace LeanProofs.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- `O_type`: bind a value to a key, or drop a key. -/
inductive Act (K V : Type) where
  | set (k : K) (v : V)
  | del (k : K)
  deriving DecidableEq, Repr

variable (K V : Type) [DecidableEq K] [DecidableEq V]

/-- `type = < O_type, Q_type, Val_type >`. A query names a key and is
answered by all the values currently bound to it. -/
@[reducible] def type : MRDTType where
  OType := Act K V
  decOType := inferInstance
  QType := K
  ValType := Finset V

/-- `Sigma`: the bindings, each tagged by the timestamp that created it. -/
abbrev St (K V : Type) := Finset ((K × V) × Timestamp)

variable {K V}

/-- `do(sigma, t, r, o)`. -/
def step (S : St K V) (e : Op (Act K V)) : St K V :=
  match e.op with
  | .set k v => insert ((k, v), e.time) S
  | .del k => S.filter (fun p => p.1.1 ≠ k)

/-- `merge(l,a,b)`, the same three-way shape as the OR-set: keep what both
branches kept, and take what either branch added. -/
def mergeState (l a b : St K V) : St K V := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- The bindings, with the timestamps erased. -/
def view (S : St K V) : Finset (K × V) := S.image Prod.fst

/-- `query(sigma, k)`: every value bound to `k`. -/
def lookup (S : St K V) (k : K) : Finset V :=
  ((view S).filter (fun p => p.1 = k)).image Prod.snd

/-- `rc`: `del k` is ordered before `set k v`. Operations on different keys
commute, and so are left unordered. -/
def rc : Act K V → Act K V → OrderResult
  | .del k, .set j _ => if k = j then OrderResult.Fst_then_snd else OrderResult.Either
  | .set k _, .del j => if k = j then OrderResult.Snd_then_fst else OrderResult.Either
  | _, _ => OrderResult.Either

variable (K V)

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
@[reducible] def D : Impl (type K V) where
  Sigma := St K V
  decSigma := inferInstance
  sigma0 := ∅
  do_ := step
  merge := mergeState
  query := lookup
  rc := rc

end LeanProofs.Implementations.SetWinsMap
