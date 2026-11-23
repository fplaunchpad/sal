import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image

/-!
# The set-wins map: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3;
`historySpec` is the `Spec` of Section 4, as a language of histories.
`issuance` is the guard `G` of Section 3.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs1.Implementations.SetWinsMap

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- `O_type`: bind a value to a key, or drop a key. -/
inductive AppOp (K V : Type) where
  | set (k : K) (v : V)
  | del (k : K)
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event (K V : Type) := Op (AppOp K V)

variable (K V : Type) [DecidableEq K] [DecidableEq V]

/-- `type = < O_type, Q_type, Val_type >`. A query names a key and is
answered by all the values currently bound to it. -/
@[reducible] def type : MRDTType where
  OType := AppOp K V
  decOType := inferInstance
  QType := K
  ValType := Finset V

/-- `Sigma`: the bindings, each tagged by the timestamp that created it. -/
abbrev St (K V : Type) := Finset ((K × V) × Timestamp)

variable {K V}

/-- `do(sigma, t, r, o)`. -/
def step (S : St K V) (e : Event K V) : St K V :=
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
def rc : AppOp K V → AppOp K V → OrderResult
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


/-! ## `Spec` -/

/-- `Spec`: an ordinary multimap, with no timestamps anywhere. -/
def specMachine : DeterministicSpec (type K V).OType (type K V).QType (type K V).ValType where
  State := Finset (K × V)
  initial := ∅
  update S o := match o with
    | .set k v => insert (k, v) S
    | .del k => S.filter (fun q => q.1 ≠ k)
  query S k := (S.filter (fun q => q.1 = k)).image Prod.snd

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type K V) := (specMachine K V).toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance (D K V).toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs1.Implementations.SetWinsMap
