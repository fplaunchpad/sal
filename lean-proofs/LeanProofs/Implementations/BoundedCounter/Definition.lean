import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The bounded counter with rights transfer: the implementation tuple

The Bounded counter row of Table 1, following Appendix
`app:dt-bounded-counter` and Balegas et al. Each replica may decrement only
against its local rights and may transfer rights to another replica.

```
  R : Nat -> Nat -> Nat     R i i counts i's increments
                            R i j counts i's transfers to j
  U : Nat -> Nat            U i counts i's decrements
```

Every cell is single-writer and cumulative, which is what makes the
componentwise **maximum** merge safe: a missing incoming transfer only
underestimates the available rights.

```
  do((R,U), t, i, inc a)        = (R[(i,i) += a], U)
  do((R,U), t, i, dec a)        = (R, U[i += a])
  do((R,U), t, i, transfer a j) = (R[(i,j) += a], U)
  merge(l, a, b)                = (max R_a R_b, max U_a U_b)     l unused
```

`rc` is empty: every pair of events commutes, since each effector adds to a
cell and addition commutes.

`Negative.lean` shows that this row nevertheless has no obligation bundle on
this route, and the appendix says why: the cumulative cells need an event's
dependencies to be its **full causal past**, while Section 5 fixes them to
the non-commuting visible predecessors.
-/

namespace LeanProofs1.Implementations.BoundedCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- `O_type`. Amounts are non-negative, as in the source. -/
inductive AppOp where
  | increment (amount : Nat)
  | decrement (amount : Nat)
  | transfer (amount target : Nat)
  deriving DecidableEq, Repr

/-- The queries: the counter's value, or one replica's rights. -/
inductive Query where
  | value
  | localRights (replica : Nat)
  deriving DecidableEq, Repr

/-- `Sigma`: the rights matrix and the consumption vector. -/
structure St where
  R : Nat → Nat → Nat
  U : Nat → Nat

@[ext] theorem St.ext {s t : St} (hR : ∀ i j, s.R i j = t.R i j)
    (hU : ∀ i, s.U i = t.U i) : s = t := by
  cases s; cases t
  simp_all only [St.mk.injEq]
  exact ⟨funext (fun i => funext (hR i)), funext hU⟩

/-- `sigma0`: every cell zero. -/
def initial : St := ⟨fun _ _ => 0, fun _ => 0⟩

/-- Add `amount` to one entry of a vector. -/
def bump (f : Nat → Nat) (r amount : Nat) : Nat → Nat :=
  fun k => f k + if k = r then amount else 0

/-- Add `amount` to one entry of a matrix. -/
def bumpMatrix (f : Nat → Nat → Nat) (r c amount : Nat) : Nat → Nat → Nat :=
  fun i j => f i j + if i = r ∧ j = c then amount else 0

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Query
  ValType := Int

/-- `do`: each effector adds its amount to the issuer's own cell. -/
def step (s : St) (e : Op AppOp) : St :=
  match e.op with
  | .increment a => { s with R := bumpMatrix s.R e.rep e.rep a }
  | .decrement a => { s with U := bump s.U e.rep a }
  | .transfer a j => { s with R := bumpMatrix s.R e.rep j a }

/-- `merge`: componentwise maximum. The ancestor is unused. -/
def mergeState (_l a b : St) : St :=
  ⟨fun i j => max (a.R i j) (b.R i j), fun i => max (a.U i) (b.U i)⟩

/-- `B_i`: the rights replica `r` still holds. -/
def localRights (n : Nat) (s : St) (r : Nat) : Int :=
  (s.R r r : Int)
    + ∑ j ∈ (Finset.range n).erase r, (s.R j r : Int)
    - ∑ j ∈ (Finset.range n).erase r, (s.R r j : Int) - (s.U r : Int)

/-- `V`: the counter's value, above the lower bound `K`. -/
def value (n : Nat) (K : Int) (s : St) : Int :=
  K + ∑ r ∈ Finset.range n, (s.R r r : Int) - ∑ r ∈ Finset.range n, (s.U r : Int)

/-- `rc` is empty: every pair of events commutes. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, over `n` replicas
with lower bound `K`. -/
noncomputable def D (n : Nat) (K : Int) : Impl type where
  Sigma := St
  decSigma := fun _ _ => Classical.propDecidable _
  sigma0 := initial
  do_ := step
  merge := mergeState
  query s q := match q with
    | .value => value n K s
    | .localRights r => localRights n s r
  rc := rcOf

/-! ## Issuance -/

/-- Issuance: a decrement or a transfer must be funded from the rights the
issuer holds in its own original state, and a transfer must name another
replica of the fixed universe. -/
def issuance (n : Nat) (K : Int) : Issuance (D n K).toMRDTSig where
  CanIssue := fun e s =>
    e.rep < n ∧ match e.op with
      | .increment _ => True
      | .decrement a => (a : Int) ≤ localRights n s e.rep
      | .transfer a j => j < n ∧ j ≠ e.rep ∧ (a : Int) ≤ localRights n s e.rep

end LeanProofs1.Implementations.BoundedCounter
