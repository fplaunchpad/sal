import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec
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

`Negative.lean` shows that this row has no obligation bundle at Section 5's
reading, and the appendix says why: the cumulative cells need an event's
dependencies to be its **full causal past**, while Section 5 fixes them to
the non-commuting visible predecessors. It also shows that enlarging the
dependency set alone does not suffice, because `lo^C_E` is empty here and so
maximality is vacuous. `VCs.lean` proves all five conditions once both are
generalised together, through `Interface/CausalRoute.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.BoundedCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

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

/-! ## `Spec`

The value is specified exactly. The rights query is left
**unconstrained**, and it has to be: a replica's rights are not a function
of the operation sequence. `transfer a j` records its target but not its
issuer, and the sequential alphabet is `O_type`, which drops the issuer, so
no history language over `O_type` can pin `B_i` down. Rights are the
mechanism by which this row enforces the bound rather than part of the
bound, and `CanIssue` below is where they are consumed.

This is why `Spec` is given as a `HistoryMachine`, whose query transition is
a relation, rather than as a `DeterministicSpec`, whose `query` field would
have to invent an answer. -/

/-- The counter's net movement under one operation. A transfer moves rights
between replicas and leaves the value alone. -/
def specDelta : AppOp → Int
  | .increment a => (a : Int)
  | .decrement a => -(a : Int)
  | .transfer _ _ => 0

/-- `Spec` as a history machine over the sequential alphabet. -/
def specMachine (K : Int) : HistoryMachine type.OType type.QType type.ValType where
  State := Int
  initial := 0
  transition z label w :=
    match label with
    | .update o => w = z + specDelta o
    | .query q answer =>
        w = z ∧ match q with
          | .value => answer = K + z
          | .localRights _ => True

/-- `Spec` as a history language. -/
def historySpec (K : Int) : Soundness.Spec type := (specMachine K).toSpec

/-! ## `Spec` at the event alphabet

The projected specification above cannot constrain `localRights`, because
its alphabet is `O_type` and a transfer's issuer is not part of its
operation. The framework's other criterion keeps the whole event, timestamp
and replica included, in the sequential alphabet, and at that alphabet the
rights query **is** specifiable exactly. This is the reading the paper's
artifact uses for this row, and `Certificate.lean` certifies the row against
both.

The escrow reading: an increment mints rights for its issuer, a decrement
consumes the issuer's, and a transfer moves rights from issuer to target
without touching the value. -/

/-- The specification's state: the counter's value and each replica's
rights. -/
structure Accounts where
  value : Int
  balance : Nat → Int

@[ext] theorem Accounts.ext {a b : Accounts} (hv : a.value = b.value)
    (hb : ∀ r, a.balance r = b.balance r) : a = b := by
  cases a; cases b
  simp only [Accounts.mk.injEq]
  exact ⟨hv, funext hb⟩

def initialAccounts (K : Int) : Accounts := ⟨K, fun _ => 0⟩

/-- The rights `e` hands to `r`. -/
def credit (r : Nat) (e : Op AppOp) : Int :=
  match e.op with
  | .increment a => if r = e.rep then (a : Int) else 0
  | .decrement _ => 0
  | .transfer a t => if r = t then (a : Int) else 0

/-- The rights `e` takes from `r`. Only an issuer ever spends. -/
def debit (r : Nat) (e : Op AppOp) : Int :=
  match e.op with
  | .increment _ => 0
  | .decrement a => if r = e.rep then (a : Int) else 0
  | .transfer a _ => if r = e.rep then (a : Int) else 0

def accountStep (s : Accounts) (e : Op AppOp) : Accounts :=
  ⟨s.value + specDelta e.op, fun r => s.balance r + credit r e - debit r e⟩

def accountQuery (s : Accounts) : type.QType → Int
  | .value => s.value
  | .localRights r => s.balance r

/-- The issuer is one of the `n` replicas, and a transfer names another of
them. -/
def ValidIssuer (n : Nat) (e : Op AppOp) : Prop :=
  e.rep < n ∧ ∀ a t, e.op = AppOp.transfer a t → t < n ∧ t ≠ e.rep

/-- The issuer can pay for what it spends. -/
def Affordable (s : Accounts) (e : Op AppOp) : Prop :=
  ∀ a : Nat, (e.op = AppOp.decrement a ∨ ∃ t, e.op = AppOp.transfer a t) →
    (a : Int) ≤ s.balance e.rep

/-- `Spec` as a history machine over the event alphabet. Both queries are
answered exactly, and the two side conditions say that the history is one a
correct implementation could have produced. -/
def eventMachine (n : Nat) (K : Int) :
    HistoryMachine (Op type.OType) type.QType type.ValType where
  State := Accounts
  initial := initialAccounts K
  transition s label t :=
    match label with
    | .update e => t = accountStep s e ∧ ValidIssuer n e ∧ Affordable s e
    | .query q answer => t = s ∧ answer = accountQuery s q

/-- `Spec` at the event alphabet, as a history language. -/
def eventSpec (n : Nat) (K : Int) :
    HistorySpec (Op type.OType) type.QType type.ValType :=
  (eventMachine n K).toSpec

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

end LeanProofs.NoSpecNonComm.Implementations.BoundedCounter
