import LeanProofs.Interface.Implementation

/-!
# The enable-wins flag: its implementation tuple

The Enable-wins flag row of Table 1, Appendix `app:dt-enable-wins-flag`.

`enable` is the winning request, `disable` clears observed enables, and the
client reads the physical bit directly: `read(s) = [exists i. b_i = true]`.

`Sigma` is a per-replica counter and bit. A `winning` increments the issuer's
counter and sets its bit; a `reset` clears every bit and leaves the counters
alone. The counter is what tells `merge` whether a branch has a `winning` the
ancestor did not have, which is the role the record sets play in the OR-set.

`rc` is nonempty: `reset` is ordered before `winning`, so in a concurrent pair
the `winning` survives.
-/

namespace LeanProofs.Implementations.EnableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- `O_type`. The names are the ones the source algorithm uses; which of them
the client calls "enable" depends on the polarity. -/
inductive Act where
  | winning
  | reset
  deriving DecidableEq, Repr

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := Act
  decOType := inferInstance
  QType := Unit
  ValType := Bool

/-- One replica's row: how many `winning` events it issued, and its bit. -/
abbrev Cell := Int × Bool

/-- `Sigma`: one row per replica. -/
abbrev St := Replica → Cell

/-- `do(sigma, t, r, o)`. -/
def step (s : St) (e : Op Act) : St :=
  match e.op with
  | .winning => fun r => if r = e.rep then ((s r).1 + 1, true) else s r
  | .reset => fun r => ((s r).1, false)

/-- The bit of a merged row. Agreeing branches keep their bit; a branch that
disagrees wins exactly when its counter has grown since the ancestor, that is
when it holds a `winning` the ancestor did not. -/
def mergeFlag (l a b : Cell) : Bool :=
  if a.2 && b.2 then true
  else if !a.2 && !b.2 then false
  else if a.2 then decide (a.1 > l.1)
  else decide (b.1 > l.1)

/-- One merged row. The counter is the usual three-way sum. -/
def mergeCell (l a b : Cell) : Cell := (a.1 + b.1 - l.1, mergeFlag l a b)

/-- `merge(l,a,b)`, row by row. -/
def mergeState (l a b : St) : St := fun r => mergeCell (l r) (a r) (b r)

/-- The physical reading: some row has its bit set. -/
noncomputable def active (s : St) : Bool :=
  open Classical in decide (∃ r, (s r).2 = true)

/-- `rc`: `reset` before `winning`. -/
def rc : Act → Act → OrderResult
  | .reset, .winning => OrderResult.Fst_then_snd
  | .winning, .reset => OrderResult.Snd_then_fst
  | _, _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

`decSigma` is classical: equality of row functions is not decidable, and
`active` quantifies over every replica. -/
@[reducible] noncomputable def D : Impl type where
  Sigma := St
  decSigma := fun a b => Classical.propDecidable (a = b)
  sigma0 := fun _ => (0, false)
  do_ := step
  merge := mergeState
  query s _ := active s
  rc := rc

/-- `enable` sets the flag; it is the winning request. -/
abbrev enable : Act := .winning

/-- `disable` clears every observed enable. -/
abbrev disable : Act := .reset

end LeanProofs.Implementations.EnableWinsFlag
