import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec

/-!
# The disable-wins flag: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3;
`historySpec` is the `Spec` of Section 4, as a language of histories.
`issuance` is the guard `G` of Section 3.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.DisableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- `O_type`. The names are the ones the source algorithm uses; which of them
the client calls "enable" depends on the polarity. -/
inductive AppOp where
  | winning
  | reset
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event := Op AppOp

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Bool

/-- One replica's row: how many `winning` events it issued, and its bit. -/
abbrev Cell := Int × Bool

/-- `Sigma`: one row per replica. -/
abbrev St := Replica → Cell

/-- `do(sigma, t, r, o)`. -/
def step (s : St) (e : Event) : St :=
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
def rc : AppOp → AppOp → OrderResult
  | .reset, .winning => OrderResult.Fst_then_snd
  | .winning, .reset => OrderResult.Snd_then_fst
  | _, _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

`decSigma` is classical: equality of row functions is not decidable, and
`active` quantifies over every replica. -/
@[reducible] noncomputable def D : Impl type where
  Sigma := St
  decSigma := fun a b => Classical.propDecidable (a = b)
  sigma0 := fun _ => (0, true)
  do_ := step
  merge := mergeState
  query s _ := !active s
  rc := rc

/-- `disable` advances the issuer's disable counter; it is the winning
request for this polarity. -/
abbrev disable : AppOp := .winning

/-- `enable` clears every observed disable. -/
abbrev enable : AppOp := .reset


/-! ## `Spec` -/

/-- How one request moves the physical bit. -/
def flagStep (_ : Bool) (o : AppOp) : Bool :=
  match o with
  | .winning => true
  | .reset => false

/-- How one request moves the client Boolean. -/
def boolStep (invert : Bool) (_ : Bool) (o : AppOp) : Bool :=
  match o with
  | .reset => invert
  | .winning => !invert

/-- `Spec`: one Boolean, set by `winning` and cleared by `reset`, read
directly or negated according to `true`. -/
def specMachine :
    DeterministicSpec type.OType type.QType type.ValType where
  State := Bool
  initial := if true then !true else true
  update := boolStep true
  query b _ := b

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type :=
  specMachine.toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. The source algorithm puts no side condition
on the events a replica may mint. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.NoSpecNonComm.Implementations.DisableWinsFlag
