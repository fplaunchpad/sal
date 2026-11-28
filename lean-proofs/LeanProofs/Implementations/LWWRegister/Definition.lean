import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec

/-!
# The LWW register: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3;
`historySpec` is the `Spec` of Section 4, as a language of histories.
`issuance` is the guard `G` of Section 3.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- `O_type`. -/
inductive AppOp where
  | write (value : Nat)
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event := Op AppOp

/-- A write key `(t, r, v)`, ordered lexicographically. -/
abbrev Write := Lex (Nat × Lex (Nat × Nat))

/-- `Sigma`: `bot` is the unset register. -/
abbrev St := WithBot Write

def valueOf (e : Event) : Nat :=
  match e.op with
  | .write v => v

/-- The key an event writes. -/
def packed (e : Event) : Write :=
  toLex (e.time, toLex (e.rep, valueOf e))

def writeValue (w : Write) : Nat := (ofLex (ofLex w).2).2

/-- `query`. -/
def readOf : St → Option Nat
  | ⊥ => none
  | (w : Write) => some (writeValue w)

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Option Nat

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

Reducible so that `D.Sigma` unfolds to `St` during instance search; the
obligations are `max` lemmas and need the `LinearOrder` instance. -/
@[reducible] noncomputable def D : Impl type where
  Sigma := St
  decSigma := fun a b => Classical.propDecidable (a = b)
  sigma0 := ⊥
  do_ s e := max s ↑(packed e)
  merge _ a b := max a b
  query s _ := readOf s
  rc _ _ := OrderResult.Either


/-! ## `Spec` -/

/-- `Spec`: an overwrite register. Timestamp and replica are ignored. -/
def specMachine : DeterministicSpec type.OType type.QType type.ValType where
  State := Option Nat
  initial := none
  update _ o := match o with | .write v => some v
  query s _ := s

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## The chronological witness -/

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.NoSpecNonComm.Implementations.LWWRegister
