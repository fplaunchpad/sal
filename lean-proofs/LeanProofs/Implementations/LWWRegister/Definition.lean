import LeanProofs.Interface.Implementation
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex

/-!
# The last-writer-wins register: its implementation tuple

`D_type = < Sigma, sigma0, do, merge, query, rc >` for the LWW register row
of Table 1, following Appendix `app:dt-lww-register`.

* **State** unset `bot`, or a write key `(t, r, v)` ordered lexicographically
  with `bot` least. **Initial** `bot`.
* **Payload** `write(v)`.
* **Update** `e(S) = max(S, (t,r,v))`.
* **Merge** `merge(l,a,b) = max(a,b)`; the base `l` is ignored.
* **Query** `none` when unset, otherwise `some v`.
* **rc** empty.

The timestamp leads the key; replica and value are deterministic tie
breakers that matter only at states with repeated timestamps, which a
reachable configuration never has. Carrying them keeps `max` well defined at
every state, which is what the obligations quantify over.
-/

namespace LeanProofs.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- `O_type`. -/
inductive LWWOp where
  | write (value : Nat)
  deriving DecidableEq, Repr

/-- A write key `(t, r, v)`, ordered lexicographically. -/
abbrev Write := Lex (Nat × Lex (Nat × Nat))

/-- `Sigma`: `bot` is the unset register. -/
abbrev St := WithBot Write

def valueOf (e : Op LWWOp) : Nat :=
  match e.op with
  | .write v => v

/-- The key an event writes. -/
def packed (e : Op LWWOp) : Write :=
  toLex (e.time, toLex (e.rep, valueOf e))

def writeValue (w : Write) : Nat := (ofLex (ofLex w).2).2

@[simp] theorem writeValue_packed (e : Op LWWOp) :
    writeValue (packed e) = valueOf e := by
  rcases e with ⟨t, r, o⟩; cases o; rfl

/-- `query`. -/
def readOf : St → Option Nat
  | ⊥ => none
  | (w : Write) => some (writeValue w)

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := LWWOp
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

end LeanProofs.Implementations.LWWRegister
