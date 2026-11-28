import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec

/-!
# The multi-value register, grow-only carrier: the implementation tuple

The multi-value register of Appendix `app:dt-mvr`, recorded the way
`Sal/MRDTs/Instances/MVR.lean` does: **nothing is ever removed**. One store
remembers every write that has happened, a second remembers every identity
that has been superseded, and the query subtracts the two.

```
  Sigma = ((Nat × Nat) -> Bool) × (Nat -> Bool)      writes, graveyard
  sigma0 = (fun _ => false, fun _ => false)
  do((B,G), write i v O) = (B ∪ {(i,v)}, G ∪ O)
  merge(l,a,b)           = (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)   componentwise
  query(B,G)             = { v | ∃ i, B (i,v) ∧ ¬ G i }
```

Both components are grow-only, so **every pair of events commutes** and
`rc` is empty, which is what the appendix asks for.

## Two differences from the compact carrier

`Implementations/MVRegister/` holds the compact presentation, where a write
*filters* the superseded entries out of a single store. There the appendix's
own prose says no operation-only `rc` can work, and `Negative.lean` proves
it. Here nothing is filtered, so the obstruction does not arise.

The second difference is that the operation carries the identity it
allocates, rather than taking it from the event's timestamp. Definition 4
hands the specification `projectedUpdates`, which keeps only each event's
label, so the identity has to sit in the label for the specification to
allocate it. `issuance` requires it to equal the event's timestamp, so on
every certified execution this is the appendix's tuple. The RGA row takes
the same step for the same reason.

No proof appears in this file.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.MVRegisterHistorical

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- `O_type`: write a value under an identity, superseding the identities in
`overwrites`. -/
inductive AppOp where
  | write (id value : Nat) (overwrites : List Nat)
  deriving DecidableEq, Repr

/-- The identity a write allocates. -/
def newId : AppOp → Nat
  | .write i _ _ => i

/-- The value a write carries. -/
def writeValue : AppOp → Nat
  | .write _ v _ => v

/-- The identities a write supersedes. -/
def overwrites : AppOp → List Nat
  | .write _ _ O => O

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := Set Nat

/-- `Sigma`: the writes ever made, and the identities ever superseded. -/
abbrev St := ((Nat × Nat) → Bool) × (Nat → Bool)

/-- `do`: record this write, and record everything it supersedes. Neither
store ever loses an entry. -/
def step (s : St) (e : Op AppOp) : St :=
  (fun p => s.1 p || decide (p = (newId e.op, writeValue e.op)),
   fun n => s.2 n || decide (n ∈ overwrites e.op))

/-- `merge`: the three-way shape, componentwise. -/
def mergeState (l a b : St) : St :=
  (fun p => (l.1 p && (a.1 p && b.1 p)) || ((a.1 p && !l.1 p) || (b.1 p && !l.1 p)),
   fun n => (l.2 n && (a.2 n && b.2 n)) || ((a.2 n && !l.2 n) || (b.2 n && !l.2 n)))

/-- `query`: the values whose identity has not been superseded. -/
def readValues (s : St) : Set Nat := {v | ∃ i, s.1 (i, v) = true ∧ s.2 i = false}

/-- `rc` is empty: both stores are grow-only, so every pair of events
commutes and nothing needs ordering. -/
def rcOf : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
noncomputable def D : Impl type where
  Sigma := St
  decSigma := fun _ _ => Classical.propDecidable _
  sigma0 := (fun _ => false, fun _ => false)
  do_ := step
  merge := mergeState
  query s _ := readValues s
  rc := rcOf

/-! ## `Spec`

The independent specification of Appendix `app:dt-mvr`: a **compact** live
set of tagged writes, where a write drops the entries it names instead of
marking them. It is not the implementation — the implementation never
removes anything — and the content of clause 2 is that the grow-only query
agrees with this compact fold.

A history is admitted only when it is **legal**: identities are distinct, and
a write supersedes only identities already allocated. Targets need not still
be live, so two concurrent writes may supersede the same earlier write.
-/

/-- The specification's state: the live tagged writes, and every identity
ever allocated. -/
abbrev SpecState := Finset (Nat × Nat) × Finset Nat

/-- One step of the specification: drop what this write names, add itself. -/
def sstep (s : SpecState) (o : AppOp) : SpecState :=
  (insert (newId o, writeValue o) (s.1.filter (fun q => q.1 ∉ overwrites o)),
   insert (newId o) s.2)

/-- The specification as a machine over operations. -/
def specMachine : HistoryMachine type.OType type.QType type.ValType where
  State := SpecState
  initial := (∅, ∅)
  transition s label t :=
    match label with
    | .update o =>
        newId o ∉ s.2 ∧ (∀ n ∈ overwrites o, n ∈ s.2) ∧ t = sstep s o
    | .query _ answer => t = s ∧ answer = {v | ∃ u, (u, v) ∈ s.1}

/-- `Spec` as a language of histories. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- `i` has been written. -/
def born (s : St) (i : Nat) : Prop := ∃ v, s.1 (i, v) = true

/-- Issuance: the identity is the event's own timestamp, it is fresh, and
every superseded identity was already written. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun e s =>
    newId e.op = e.time ∧ ¬ born s (newId e.op)
      ∧ ∀ n ∈ overwrites e.op, born s n

end LeanProofs.NoSpecNonComm.Implementations.MVRegisterHistorical
