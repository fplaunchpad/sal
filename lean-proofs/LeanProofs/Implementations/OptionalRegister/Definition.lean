import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex

/-!
# The optional register: the implementation and the specification

**A duplicate.** This folder is a standalone copy of the row, kept so the
specification-visibility variant can be read and diffed on its own. This
file is `Implementations/OptionalRegister/Definition.lean` with the
namespace changed and nothing else.

The Optional register row of Table 1, Appendix `app:dt-optional-register`.
A register whose payload may be absent. The active payload is the one with
the greatest `(timestamp, replica)` key.

`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3.
The state is a finite map from replicas to cells. A cell carries a counter
and a flag, which is the enable-wins core, together with the payload that
replica last wrote.

* **Update** `set v` bumps the issuer's counter, raises its flag and stores
  `(time, v)`. `unset` clears every flag and payload, leaving the counters.
* **Merge** is cellwise. The flag is the enable-wins merge on the counter;
  the payload follows the surviving flag, and on a tie it takes the write
  with the greater timestamp.
* **Query** returns the payload of the greatest `(timestamp, replica)` key
  among the cells whose flag is raised, or `none`.
* **rc** orders `unset` before `set v`, and nothing else.

`issuance` is the guard `G(e, s) <=> 0 < time(e)`. Timestamp `0` is what an
untouched cell's payload carries, so a `set` minted at `0` would be
indistinguishable from an absent one.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.OptionalRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- `O_type`: write a value, or clear the register. -/
inductive Action where
  | set (value : Nat)
  | unset
  deriving DecidableEq, Repr

/-- The payload a cell remembers: the timestamp of the write and its value. -/
abbrev Payload := Nat × Nat

/-- A cell: the enable-wins counter and flag, beside the payload. -/
abbrev Cell := (Int × Bool) × Payload

/-- The cell of a replica that has done nothing. -/
def zero : Cell := ((0, false), (0, 0))

/-- `Sigma`: a finite partial map from replicas to cells, normalised so that
a replica outside the domain reads as `zero`. -/
structure State where
  domain : Finset Nat
  cells : Nat → Cell
  outside : ∀ r, r ∉ domain → cells r = zero

@[ext] theorem State.ext {s t : State} (domain : s.domain = t.domain)
    (cells : ∀ r, s.cells r = t.cells r) : s = t := by
  cases s; cases t
  simp_all only
  congr
  funext r; exact cells r

/-- `sigma0`: every replica untouched. -/
def initial : State := ⟨∅, fun _ => zero, by simp⟩

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := Action
  decOType := inferInstance
  QType := Unit
  ValType := Option Nat

/-- `do`. `set v` touches only the issuer's cell; `unset` clears every flag
and payload and leaves every counter alone. -/
def step (s : State) (e : Op Action) : State := match e.op with
  | .set v => ⟨insert e.rep s.domain,
      fun r => if r = e.rep then (((s.cells r).1.1 + 1, true), (e.time, v)) else s.cells r,
      by intro r h
         have absent : r ≠ e.rep ∧ r ∉ s.domain := by simpa using h
         simp [absent.1, s.outside r absent.2]⟩
  | .unset => ⟨s.domain, fun r => (((s.cells r).1.1, false), (0, 0)),
      by intro r h; simp [s.outside r h, zero]⟩

/-- The enable-wins flag merge, on the counters. -/
def mergeFlag (l a b : Int × Bool) : Bool :=
  if a.2 && b.2 then true
  else if !a.2 && !b.2 then false
  else if a.2 then decide (a.1 > l.1)
  else decide (b.1 > l.1)

/-- Two live payloads merge to the one with the greater timestamp. -/
def mergePayload (_l a b : Payload) : Payload :=
  if a.1 = b.1 then (a.1, (a.2 + b.2) / 2)
  else if a.1 > b.1 then a else b

/-- Cellwise merge: the flag by `mergeFlag`, the payload following it. -/
def mergeCell (l a b : Cell) : Cell :=
  let flag := mergeFlag l.1 a.1 b.1
  let payload := if !flag then (0, 0)
    else if !a.1.2 then b.2
    else if !b.1.2 then a.2
    else mergePayload l.2 a.2 b.2
  ((a.1.1 + b.1.1 - l.1.1, flag), payload)

@[simp] theorem mergeCell_zero : mergeCell zero zero zero = zero := rfl

/-- `merge`, cellwise. -/
def mergeState (l a b : State) : State :=
  ⟨l.domain ∪ (a.domain ∪ b.domain),
    fun r => mergeCell (l.cells r) (a.cells r) (b.cells r),
    by intro r h
       have absent : r ∉ l.domain ∧ r ∉ a.domain ∧ r ∉ b.domain := by simpa using h
       change mergeCell (l.cells r) (a.cells r) (b.cells r) = zero
       rw [l.outside r absent.1, a.outside r absent.2.1, b.outside r absent.2.2,
         mergeCell_zero]⟩

/-- A candidate write, keyed lexicographically by timestamp, then replica. -/
abbrev Write := Lex (Nat × Lex (Nat × Nat))

/-- The writes of the cells whose flag is raised. -/
def candidates (s : State) : Finset Write :=
  (s.domain.filter (fun r => (s.cells r).1.2)).image
    (fun r => toLex ((s.cells r).2.1, toLex (r, (s.cells r).2.2)))

/-- The greatest candidate, if there is one. -/
def winner (s : State) : Option Write :=
  if h : (candidates s).Nonempty then some ((candidates s).max' h) else none

/-- `query`: the value of the winning write. -/
def readValue (s : State) : Option Nat := (winner s).map (fun c => (ofLex (ofLex c).2).2)

/-- `rc`: an `unset` is ordered before a `set`, and nothing else is ordered. -/
def rcOf : Action → Action → OrderResult
  | .unset, .set _ => .Fst_then_snd
  | .set _, .unset => .Snd_then_fst
  | _, _ => .Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
noncomputable def D : Impl type where
  Sigma := State
  decSigma := fun _ _ => Classical.propDecidable _
  sigma0 := initial
  do_ := step
  merge := mergeState
  query := fun s _ => readValue s
  rc := rcOf

/-! ## `Spec`

The sequential specification is an ordinary register: `set v` makes the
value `v`, `unset` makes it absent, and a query reads it off. It is
order-sensitive, which is why this row's clause 2 is the execution-scoped
one: the implementation answers with the greatest-timestamp write, and only
a timestamp-sorted history explains that. -/

/-- The specification as a deterministic machine. -/
def specMachine : DeterministicSpec type.OType type.QType type.ValType where
  State := Option Nat
  initial := none
  update _ o := match o with
    | .set v => some v
    | .unset => none
  query s _ := s

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, s) <=> 0 < time(e)`. Timestamp `0` is what an untouched
cell's payload carries, so a `set` minted at `0` could not be told from a
cell no one has written. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun e _ => 0 < e.time

end LeanProofs.NoSpecNonComm.Implementations.OptionalRegister
