import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec

/-!
# The remove-wins set: the implementation and the specification

The two definitions the obligations are stated about, and nothing else.
`D_type = < Sigma, sigma0, do, merge, query, rc >` is the tuple of Section 3;
`historySpec` is the `Spec` of Section 4, as a language of histories.
`issuance` is the guard `G` of Section 3, which this row does not use.

No proof appears in this file. Every obligation is in `VCs.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- `O_type`: add and remove an element. -/
inductive AppOp (A : Type) where
  | add (x : A)
  | remove (x : A)
  deriving DecidableEq, Repr

/-- An event: an operation with its timestamp and replica. -/
abbrev Event (A : Type) := Op (AppOp A)

variable (A : Type) [DecidableEq A] [Fintype A]

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp A
  decOType := inferInstance
  QType := A
  ValType := Bool

/-- `Sigma`: the removal tags, each an element paired with the timestamp of
the event that removed it, or with `none` for an initial tag.

The appendix reserves timestamp `0` for the initial tags and keeps real
events off it with an issuance guard. Carrying the seeds as `none` instead
makes them a different shape of tag rather than a reserved value of the same
shape, so no guard is needed and no event can collide with a seed. -/
abbrev St (A : Type) := Finset (A × Option Timestamp)

/-- `sigma0`: every element starts removed, under the seed tag. -/
def sigma0 : St A := Finset.univ.image (fun x => (x, (none : Option Timestamp)))

variable {A}

@[simp] theorem mem_sigma0 (p : A × Option Timestamp) :
    p ∈ sigma0 A ↔ p.2 = none := by
  simp only [sigma0, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, h⟩; exact (congrArg Prod.snd h).symm ▸ rfl
  · intro h; exact ⟨p.1, by rw [← h]⟩

/-- `do(sigma, t, r, o)`. A remove inserts its own tag; an add erases every
tag for its element, whatever removed it. -/
def step (S : St A) (e : Event A) : St A :=
  match e.op with
  | .remove x => insert (x, some e.time) S
  | .add x => S.filter (fun p => p.1 ≠ x)

/-- `merge(l,a,b)`, the same three-way shape as the OR-set. -/
def mergeState (l a b : St A) : St A := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- The elements the client sees: those with no surviving removal tag. -/
def view (S : St A) : Finset A := Finset.univ \ S.image Prod.fst

/-- `rc`: `add x` is ordered before `remove x`, the mirror of the OR-set. -/
def rc : AppOp A → AppOp A → OrderResult
  | .add x, .remove y => if x = y then OrderResult.Fst_then_snd else OrderResult.Either
  | .remove x, .add y => if x = y then OrderResult.Snd_then_fst else OrderResult.Either
  | _, _ => OrderResult.Either

variable (A)

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`. -/
@[reducible] def D : Impl (type A) where
  Sigma := St A
  decSigma := inferInstance
  sigma0 := sigma0 A
  do_ := step
  merge := mergeState
  query S x := decide (x ∈ view S)
  rc := rc


/-! ## `Spec` -/

/-- `Spec`: an ordinary set, empty at the start, with no timestamps
anywhere. -/
def specMachine : DeterministicSpec (type A).OType (type A).QType (type A).ValType where
  State := Finset A
  initial := ∅
  update S o := match o with
    | .add x => insert x S
    | .remove x => S.erase x
  query S x := decide (x ∈ S)

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec (type A) := (specMachine A).toSpec

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. The seeds of `sigma0` carry `none`, which
no event's tag can equal, so this row needs no guard. -/
def issuance (A : Type) [DecidableEq A] [Fintype A] : Issuance (D A).toMRDTSig where
  CanIssue := fun _ _ => True

end LeanProofs.NoSpecNonComm.Implementations.RemoveWinsSet
