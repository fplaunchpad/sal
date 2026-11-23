import LeanProofs.Interface.Implementation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic

/-!
# The remove-wins set: its implementation tuple

The Remove-wins set row of Table 1, Appendix `app:dt-remove-wins-set`.

This is the OR-set read in the mirror. The state holds *removal* tags rather
than add records: a `remove` inserts its own tag and an `add` erases every tag
for its element, so a concurrent `remove` wins. `rc` is reversed with it:
`add x` is ordered before `remove x`.

Two things make it more than a relabelling of the OR-set.

* Every element starts removed. `sigma0` carries a tag `(x, 0)` for each `x`,
  so the carrier must be finite and the client view is a complement.
* Timestamp `0` is reserved for those initial tags. The implementation
  therefore carries an **issuance guard**, `G(e, s) <=> 0 < time(e)`: without
  it a minted `remove` could collide with an initial tag and the two sources
  of a record would be indistinguishable. This is the first row here whose
  `I` column in Table 1 is `Y`.
-/

namespace LeanProofs.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

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
the event that removed it. Timestamp `0` marks an initial tag. -/
abbrev St (A : Type) := Finset (A × Timestamp)

/-- `sigma0`: every element starts removed, under the reserved timestamp. -/
def sigma0 : St A := Finset.univ.image (fun x => (x, (0 : Timestamp)))

variable {A}

@[simp] theorem mem_sigma0 (p : A × Timestamp) : p ∈ sigma0 A ↔ p.2 = 0 := by
  simp only [sigma0, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, h⟩; exact (congrArg Prod.snd h).symm ▸ rfl
  · intro h; exact ⟨p.1, by rw [← h]⟩

/-- `do(sigma, t, r, o)`. A remove inserts its own tag; an add erases every
tag for its element, whatever removed it. -/
def step (S : St A) (e : Event A) : St A :=
  match e.op with
  | .remove x => insert (x, e.time) S
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

end LeanProofs.Implementations.RemoveWinsSet
