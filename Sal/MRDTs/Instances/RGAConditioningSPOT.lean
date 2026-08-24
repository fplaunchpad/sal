import Sal.MRDTs.Instances.RGASequential

/-!
# RGA issuance and sequential-legality proof-oriented tests

These tests determine which part of the existing RGA issuer guard can serve
as sequential applicability.  They use the production tombstone RGA, not the
refuted rehoming design from the archived branch.
-/

namespace Sal.MRDTs.Instances.RGA.ConditioningSPOT

open Sal.MRDTs.Foundation

/-- Counterfactual legacy interpretation: replay every operation through the
implementation and require the origin issuance predicate at each prefix. -/
def strictLegalFrom : RGAM.State → List (Op RGAOp) → Prop
  | _, [] => True
  | s, e :: rest => applicable e s ∧ strictLegalFrom (RGAM.update s e) rest

def strictLegal (ops : List (Op RGAOp)) : Prop :=
  strictLegalFrom RGAM.init ops

def insertOne : Op RGAOp := (1, 0, .addAfter 0 1)
def deleteA : Op RGAOp := (2, 1, .remove 1)
def deleteB : Op RGAOp := (3, 2, .remove 1)

/-- PASS: each concurrent delete is authorized at an origin containing the
same live element. -/
example : applicable deleteA
    (applySeq RGAM.toCRDTSig RGAM.init [insertOne]) := by
  simp [applicable, deleteA, insertOne, applySeq, RGAM, rgaUpdate]

example : applicable deleteB
    (applySeq RGAM.toCRDTSig RGAM.init [insertOne]) := by
  simp [applicable, deleteB, insertOne, applySeq, RGAM, rgaUpdate]

def duplicateDeleteOrders : List (List (Op RGAOp)) :=
  [[insertOne, deleteA, deleteB], [insertOne, deleteB, deleteA],
   [deleteA, insertOne, deleteB], [deleteA, deleteB, insertOne],
   [deleteB, insertOne, deleteA], [deleteB, deleteA, insertOne]]

/-- FAIL: no serialization of both authorized deletes satisfies the strict
minting guard at every sequential prefix.  A public theorem must therefore
use a sequential delete semantics that is idempotent, or exclude duplicate
deletes with an explicit generation protocol. -/
theorem strict_guard_has_no_duplicate_delete_serialization :
    ∀ π ∈ duplicateDeleteOrders, ¬ strictLegal π := by
  simp [duplicateDeleteOrders, strictLegal, strictLegalFrom,
    applicable, deleteA, deleteB,
    insertOne, RGAM, rgaUpdate]

/-- PASS: idempotent sequential deletion admits the merged history while the
strict origin guard above does not. -/
example : listSpec.Legal
    [insertOne, deleteA, deleteB] := by
  let ops := [insertOne, deleteA, deleteB]
  let E : Set (Op RGAOp) := {e | e ∈ ops}
  have hp : listPermOf ops E := by
    constructor
    · native_decide
    · intro e
      rfl
  have hwf : VersionWellFormed E := by
    constructor
    · intro a b ha hb ht
      simp [E, ops, insertOne, deleteA, deleteB] at ha hb
      rcases ha with rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl <;> simp_all
    · intro ts replica anchor id he
      simp [E, ops, insertOne, deleteA, deleteB] at he
      rcases he with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, Or.inl rfl⟩
    · intro ts replica id he
      simp [E, ops, insertOne, deleteA, deleteB] at he
      rcases he with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
        exact ⟨1, 0, 0, by
          simp [E, ops, insertOne, deleteA, deleteB]⟩
  have hc : canonical ops = ops := by native_decide
  change listSpec.Legal ops
  rw [← hc]
  exact canonical_legal hp hwf

/-- The tombstone RGA still remembers a deleted anchor.  Unlike the archived
root-free rehoming RGA, its guard accepts a later replayed child insertion
after that anchor's delete. -/
def insertChild : Op RGAOp := (4, 2, .addAfter 1 4)

example : applicable insertChild
    (applySeq RGAM.toCRDTSig RGAM.init [insertOne, deleteA]) := by
  simp [applicable, insertChild, deleteA, insertOne, applySeq, RGAM, rgaUpdate]

end Sal.MRDTs.Instances.RGA.ConditioningSPOT
