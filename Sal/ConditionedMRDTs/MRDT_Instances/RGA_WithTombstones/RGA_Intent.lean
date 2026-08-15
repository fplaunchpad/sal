import Sal.ConditionedMRDTs.MRDT_Instances.RGA_WithTombstones.RGA_WithTombstones
import Sal.ConditionedMRDTs.Metatheory.UnifiedVerifiedMRDT

/-!
# Tombstone RGA: guarded generation and sequential intent

This module is deliberately independent of the refuted Shesha/rehoming line.
The abstract sequential state is a pair of finite sets.  Its client observation
is a deterministic sequence: insertions are considered in timestamp order,
inserted after their declared anchor, and tombstoned identifiers are filtered.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

abbrev RGAEntry := ℕ × ℕ × ℕ

structure RGASeqState where
  adds : Finset RGAEntry
  grave : Finset ℕ
deriving DecidableEq

private def insertAfter (anchor value : ℕ) : List ℕ → List ℕ
  | [] => if anchor = 0 then [value] else []
  | x :: tail =>
      if anchor = 0 then value :: x :: tail
      else if x = anchor then x :: value :: tail
      else x :: insertAfter anchor value tail

/-- The genuine list observation of an abstract tombstone-RGA state. -/
noncomputable def rgaSequence (q : RGASeqState) : List ℕ :=
  let ordered := q.adds.toList.mergeSort (fun a b => a.1 ≤ b.1)
  let inserted := ordered.foldl (fun xs e => insertAfter e.2.1 e.2.2 xs) []
  inserted.filter (fun id => id ∉ q.grave)

def rgaSequentialSpec : SequentialSpec (Op RGAOp) where
  State := RGASeqState
  init := ⟨∅, ∅⟩
  step q e := match e.2.2 with
    | .addAfter anchor id => ⟨insert (e.1, anchor, id) q.adds, q.grave⟩
    | .remove id => ⟨q.adds, insert id q.grave⟩

def rgaStateRel (s : RGAM.State) (q : RGASeqState) : Prop :=
  (∀ e, s.1 e = decide (e ∈ q.adds)) ∧
  (∀ id, s.2 id = decide (id ∈ q.grave))

/-- The issuer guard: anchors must already exist (except root `0`); insertion
timestamps and element identifiers are fresh; an inserted identifier was never
removed; and removal only targets a live, previously inserted identifier.
The anchor timestamp is required to precede the child timestamp, making the
timestamp-ordered sequence observation respect anchor closure. -/
def rgaApplicable (e : Op RGAOp) (s : RGAM.State) : Prop :=
  match e.2.2 with
  | .addAfter anchor id =>
      (anchor = 0 ∨ ∃ ts parent, ts < e.1 ∧ s.1 (ts, parent, anchor) = true) ∧
      (∀ anchor' id', s.1 (e.1, anchor', id') = false) ∧
      (∀ ts anchor', s.1 (ts, anchor', id) = false) ∧
      s.2 id = false
  | .remove id =>
      (∃ ts anchor, s.1 (ts, anchor, id) = true) ∧ s.2 id = false

/-- Every prefix was minted against the state produced by the preceding
prefix.  This is the exact single-replica history discipline. -/
inductive RGAHistoryOK : List (Op RGAOp) → Prop where
  | nil : RGAHistoryOK []
  | snoc {ops e} : RGAHistoryOK ops →
      rgaApplicable e (applySeq RGAM.toCRDTSig RGAM.init ops) →
      RGAHistoryOK (ops ++ [e])

theorem rgaSequentialSound (ops : List (Op RGAOp)) :
    rgaStateRel (applySeq RGAM.toCRDTSig RGAM.init ops)
      (rgaSequentialSpec.run ops) := by
  induction ops using List.reverseRecOn with
  | nil =>
      constructor <;> intro x <;>
        simp [applySeq, SequentialSpec.run, RGAM, rgaSequentialSpec]
  | append_singleton ops e ih =>
      rw [applySeq_append_single, SequentialSpec.run_append_single]
      rcases e with ⟨ts, replica, op⟩
      cases op with
      | addAfter anchor id =>
          constructor
          · intro p
            change ((applySeq RGAM.toCRDTSig RGAM.init ops).1 p ||
                decide (p = (ts, anchor, id))) =
              decide (p ∈ insert (ts, anchor, id)
                (rgaSequentialSpec.run ops).adds)
            rw [ih.1 p]
            simp [Bool.or_comm]
          · intro x
            simpa [rgaUpdate, rgaSequentialSpec] using ih.2 x
      | remove id =>
          constructor
          · intro p
            simpa [rgaUpdate, rgaSequentialSpec] using ih.1 p
          · intro x
            change ((applySeq RGAM.toCRDTSig RGAM.init ops).2 x ||
                decide (x = id)) =
              decide (x ∈ insert id (rgaSequentialSpec.run ops).grave)
            rw [ih.2 x]
            simp [eq_comm, Bool.or_comm]

def rgaHistorySequentialRefinement :
    HistorySequentialRefinement RGAM rgaSequentialSpec where
  Honest := RGAHistoryOK
  Rel := rgaStateRel
  init := by
    constructor <;> intro x <;> simp [RGAM, rgaSequentialSpec]
  sound := fun ops _ => rgaSequentialSound ops

def rgaGeneration : GenerationContract RGAM where
  Guard := rgaApplicable
  History := fun C => MintHonest RGAM rgaApplicable (Configuration.core C)
  history_of_mint := fun _ h => h

private theorem rgaJoin : JoinLemma3 RGAM :=
  join_lemma3_of_cd_feasible RGAM_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta RGAM_coreVCs3 RGAM_deltaVCs3)
    (cdVC3_of_all_comm RGAM_coreVCs3 RGAM_all_comm)

def rgaVerified : VerifiedMRDT RGAM where
  Honest := fun _ => True
  initInv := trivial
  join := fun C _ => (joinKitAt_plain_iff RGAM C).2 (rgaJoin C)
  Spec := rgaSequentialSpec
  seq := rgaHistorySequentialRefinement

def rgaUnified : UnifiedVerifiedMRDT RGAM where
  verified := rgaVerified
  generation := rgaGeneration
  history_entails_honest := fun _ _ => True.intro
  safety := SafetyCertificate.trivial rgaGeneration

/-! Kernel-checked PASS/FAIL controls. -/

def rgaPassAdd : Op RGAOp := (1, 0, .addAfter 0 7)
def rgaPassRemove : Op RGAOp := (2, 0, .remove 7)

example : rgaApplicable rgaPassAdd RGAM.init := by
  simp [rgaApplicable, rgaPassAdd, RGAM]
example : rgaSequence ⟨{(1, 0, 7)}, ∅⟩ = [7] := by
  simp [rgaSequence, insertAfter]
example : rgaSequence ⟨{(1, 0, 7)}, {7}⟩ = [] := by
  simp [rgaSequence, insertAfter]
example : RGAHistoryOK [rgaPassAdd, rgaPassRemove] := by
  change RGAHistoryOK ([] ++ [rgaPassAdd] ++ [rgaPassRemove])
  apply RGAHistoryOK.snoc
  · exact RGAHistoryOK.snoc .nil (by
      simp [rgaApplicable, rgaPassAdd, RGAM, applySeq])
  · simp [rgaApplicable, rgaPassAdd, rgaPassRemove, applySeq, RGAM, rgaUpdate]

/-- FAIL control: a missing anchor is rejected. -/
example : ¬ rgaApplicable (1, 0, .addAfter 42 7) RGAM.init := by
  simp [rgaApplicable, RGAM]

/-- FAIL control: removing an identifier before its insertion is rejected. -/
example : ¬ rgaApplicable (1, 0, .remove 7) RGAM.init := by
  simp [rgaApplicable, RGAM]

/-- FAIL control: timestamp reuse is rejected after the first insertion. -/
example : ¬ rgaApplicable (1, 0, .addAfter 0 8)
    (RGAM.update RGAM.init rgaPassAdd) := by
  simp [rgaApplicable, rgaPassAdd, RGAM, rgaUpdate]

#print axioms rgaSequentialSound
#print axioms rgaHistorySequentialRefinement
#print axioms rgaUnified

end Sal.ConditionedMRDTs
