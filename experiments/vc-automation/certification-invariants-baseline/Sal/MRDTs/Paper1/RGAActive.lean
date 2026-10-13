import Sal.MRDTs.Paper1.RGA
import Sal.MRDTs.Paper1.RALinearizability

/-!
# Current RGA under the manuscript's active criterion

Every concrete grow-only RGA update commutes. Exact concrete noncommutation
therefore forces an empty application-level resolver, and the active paper order
is empty. Honest issuance and causal closure still matter to the independent
allocating-list proof: they provide valid earlier anchors and unique identifiers.

The admitted language permits missing-anchor insertions as no-ops. Identifier
allocation is nondeterministic because the current application insertion label
contains no identifier. These are explicit semantic choices, not metadata passed
to the specification. `RGAStrict` investigates the stronger live-anchor language.
-/
namespace Sal.MRDTs.Paper1.RGA
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RGA

def emptyPolicy : OperationPolicy RGAOp where
  before := fun _ _ => False

theorem restrictedLaws : RestrictedLaws RGAM.toUpdateSig emptyPolicy := by
  constructor
  · intro a b
    simp [emptyPolicy, RGAM_all_comm a b]
  · intro a b c h
    exact h.1
  · intro s a b c between h
    exact h.elim

/-- Exact noncommutation admits no alternative nonempty operation policy. -/
theorem policy_must_be_empty (P : OperationPolicy RGAOp)
    (laws : RestrictedLaws RGAM.toUpdateSig P) (a b : RGAOp) :
    ¬ P.before a b := by
  intro h
  have hnc := (laws.noncomm_exact (0, 0, a) (0, 0, b)).mpr (Or.inl h)
  exact hnc (RGAM_all_comm _ _)

theorem paperOrder_empty (C : ReplayContext RGAM.toUpdateSig)
    (E : Set (Op RGAOp)) (a b : Op RGAOp) :
    ¬ paperOrder emptyPolicy C E a b := by
  simp [paperOrder, emptyPolicy, RGAM_all_comm a b]

/-- All stored versions have witnesses accepted after actual metadata stripping. -/
theorem versions_of_execution {C : Configuration RGAM}
    (exec : CertifiedExecution RGAM generation C) :
    VersionsRALinearizable RGAM emptyPolicy listHistorySpec C := by
  have replay : HasReplayWitness C := by
    cases exec with
    | ordinary reach => exact replayAdequacy.sound reach
    | virtual reach => exact replayAdequacy.soundV reach
  intro v s E hver q
  cases q
  obtain ⟨ops, hperm, _, hfold⟩ := replay v s E hver
  refine ⟨canonical ops, canonical_listPermOf hperm, ?_, ?_⟩
  · exact (canonical_ordered ops).imp (fun {_ _} _ => paperOrder_empty _ _ _ _)
  · exact admitted_of_execution exec hver hperm hfold

/-- Ordinary certified execution meets the active criterion at every head. -/
theorem certifiedRA : CertifiedRA RGAM emptyPolicy listHistorySpec generation := by
  intro C reach
  exact (versions_of_execution (.ordinary reach)).heads

/-- The same admitted-language bridge covers widened virtual-base execution. -/
theorem certifiedRAV : CertifiedRAV RGAM emptyPolicy listHistorySpec generation := by
  intro C reach
  exact (versions_of_execution (.virtual reach)).heads

#print axioms restrictedLaws
#print axioms policy_must_be_empty
#print axioms certifiedRA
#print axioms certifiedRAV
end Sal.MRDTs.Paper1.RGA
