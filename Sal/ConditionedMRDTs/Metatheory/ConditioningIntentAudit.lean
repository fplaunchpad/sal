import Sal.ConditionedMRDTs.MRDT_Instances.VerifiedCertificates
import Sal.ConditionedMRDTs.Metatheory.GenerationContract

/-!
# Conditioning-to-intent audit

This file tests whether EmbedRGA's current issuer guard implies the sequential
discipline consumed by `embed_seq_sound`. It does not: the operational model
requires timestamps to be globally fresh, while `eSeqOK` requires a Lamport
maximum that exceeds every earlier insertion timestamp. `eApplicable` sees
only the datatype state and does not enforce that maximum.

The counterexample is a single-replica history. Both root insertions pass the
issuer guard at their minting states, and their timestamps are distinct, but
the second timestamp is smaller than the first. Consequently, this is not a
concurrency/global-linearization issue.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (binaryCode)

def intentAuditHigh : Op (EOp Nat) := (10, 0, .ins 1 [] 0)
def intentAuditLow : Op (EOp Nat) := (5, 0, .ins 2 [] 0)

/-- PASS: the first root insertion satisfies the production issuer guard. -/
example : eApplicable intentAuditHigh (E binaryCode Nat).init := by
  simp [intentAuditHigh, eApplicable, E]

/-- PASS: the lower, globally fresh timestamp also satisfies the current
issuer guard after the first insertion. -/
example : eApplicable intentAuditLow
    (applySeq (E binaryCode Nat).toCRDTSig (E binaryCode Nat).init
      [intentAuditHigh]) := by
  simp [intentAuditLow, intentAuditHigh, eApplicable, applySeq, E, eUpdate]

/-- FAIL control for the desired bridge: two locally applicable mints need not
satisfy the sequential theorem's Lamport-maximum premise. -/
theorem applicable_mints_do_not_imply_eSeqOK :
    ¬ eSeqOK binaryCode [intentAuditHigh, intentAuditLow] := by
  intro h
  have hlow := h [intentAuditHigh] intentAuditLow [] (by simp)
  have hten : 10 ∈ eInsIds [intentAuditHigh] := by
    simp [intentAuditHigh, eInsIds, eIsIns]
  have hbad : 10 < 5 := by
    simpa [intentAuditLow] using hlow.1 10 hten
  omega

/-- The repaired sequential bridge for EmbedRGA. The state guard supplies
anchor/path accuracy; the explicit local-clock premise supplies the stronger
timestamp condition that `embed_seq_sound` actually consumes. -/
theorem eSeqOK_of_linearMintHistory {α : Type} [DecidableEq α] [Inhabited α]
    {Γ : Sal.EmbedRGA.OrderedPrefixCode} {ops : List (Op (EOp α))}
    (h : LinearMintHistory (E Γ α) eApplicable ops) : eSeqOK Γ ops := by
  intro pre e post heq
  refine ⟨?_, h.guarded pre e post heq⟩
  intro x hx
  obtain ⟨old, hold, _hins, htime⟩ := mem_eInsIds.mp hx
  rw [← htime]
  exact h.clocked pre e post heq old hold

/-- The same operational bridge for SidedEmbedRGA. Side selection remains a
separate generation policy; clock and applicability are the sequential intent
premises shared with EmbedRGA. -/
theorem sSeqOK_of_linearMintHistory
    {Γ : Sal.EmbedRGA.OrderedPrefixCode} {ops : List (Op SOp)}
    (h : LinearMintHistory (S Γ) sApplicable ops) : sSeqOK Γ ops := by
  intro pre e post heq
  refine ⟨?_, h.guarded pre e post heq⟩
  intro x hx
  obtain ⟨old, hold, _hins, htime⟩ := mem_sInsIds.mp hx
  rw [← htime]
  exact h.clocked pre e post heq old hold

theorem embedSequentialSound_of_linearMintHistory
    {α : Type} [DecidableEq α] [Inhabited α]
    {Γ : Sal.EmbedRGA.OrderedPrefixCode} {ops : List (Op (EOp α))}
    (h : LinearMintHistory (E Γ α) eApplicable ops) :
    (eFold Γ ops).map eProj = eSpecFold ops :=
  embed_seq_sound (eSeqOK_of_linearMintHistory h)

theorem sidedSequentialSound_of_linearMintHistory
    {Γ : Sal.EmbedRGA.OrderedPrefixCode} {ops : List (Op SOp)}
    (h : LinearMintHistory (S Γ) sApplicable ops) :
    (sRFold Γ ops).map sProj = sSpecFold ops :=
  sided_seq_sound (sSeqOK_of_linearMintHistory h)

#print axioms applicable_mints_do_not_imply_eSeqOK
#print axioms eSeqOK_of_linearMintHistory
#print axioms sSeqOK_of_linearMintHistory
#print axioms embedSequentialSound_of_linearMintHistory
#print axioms sidedSequentialSound_of_linearMintHistory

end Sal.ConditionedMRDTs
