import Sal.MRDTs.Metatheory.ProductionLedger
import Sal.MRDTs.Metatheory.Countermodels.TaggedORSet
import Sal.MRDTs.Instances.QueueCertificates

/-! Negative type controls for the release gate. These check rejected
substitutions, not impossibility of ever proving Queue's intended contract. -/
namespace Sal.MRDTs.PublicCertificateGate

open Sal.MRDTs.Foundation
set_option autoImplicit false

noncomputable section

-- Positive control for every component-mismatch test below.
example : SequentialCorrectnessCertificate Instances.LWWRegister.D
    Instances.LWWRegister.issuance Instances.LWWRegister.rc
    Instances.LWWRegister.spec Instances.LWWRegister.stateRel :=
  Instances.LWWRegister.verified.sequentialCorrectness

-- Positive control: the replay-only declaration exists and has its advertised type.
example : ReplayAdequateMRDT Instances.Queue.Q := Instances.Queue.replayAdequate

-- The completed public package is accepted, but its older replay-only
-- companion must still be rejected in the same tests below.
example : VerifiedMRDT Instances.Queue.Q := Instances.Queue.verified
example : VerifiedMRDT Instances.MVR.MVR := Instances.MVR.verified
example : VerifiedMRDT (Instances.EfficientORSet.D Nat) := Instances.EfficientORSet.verified

-- A certificate for the tagged/tombstone representation cannot certify
-- the compact per-replica implementation.
example : True := by
  fail_if_success
    have bad : VerifiedMRDT (Instances.EfficientORSet.D Nat) := Instances.ORSet.verified
  trivial

example : True := by
  fail_if_success
    have bad : VerifiedMRDT Instances.MVR.MVR := Instances.MVR.replayAdequate
  trivial

example : True := by
  fail_if_success
    have bad : VerifiedMRDT Instances.Queue.Q := Instances.Queue.replayAdequate
  trivial

example : True := by
  fail_if_success
    have bad := PackagedMRDT.of "queue" Instances.Queue.replayAdequate
  trivial

-- A public certificate for another implementation is not interchangeable.
example : True := by
  fail_if_success
    have bad : VerifiedMRDT Instances.Queue.Q := Instances.RGA.verified
  trivial

-- Even a genuine public certificate must use the selected semantic rc.
def wrongRc : ReplayPolicy Instances.LWWRegister.D.toUpdateSig :=
  ReplayPolicy.unconstrained Instances.LWWRegister.D.toUpdateSig

example : True := by
  fail_if_success
    have bad : SequentialCorrectnessCertificate Instances.LWWRegister.D
        Instances.LWWRegister.issuance
        wrongRc
        Instances.LWWRegister.spec Instances.LWWRegister.stateRel :=
      Instances.LWWRegister.verified.sequentialCorrectness
  trivial

-- Changing only the public observations also invalidates the connection.
def wrongObservations : SequentialSpec Instances.LWWRegister.D :=
  { Instances.LWWRegister.spec with query := fun _ _ => none }

example : True := by
  fail_if_success
    have bad : SequentialCorrectnessCertificate Instances.LWWRegister.D
        Instances.LWWRegister.issuance Instances.LWWRegister.rc
        wrongObservations Instances.LWWRegister.stateRel :=
      Instances.LWWRegister.verified.sequentialCorrectness
  trivial

def wrongIssuance : Issuance Instances.LWWRegister.D where
  CanIssue := fun _ _ => False

example : True := by
  fail_if_success
    have bad : SequentialCorrectnessCertificate Instances.LWWRegister.D
        wrongIssuance Instances.LWWRegister.rc
        Instances.LWWRegister.spec Instances.LWWRegister.stateRel :=
      Instances.LWWRegister.verified.sequentialCorrectness
  trivial

def wrongLegality : SequentialSpec Instances.LWWRegister.D :=
  { Instances.LWWRegister.spec with Legal := fun _ => False }

example : True := by
  fail_if_success
    have bad : SequentialCorrectnessCertificate Instances.LWWRegister.D
        Instances.LWWRegister.issuance Instances.LWWRegister.rc
        wrongLegality Instances.LWWRegister.stateRel :=
      Instances.LWWRegister.verified.sequentialCorrectness
  trivial

end
end Sal.MRDTs.PublicCertificateGate
