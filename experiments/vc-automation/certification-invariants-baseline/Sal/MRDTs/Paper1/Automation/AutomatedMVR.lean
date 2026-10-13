import Sal.MRDTs.Paper1.Automation.GenericCertifiedRecords
import Sal.MRDTs.Paper1.CertifiedMVRVCContract

/-! The author's interface consists of record projections and fixed finite
obligations. All history/issuance propagation and five-VC assembly is generic.
The existing semantic representation is definitionally the template's one. -/
namespace Sal.MRDTs.Paper1.Automation.AutomatedMVR
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Instances.MVRLive
open CertifiedQueueMVR.MVR.RawVC
open GenericCertifiedRecords
open Classical

/-- Concrete annotations plus automatically discharged finite obligations. -/
def model : Model D issuance (Nat × Nat) where
  carrier := id
  written := fun e => (e.1,Sal.MRDTs.Instances.MVR.writeValue e)
  tag := Prod.fst
  target := fun e n => n ∈ Sal.MRDTs.Instances.MVR.overwrites e
  carrier_injective := by simp [Function.Injective]
  empty := rfl
  written_tag := by simp
  update_cell := by intros; simp [D,update,Sal.MRDTs.Instances.MVR.clientStep]
  merge_cell := by intros; rfl
  issuer_cell := by
    intros
    simp_all [issuance,canIssue,Finset.ext_iff]


end Sal.MRDTs.Paper1.Automation.AutomatedMVR
