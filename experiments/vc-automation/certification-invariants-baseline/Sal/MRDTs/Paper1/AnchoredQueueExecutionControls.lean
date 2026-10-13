import Sal.MRDTs.Paper1.AnchoredQueueControls
import Sal.MRDTs.Paper1.CertifiedRGARawOrderObstruction

/-! Recheck a concrete store trace with the stronger queue issuer, rather than
infer queue honesty from the weaker sequence certificate. Its left branch
removes the singleton anchor and resets its tail; its right branch uses the
still-observed singleton tail. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.ExecutionControls
open Foundation


abbrev config := CertifiedRGARawOrderObstruction.config

theorem issuer_guard (i : CertifiedRGARawOrderObstruction.I) : CanIssue (CertifiedRGARawOrderObstruction.event i) (CertifiedRGARawOrderObstruction.records (CertifiedRGARawOrderObstruction.issuer i)).1 := by
  fin_cases i <;> decide +kernel

theorem mint_honest (k : CertifiedRGARawOrderObstruction.V) : MintHonest Q CanIssue (config k) := by
  intro e he
  obtain ⟨i,rfl,hi⟩ := CertifiedRGARawOrderObstruction.event_supported_issued he
  refine ⟨CertifiedRGARawOrderObstruction.pastOps i,CertifiedRGARawOrderObstruction.past_enum k i hi,by
    change respects (CertifiedRGARawOrderObstruction.pastOps i) (CertifiedRGARawOrderObstruction.vis k)
    unfold respects
    fin_cases k <;> fin_cases i <;> decide +kernel,?_⟩
  rw [CertifiedRGARawOrderObstruction.past_fold_issuer]
  exact issuer_guard i

theorem issued_apply (i : CertifiedRGARawOrderObstruction.I) :
    IssuedStep Q issuance (config (CertifiedRGARawOrderObstruction.before i))
      (.apply (CertifiedRGARawOrderObstruction.event i).time (CertifiedRGARawOrderObstruction.event i).rep (CertifiedRGARawOrderObstruction.event i).op)
      (config (CertifiedRGARawOrderObstruction.newVersion i)) := by
  apply IssuedStep.apply (v := (CertifiedRGARawOrderObstruction.issuer i).val) (s := (CertifiedRGARawOrderObstruction.records (CertifiedRGARawOrderObstruction.issuer i)).1)
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · exact issuer_guard i
  · exact CertifiedRGARawOrderObstruction.apply_step i

theorem certified : MintCertifiedReach Q issuance (config 6) := by
  have h0 : MintCertifiedReach Q issuance (config 0) := by
    change MintCertifiedReach Q issuance (CertifiedRGARawOrderObstruction.config 0)
    rw [CertifiedRGARawOrderObstruction.config_zero]
    exact .init
  have h1 := MintCertifiedReach.step h0 (mint_honest 0) (issued_apply 0) (mint_honest 1)
  have h2 := MintCertifiedReach.step h1 (mint_honest 1)
    (IssuedStep.nonApply CertifiedRGARawOrderObstruction.fork_step (by intro t r o h; cases h)) (mint_honest 2)
  have h3 := MintCertifiedReach.step h2 (mint_honest 2) (issued_apply 1) (mint_honest 3)
  have h4 := MintCertifiedReach.step h3 (mint_honest 3) (issued_apply 2) (mint_honest 4)
  have h5 := MintCertifiedReach.step h4 (mint_honest 4) (issued_apply 3) (mint_honest 5)
  exact .step h5 (mint_honest 5)
    (IssuedStep.nonApply CertifiedRGARawOrderObstruction.merge_step (by intro t r o h; cases h)) (mint_honest 6)

/-- The ordinary trace is also genuinely certified in widened execution,
which includes its base fragment. This control itself uses a unique GCA. -/
theorem certifiedV :
    MintCertifiedReachV Q (canonicalVirtualMergeBase Q) issuance (config 6) := certified.toV

/-- Full representation closure and recursive virtual-base validity hold at
this actual queue-certified store, independently of the FIFO history bridge. -/
theorem certified_representation_control :
    MintCertifiedReach Q issuance (config 6) ∧
    Valid (config 6) (CertifiedRGARawOrderObstruction.records 6).1 ∧
    headQuery (CertifiedRGARawOrderObstruction.records 6).1 () = some (3,30) ∧
    headQuery (CertifiedRGARawOrderObstruction.records 6).1 () ≠ some (4,40) ∧
    Q.query (CertifiedRGARawOrderObstruction.records 6).1 () = [30,40] := by
  refine ⟨certified,?_,by decide +kernel,by decide +kernel,CertifiedRGARawOrderObstruction.final_read.1⟩
  apply stored_valid (.ordinary certified) (v := 6)
    (H := (↑((CertifiedRGARawOrderObstruction.indices 6).image CertifiedRGARawOrderObstruction.event) : Set Event))
  rfl

#print axioms certified
#print axioms certified_representation_control
end Sal.MRDTs.Paper1.AnchoredQueue.ExecutionControls
