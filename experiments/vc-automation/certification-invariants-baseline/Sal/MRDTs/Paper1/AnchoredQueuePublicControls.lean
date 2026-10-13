import Sal.MRDTs.Paper1.AnchoredQueuePublic
import Sal.MRDTs.Paper1.AnchoredQueueExecutionControls
import Sal.MRDTs.Paper1.AnchoredQueueCertificate

/-! Nonvacuity at the public tagged-head signature. The actual fork/apply/
merge trace is lifted with its original state and issuance guards; only query
labels are interpreted at the public observation. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.PublicControls
open Foundation

/-- The observation field does not alter an allocated version store. -/
def expose (C : Configuration Q) : Configuration publicQueue where
  vis := C.vis
  ver := C.ver
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := C.ver_init
  head_alloc := C.head_alloc
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  gca_events := C.gca_events

@[simp] theorem expose_init : expose (initConfig Q) = initConfig publicQueue := rfl
@[simp] theorem kernel_expose (C : Configuration Q) : Public.kernel (expose C) = C := rfl

def label (C : Configuration Q) : Label Q → Label publicQueue
  | .fork dst src => .fork dst src
  | .apply t r o => .apply t r o
  | .merge a b => .merge a b
  | .query r q _ => .query r q (publicQueue.query ((C.headState r).getD Q.init) q)

theorem step {C C' : Configuration Q} {l : Label Q}
    (h : Step Q C l C') : Step publicQueue (expose C) (label C l) (expose C') := by
  cases h with
  | fork fresh source stored unused rank next vis ver head parents =>
      exact Step.fork (D := publicQueue) (C := expose C) fresh source stored unused rank _ vis ver head parents
  | apply head stored time fresh unused rank next vis ver heads parents =>
      exact Step.apply (D := publicQueue) (C := expose C) head stored time fresh unused rank _ vis ver heads parents
  | merge head₁ head₂ ver₁ ver₂ gca ver₀ fresh rank₁ rank₂ next vis ver heads parents =>
      exact Step.merge (D := publicQueue) (C := expose C) head₁ head₂ ver₁ ver₂ gca ver₀ fresh rank₁ rank₂ _ vis ver heads parents
  | query stateAt value =>
      apply Step.query (D := publicQueue) (C := expose _) stateAt
      simp only [stateAt,Option.getD_some]

theorem issued {C C' : Configuration Q} {l : Label Q}
    (h : IssuedStep Q issuance C l C') :
    IssuedStep publicQueue Public.issuance (expose C) (label C l) (expose C') := by
  cases h with
  | nonApply raw non =>
      refine .nonApply (step raw) ?_
      cases l <;> simp only [label]
      · intro t r o h; cases h
      · exact False.elim (non _ _ _ rfl)
      · intro t r o h; cases h
      · intro t r o h; cases h
  | apply head version guard raw => exact .apply head version guard (step raw)

theorem reach {C : Configuration Q} (h : MintCertifiedReach Q issuance C) :
    MintCertifiedReach publicQueue Public.issuance (expose C) := by
  induction h with
  | init => exact .init
  | step _ before action after ih => exact .step ih before (issued action) after

abbrev endpoint := expose (ExecutionControls.config 6)

theorem certified : MintCertifiedReach publicQueue Public.issuance endpoint :=
  reach ExecutionControls.certified

theorem certifiedV :
    MintCertifiedReachV publicQueue (canonicalVirtualMergeBase publicQueue)
      Public.issuance endpoint := certified.toV

/-- PASS+FAIL: the real merged version has tagged head (3,30), not the
concurrent tail child (4,40), and contains both live identities. -/
theorem public_certified_control :
    CertifiedExecution publicQueue Public.issuance endpoint ∧
    publicQueue.query (CertifiedRGARawOrderObstruction.records 6).1 () = some (3,30) ∧
    publicQueue.query (CertifiedRGARawOrderObstruction.records 6).1 () ≠ some (4,40) ∧
    publicQueue.query (CertifiedRGARawOrderObstruction.records 6).1 () ≠ none ∧
    endpoint.ver 6 = some ((CertifiedRGARawOrderObstruction.records 6).1,
      (↑((CertifiedRGARawOrderObstruction.indices 6).image CertifiedRGARawOrderObstruction.event) : Set Event)) := by
  refine ⟨.ordinary certified,?_,?_,?_,rfl⟩
  · change headQuery (CertifiedRGARawOrderObstruction.records 6).1 () = some (3,30)
    decide +kernel
  · change headQuery (CertifiedRGARawOrderObstruction.records 6).1 () ≠ some (4,40)
    decide +kernel
  · change headQuery (CertifiedRGARawOrderObstruction.records 6).1 () ≠ none
    decide +kernel

#print axioms certified
#print axioms public_certified_control

/-- The universal public bridge is instantiated on the actual nonempty
certified merge trace, including independent specification visibility. -/
theorem public_ra_control :
    InvariantOrder.VersionsRA publicQueue (Valid (Public.kernel endpoint))
      CertifiedRGAInvariantReplay.policy Public.language endpoint ∧
    publicQueue.query (CertifiedRGARawOrderObstruction.records 6).1 () = some (3,30) ∧
    publicQueue.query (CertifiedRGARawOrderObstruction.records 6).1 () ≠ some (4,40) := by
  exact ⟨History.correct certified,public_certified_control.2.1,public_certified_control.2.2.1⟩

#print axioms public_ra_control
end Sal.MRDTs.Paper1.AnchoredQueue.PublicControls
