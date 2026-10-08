import Sal.MRDTs.Instances.MVRLiveContract
import Sal.MRDTs.Paper1.GuardedQueueMVR
import Sal.MRDTs.Paper1.EventBridge

/-! Eligibility is membership in a genuinely certified configuration. Compact
MVR's carried overwrite targets then have visible births; concurrent eligible
writes commute concretely, even on arbitrary replay scratch states. -/
namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR
open Foundation
open Instances.MVRLive
open Classical

theorem overwrite_implies_visibility {C : Configuration D}
    (execution : CertifiedExecution D issuance C) {a b : Event}
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (target : a.time ∈ Instances.MVR.overwrites b) : C.vis a b := by
  obtain ⟨birth,member,vis,time⟩ := issued_overwrite execution.mintHonest hb target
  have same : birth = a := C.replayContext.ts_unique member ha time
  simpa only [same] using vis

theorem concurrent_targets_absent {C : Configuration D}
    (execution : CertifiedExecution D issuance C) {a b : Event}
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (concurrent : ¬ C.vis a b ∧ ¬ C.vis b a) :
    a.time ∉ Instances.MVR.overwrites b ∧ b.time ∉ Instances.MVR.overwrites a :=
  ⟨fun target => concurrent.1 (overwrite_implies_visibility execution ha hb target),
    fun target => concurrent.2 (overwrite_implies_visibility execution hb ha target)⟩

theorem concurrent_commutes {C : Configuration D}
    (execution : CertifiedExecution D issuance C) {a b : Event}
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (concurrent : ¬ C.vis a b ∧ ¬ C.vis b a) : D.toUpdateSig.commutes a b := by
  obtain ⟨hab,hba⟩ := concurrent_targets_absent execution ha hb concurrent
  intro s
  change update (update s a) b = update (update s b) a
  ext p
  simp only [update, Instances.MVR.clientStep, Finset.mem_insert, Finset.mem_filter]
  change a.1 ∉ Instances.MVR.overwrites b at hab
  change b.1 ∉ Instances.MVR.overwrites a at hba
  grind

/-- Empty payload conflict is exact on eligible concurrent writes. This does
not claim that causal birth/overwrite effects commute. -/
theorem concurrent_empty_exact {C : Configuration D}
    (execution : CertifiedExecution D issuance C) {a b : Event}
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (concurrent : ¬ C.vis a b ∧ ¬ C.vis b a) :
    ¬ D.toUpdateSig.commutes a b ↔
      (commutingPolicy D.AppOp).before a.op b.op ∨
      (commutingPolicy D.AppOp).before b.op a.op := by
  simp [commutingPolicy, concurrent_commutes execution ha hb concurrent]

end Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR
