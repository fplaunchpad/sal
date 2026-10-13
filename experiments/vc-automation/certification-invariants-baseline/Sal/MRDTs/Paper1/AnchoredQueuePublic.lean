import Sal.MRDTs.Paper1.AnchoredQueue

/-! The public anchored queue exposes the existing tagged-head query. Changing
that observation does not alter its operational graph or issuance discipline. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.Public
open Foundation

def issuance : Issuance publicQueue := ⟨CanIssue⟩

def kernel (C : Configuration publicQueue) : Configuration Q where
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

@[simp] theorem kernel_init : kernel (initConfig publicQueue) = initConfig Q := rfl
@[simp] theorem kernel_headState (C : Configuration publicQueue) (r : Replica) :
    (kernel C).headState r = C.headState r := rfl

/-- Query labels are interpreted in the same concrete state, without assuming
that the head observation determines the whole queue. -/
def label (C : Configuration publicQueue) : Label publicQueue → Label Q
  | .fork dst src => .fork dst src
  | .apply t r o => .apply t r o
  | .merge a b => .merge a b
  | .query r q _ => .query r q (Q.query ((C.headState r).getD Q.init) q)

theorem step {C C' : Configuration publicQueue} {l : Label publicQueue}
    (h : Step publicQueue C l C') : Step Q (kernel C) (label C l) (kernel C') := by
  cases h with
  | fork fresh source stored unused rank next vis ver head parents =>
      exact Step.fork (D := Q) (C := kernel C) fresh source stored unused rank _ vis ver head parents
  | apply head stored time fresh unused rank next vis ver heads parents =>
      exact Step.apply (D := Q) (C := kernel C) head stored time fresh unused rank _ vis ver heads parents
  | merge head₁ head₂ ver₁ ver₂ gca ver₀ fresh rank₁ rank₂ next vis ver heads parents =>
      exact Step.merge (D := Q) (C := kernel C) head₁ head₂ ver₁ ver₂ gca ver₀ fresh rank₁ rank₂ _ vis ver heads parents
  | query stateAt value =>
      apply Step.query (D := Q) (C := kernel _) stateAt
      simp only [stateAt,Option.getD_some]

theorem mint {C : Configuration publicQueue} (h : MintHonest publicQueue CanIssue C) :
    MintHonest Q CanIssue (kernel C) := h

theorem issued {C C' : Configuration publicQueue} {l : Label publicQueue}
    (h : IssuedStep publicQueue issuance C l C') :
    IssuedStep Q AnchoredQueue.issuance (kernel C) (label C l) (kernel C') := by
  cases h with
  | nonApply raw non =>
      refine .nonApply (step raw) ?_
      cases l <;> simp only [label]
      · intro t r o h; cases h
      · exact False.elim (non _ _ _ rfl)
      · intro t r o h; cases h
      · intro t r o h; cases h
  | apply head version guard raw => exact .apply head version guard (step raw)

theorem reach {C : Configuration publicQueue}
    (h : MintCertifiedReach publicQueue issuance C) :
    MintCertifiedReach Q AnchoredQueue.issuance (kernel C) := by
  induction h with
  | init => exact .init
  | step _ before action after ih => exact .step ih (mint before) (issued action) (mint after)

private theorem fold_query_irrelevant (C : Configuration publicQueue)
    (S : Finset Version) (s : State) (xs : List Version) :
    vfoldAux (D := Q) C.ver C.parents C.parents_lt S s xs =
      vfoldAux (D := publicQueue) C.ver C.parents C.parents_lt S s xs := by
  fun_induction vfoldAux (D := Q) C.ver C.parents C.parents_lt S s xs with
  | case1 => simp only [vfoldAux_nil]
  | case2 S s m ms inner outer =>
      have base : virtualBaseAux (D := Q) C.ver C.parents C.parents_lt S m =
          virtualBaseAux (D := publicQueue) C.ver C.parents C.parents_lt S m := by
        unfold virtualBaseAux
        split
        · rfl
        · rename_i x xs eq
          exact inner x xs eq
      rw [vfoldAux_cons]
      rw [← base]
      exact outer

/-- The recursive virtual resolver depends only on the operational fields. -/
theorem virtual_base (C : Configuration publicQueue) (a b : Version) :
    virtualMergeBaseState (kernel C) a b = virtualMergeBaseState C a b := by
  unfold virtualMergeBaseState virtualBaseAux
  simp only [kernel]
  split
  · rfl
  · exact fold_query_irrelevant C _ _ _

theorem stepV {C C' : Configuration publicQueue} {l : Label publicQueue}
    (h : StepV publicQueue (canonicalVirtualMergeBase publicQueue) C l C') :
    StepV Q (canonicalVirtualMergeBase Q) (kernel C) (label C l) (kernel C') := by
  cases h with
  | base raw => exact .base (step raw)
  | mergeVirtual head₁ head₂ ver₁ ver₂ fresh rank₁ rank₂ next vis ver heads parents =>
      apply StepV.mergeVirtual (D := Q) (C := kernel C) head₁ head₂ ver₁ ver₂
        fresh rank₁ rank₂ _ vis _ heads parents
      simpa only [canonicalVirtualMergeBase,virtual_base] using ver

theorem issuedV {C C' : Configuration publicQueue} {l : Label publicQueue}
    (h : IssuedStepV publicQueue (canonicalVirtualMergeBase publicQueue) issuance C l C') :
    IssuedStepV Q (canonicalVirtualMergeBase Q) AnchoredQueue.issuance
      (kernel C) (label C l) (kernel C') := by
  classical
  cases h with
  | base raw => exact .base (issued raw)
  | virtual raw non =>
      have nonapply : ∀ t r o, l ≠ .apply t r o := by
        intro t r o eq
        subst l
        cases raw with
        | base ordinary => exact non ordinary
      by_cases ordinary : Step Q (kernel C) (label C l) (kernel C')
      · apply IssuedStepV.base
        refine .nonApply ordinary ?_
        cases l <;> simp only [label]
        · intro t r o h; cases h
        · exact False.elim (nonapply _ _ _ rfl)
        · intro t r o h; cases h
        · intro t r o h; cases h
      · exact .virtual (stepV raw) ordinary

theorem reachV {C : Configuration publicQueue}
    (h : MintCertifiedReachV publicQueue (canonicalVirtualMergeBase publicQueue) issuance C) :
    MintCertifiedReachV Q (canonicalVirtualMergeBase Q) AnchoredQueue.issuance (kernel C) := by
  induction h with
  | init => exact .init
  | step _ before action after ih => exact .step ih (mint before) (issuedV action) (mint after)

theorem execution {C : Configuration publicQueue}
    (h : CertifiedExecution publicQueue issuance C) :
    CertifiedExecution Q AnchoredQueue.issuance (kernel C) := by
  cases h with
  | ordinary h => exact .ordinary (reach h)
  | virtual h => exact .virtual (reachV h)

noncomputable def fifoSpec : SequentialSpec publicQueue where
  State := List (Nat × Nat)
  init := []
  step := AnchoredQueue.fifoStep
  Legal := AnchoredQueue.fifoLegal
  query := fun s _ => s.head?

noncomputable def language := GuardedHistory.language fifoSpec

#print axioms execution
#print axioms reach
#print axioms virtual_base
end Sal.MRDTs.Paper1.AnchoredQueue.Public
