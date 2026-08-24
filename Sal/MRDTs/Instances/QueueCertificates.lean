import Sal.MRDTs.Instances.QueueSequential

/-! Production certificates for the mergeable queue over the plain MRDT API. -/

namespace Sal.MRDTs.Instances.Queue

open Sal.MRDTs.Foundation
open Classical

def QHonest (C : Configuration Q) : Prop :=
  ∀ e ∈ C.events, ∀ t : ℕ, e.2.2 = QOp.deq t →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = t ∧ ∃ v, a.2.2 = QOp.enq v

theorem qHonest_core {C : Configuration Q} (h : QHonest C) :
    QHonestCore C.core := by
  exact h

/-- Enqueue stamps are fresh; dequeue records the head observed by its issuer. -/
def qApplicable (o : Op QOp) (s : QState) : Prop :=
  match o.2.2 with
  | .enq _ => o.1 ∉ qTags s
  | .deq t => ∃ v rest, s = (t, v) :: rest

theorem qTags_fold_sub : ∀ (π : List (Op QOp)) (t : ℕ),
    t ∈ qTags (applySeq Q.toCRDTSig Q.init π) →
    ∃ a ∈ π, qIsEnq a = true ∧ a.1 = t := by
  intro π
  induction π using List.reverseRecOn with
  | nil =>
      intro t ht
      change t ∈ qTags ([] : QState) at ht
      simpa [qTags] using ht
  | append_singleton π e ih =>
    intro t ht
    rw [applySeq_append_single] at ht
    rw [Q_core_update] at ht
    set s : QState := applySeq Q.toCRDTSig Q.init π
    obtain ⟨ts, r, op⟩ := e
    cases op with
    | enq v =>
      by_cases hmem : ts ∈ qTags s
      · rw [show qUpdate s (ts, r, QOp.enq v) = s from by simp [qUpdate, hmem]] at ht
        obtain ⟨a, ha, h1, h2⟩ := ih t ht
        exact ⟨a, List.mem_append_left _ ha, h1, h2⟩
      · rw [show qUpdate s (ts, r, QOp.enq v) = s ++ [(ts, v)] from by
          simp [qUpdate, hmem]] at ht
        unfold qTags at ht
        rw [List.map_append, List.mem_append] at ht
        rcases ht with ht | ht
        · obtain ⟨a, ha, h1, h2⟩ := ih t ht
          exact ⟨a, List.mem_append_left _ ha, h1, h2⟩
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
          exact ⟨(ts, r, QOp.enq v), List.mem_append_right _ (by simp),
            by simp [qIsEnq], by simpa using ht.symm⟩
    | deq t' =>
      have hsub : qTags (qUpdate s (ts, r, QOp.deq t')) ⊆ qTags s := by
        intro x hx
        unfold qUpdate at hx
        unfold qTags at hx ⊢
        rw [List.mem_map] at hx ⊢
        obtain ⟨p, hp, hpx⟩ := hx
        exact ⟨p, List.mem_of_mem_filter hp, hpx⟩
      obtain ⟨a, ha, h1, h2⟩ := ih t (hsub ht)
      exact ⟨a, List.mem_append_left _ ha, h1, h2⟩

theorem qHonest_of_mint (C : Configuration Q)
    (h : MintHonest Q qApplicable C) : QHonest C := by
  intro e he t ht
  obtain ⟨π, hπ, _, hg⟩ := h e he
  obtain ⟨ts, r, op⟩ := e
  simp only at ht
  subst ht
  obtain ⟨v, rest, hs⟩ := hg
  have htag : t ∈ qTags (applySeq Q.toCRDTSig Q.init π) := by
    rw [hs]
    simp [qTags]
  obtain ⟨a, ha, hEnq, htag⟩ := qTags_fold_sub π t htag
  have haev := (hπ.2 a).mp ha
  obtain ⟨ats, ar, aop⟩ := a
  cases aop with
  | deq t' => exact absurd hEnq (by simp [qIsEnq])
  | enq w => exact ⟨(ats, ar, QOp.enq w), haev.1, haev.2, htag, w, rfl⟩

def generation : Issuance Q where
  CanIssue := qApplicable

def convergence : ConvergenceCertificate Q generation where
  soundV := fun h =>
    ra_of_mintCertifiedV
      (fun _ hC => q_join_at (qHonest_core (qHonest_of_mint _ hC))) h

def spec : SequentialMachine (Op QOp) where
  State := List ℕ
  init := []
  step := qSpecStep

theorem spec_run (ρ : List (Op QOp)) : spec.run ρ = qSpecFold ρ := rfl

theorem qOK_of_linear {ρ : List (Op QOp)}
    (h : LinearMintHistory Q qApplicable ρ) : qOK ρ := by
  intro σ o τ heq
  have hg := h.guarded σ o τ heq
  obtain ⟨ts, r, op⟩ := o
  cases op with
  | enq w =>
      constructor
      · intro v _
        exact hg
      · intro t hbad
        cases hbad
  | deq t' =>
      constructor
      · intro v hbad
        cases hbad
      · intro t heq
        cases heq
        exact hg

def sequential : SequentialRefinement Q spec where
  Honest := qOK
  Rel := fun s q => s.map Prod.snd = q
  init := rfl
  sound := by
    intro ρ h
    rw [spec_run]
    exact queue_seq_sound h

noncomputable def replayVerified : ReplayVerifiedMRDT Q where
  issuance := generation
  convergence := convergence
  Machine := spec
  sequential := sequential
  sequential_of_mint := fun _ h => qOK_of_linear h

example : qApplicable (0, 0, QOp.enq 7) [] := by simp [qApplicable, qTags]

example : ¬ qApplicable (1, 0, QOp.deq 7) [] := by simp [qApplicable]

#print axioms q_join_at
#print axioms queue_seq_sound
#print axioms replayVerified

end Sal.MRDTs.Instances.Queue
