import Sal.MRDTs.Metatheory.Correctness

/-!
# Add-wins observed-remove set

This production instance stores two grow-only finite sets: tagged additions
and removed tags. An add uses its globally fresh event timestamp as its tag. A
remove carries exactly the currently live tags for one element at its issuer.
The effectors commute because the observed set is frozen in the operation.
-/

namespace Sal.MRDTs.Instances.ORSet

open Sal.MRDTs.Foundation

variable (α : Type) [DecidableEq α]

inductive OROp where
  | add (element : α)
  | remove (element : α) (observed : Finset Timestamp)
  deriving DecidableEq

abbrev AddRecord := Timestamp × α
abbrev State := Finset (AddRecord α) × Finset Timestamp

def update (state : State α) (event : Op (OROp α)) : State α :=
  match event.2.2 with
  | .add element => (insert (event.1, element) state.1, state.2)
  | .remove _ observed => (state.1, state.2 ∪ observed)

def merge (left right : State α) : State α :=
  (left.1 ∪ right.1, left.2 ∪ right.2)

def liveTags (state : State α) (element : α) : Finset Timestamp :=
  (state.1.filter fun record =>
    decide (record.2 = element ∧ record.1 ∉ state.2)).image Prod.fst

def contains (state : State α) (element : α) : Bool :=
  decide (liveTags α state element).Nonempty

def D : MRDTSig where
  State := State α
  dec_state := inferInstance
  init := (∅, ∅)
  AppOp := OROp α
  dec_op := inferInstance
  Query := α
  Value := Bool
  update := update α
  query := contains α
  merge := fun _ left right => merge α left right

variable {α}

theorem all_comm (a b : Op (OROp α)) :
    (D α).toCRDTSig.commutes a b := by
  intro state
  rcases a with ⟨atime, ar, aa⟩
  rcases b with ⟨bt, br, ba⟩
  cases aa <;> cases ba <;>
    simp only [D, update]
  all_goals
    apply Prod.ext <;>
      apply Finset.ext <;>
        intro x <;>
          simp [or_assoc, or_left_comm, or_comm]

theorem updateVCs : UpdateVCs (D α).toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b _ _
    constructor
    · intro h
      exact absurd (all_comm a b) h
    · rintro (h | h) <;> exact RcRes.noConfusion h
  · intro a b c _ _
    rintro ⟨h, _⟩
    exact RcRes.noConfusion h
  · intro state a b c ops _ _ _ h _
    exact RcRes.noConfusion h

theorem coreVCs3 : CoreVCs3 (D α) := by
  refine ⟨updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    apply Prod.ext <;> apply Finset.ext <;> intro x <;>
      simp [D, merge, or_comm]
  · intro state
    apply Prod.ext <;> apply Finset.ext <;> intro x <;> simp [D, merge]
  · intro l a b event
    apply Prod.ext <;> apply Finset.ext <;> intro x
    · rcases event with ⟨time, replica, op⟩
      cases op <;> simp [D, merge, update, or_assoc, or_comm]
    · rcases event with ⟨time, replica, op⟩
      cases op <;> simp [D, merge, update, or_left_comm, or_comm]
  · intro a event before after _ _
    apply Prod.ext <;> apply Finset.ext <;> intro x
    · rcases event with ⟨time, replica, op⟩
      cases op <;> simp [D, merge, update, or_left_comm]
    · rcases event with ⟨time, replica, op⟩
      cases op <;> simp [D, merge, update, or_left_comm, or_comm]

theorem deltaVCs3 : DeltaVCs3 (D α) := by
  constructor
  · intro m x₀ x₁ x₂ c
    apply Prod.ext <;> apply Finset.ext <;> intro x <;>
      simp [D, merge, or_left_comm]
  · intro l m x c y
    apply Prod.ext <;> apply Finset.ext <;> intro z <;>
      simp [D, merge, or_comm]

theorem join : JoinLemma3 (D α) :=
  join_lemma3_of_cd' coreVCs3 deltaVCs3
    (cdVC3_of_all_comm coreVCs3 all_comm)

/-- Add timestamps must be fresh in the issuer state. A remove must carry all
and only the live tags for its named element at that state. -/
def canIssue (event : Op (OROp α)) (state : State α) : Prop :=
  match event.2.2 with
  | .add _ => event.1 ∉ state.1.image Prod.fst
  | .remove element observed => observed = liveTags α state element

instance canIssueDecidable (event : Op (OROp α)) (state : State α) :
    Decidable (canIssue event state) := by
  rcases event with ⟨time, replica, op⟩
  cases op <;> simp only [canIssue] <;> infer_instance

def issuance : Issuance (D α) where
  CanIssue := canIssue

def convergence : ConvergenceCertificate (D α) issuance where
  soundV := fun h => isRALinearizable_of_join
    (ra_of_mintCertifiedV (fun _ _ => join _) h)

/-! ## Independent sequential tagged-set machine -/

structure SeqState (α : Type) where
  additions : Finset (AddRecord α)
  removed : Finset Timestamp
  deriving DecidableEq

def seqInit (α : Type) : SeqState α := ⟨∅, ∅⟩

def seqStep (α : Type) [DecidableEq α]
    (state : SeqState α) (event : Op (OROp α)) : SeqState α :=
  match event.2.2 with
  | .add element => { state with
      additions := insert (event.1, element) state.additions }
  | .remove _ observed => { state with removed := state.removed ∪ observed }

def seqLiveTags (α : Type) [DecidableEq α]
    (state : SeqState α) (element : α) : Finset Timestamp :=
  (state.additions.filter fun record =>
    decide (record.2 = element ∧ record.1 ∉ state.removed)).image Prod.fst

def seqContains (α : Type) [DecidableEq α]
    (state : SeqState α) (element : α) : Bool :=
  decide (seqLiveTags α state element).Nonempty

def spec (α : Type) [DecidableEq α] : SequentialSpec (D α) where
  State := SeqState α
  init := seqInit α
  step := seqStep α
  Legal := fun _ => True
  query := seqContains α

def stateRel (state : State α) (sequential : SeqState α) : Prop :=
  state.1 = sequential.additions ∧ state.2 = sequential.removed

theorem step_preserves_rel {state : State α} {sequential : SeqState α}
    (rel : stateRel state sequential) (event : Op (OROp α)) :
    stateRel (update α state event) (seqStep α sequential event) := by
  rcases state with ⟨adds, removed⟩
  rcases sequential with ⟨seqAdds, seqRemoved⟩
  simp only [stateRel] at rel
  rcases rel with ⟨rfl, rfl⟩
  rcases event with ⟨time, replica, op⟩
  cases op <;> simp [stateRel, update, seqStep]

theorem fold_refines (ops : List (Op (OROp α))) :
    stateRel
      (applySeq (D α).toCRDTSig (D α).init ops)
      ((spec α).run ops) := by
  induction ops using List.reverseRecOn with
  | nil =>
      change (∅ : Finset (Timestamp × α)) = ∅ ∧
        (∅ : Finset Timestamp) = ∅
      exact ⟨rfl, rfl⟩
  | append_singleton ops event ih =>
      rw [applySeq_append_single, SequentialSpec.run_append_single]
      exact step_preserves_rel ih event

theorem query_refines (ops : List (Op (OROp α))) (element : α) :
    (D α).query (applySeq (D α).toCRDTSig (D α).init ops) element =
      (spec α).query ((spec α).run ops) element := by
  have rel := fold_refines (α := α) ops
  change decide (liveTags α
      (applySeq (D α).toCRDTSig (D α).init ops) element).Nonempty =
    decide (seqLiveTags α ((spec α).run ops) element).Nonempty
  unfold stateRel at rel
  rw [show liveTags α
        (applySeq (D α).toCRDTSig (D α).init ops) element =
      seqLiveTags α ((spec α).run ops) element by
    unfold liveTags seqLiveTags
    rw [rel.1, rel.2]]

noncomputable def verified : VerifiedMRDT (D α) where
  issuance := issuance
  interaction := InteractionSpec.raw (D α)
  convergence := convergence
  Spec := spec α
  Rel := stateRel
  sequentialCorrectness := SequentialCorrectnessCertificate.ofTotal
    (fun _ => True.intro)
    (fold_refines (α := α))
    (query_refines (α := α))

/-! ## Issuance and add-wins SPOTs -/

def addA : Op (OROp Nat) := (1, 0, .add 7)
def removeObserved : Op (OROp Nat) := (2, 0, .remove 7 {1})
def removeConcurrent : Op (OROp Nat) := (3, 1, .remove 7 ∅)
def afterAdd : State Nat := update Nat (D Nat).init addA

theorem add_fresh_issuable : canIssue addA (D Nat).init := by native_decide

theorem observed_remove_issuable : canIssue removeObserved afterAdd := by
  native_decide

theorem omitted_observed_tag_rejected : ¬ canIssue removeConcurrent afterAdd := by
  native_decide

theorem fabricated_tag_rejected :
    ¬ canIssue (4, 0, .remove 7 {99}) afterAdd := by native_decide

theorem observed_remove_removes :
    contains Nat (update Nat afterAdd removeObserved) 7 = false := by
  native_decide

theorem concurrent_remove_add_wins :
    contains Nat
      (update Nat (update Nat (D Nat).init removeConcurrent) addA) 7 = true := by
  native_decide

#print axioms verified
#print axioms observed_remove_issuable
#print axioms omitted_observed_tag_rejected
#print axioms concurrent_remove_add_wins

end Sal.MRDTs.Instances.ORSet
