import Sal.MRDTs.Metatheory.Correctness
import Sal.MRDTs.Metatheory.Safety
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.MinMax

/-!
# Last-writer-wins register

The representation stores the greatest timestamped write. Updates and merge
are `max`, so raw effectors commute and the default proof-local replay policy
is sufficient. The public interaction policy is separate: it orders writes by
their timestamped key. A sorted overwrite history is therefore an ordinary
sequential-register explanation of every stored state.
-/

namespace Sal.MRDTs.Instances.LWWRegister

open Sal.MRDTs.Foundation

inductive LWWOp where
  | write (value : Nat)
  deriving DecidableEq, Repr

/-- Timestamp first, followed by replica and value as deterministic tie
breakers. Reachable configurations already have globally unique timestamps. -/
abbrev LWWWrite := Lex (Nat × Lex (Nat × Nat))

/-- `bot` is the unset register; a non-bottom state is the winning write. -/
abbrev State := WithBot LWWWrite

def valueOf (event : Op LWWOp) : Nat :=
  match event.2.2 with
  | .write value => value

def packedWrite (event : Op LWWOp) : LWWWrite :=
  toLex (event.1, toLex (event.2.1, valueOf event))

def writeValue (write : LWWWrite) : Nat :=
  (ofLex (ofLex write).2).2

@[simp] theorem writeValue_packedWrite (event : Op LWWOp) :
    writeValue (packedWrite event) = valueOf event := by
  rcases event with ⟨time, replica, operation⟩
  cases operation
  rfl

def read : State → Option Nat
  | ⊥ => none
  | (write : LWWWrite) => some (writeValue write)

def update (state : State) (event : Op LWWOp) : State :=
  max state ↑(packedWrite event)

def D : MRDTSig where
  State := State
  dec_state := inferInstance
  init := ⊥
  AppOp := LWWOp
  dec_op := inferInstance
  Query := Unit
  Value := Option Nat
  update := update
  merge := fun _ left right => max left right
  query := fun state _ => read state

theorem all_comm (a b : Op D.AppOp) : D.toUpdateSig.commutes a b := by
  intro state
  simp only [D, update]
  simp [max_comm, max_assoc, max_left_comm]

theorem replayLaws : ReplayLaws D.toUpdateSig := by
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

theorem mergeLaws : MergeLaws D := by
  refine ⟨replayLaws, ?_, ?_⟩
  · intro _ left right
    simpa only [D] using (max_comm (α := State) left right)
  · intro state
    simpa only [D] using
      (max_eq_right (α := State) (bot_le : (⊥ : State) ≤ state))

theorem commutingPeelLaw : CommutingPeelLaw D := by
  constructor
  · intro state event π₀ π₂ _ _
    simp only [D, update]
    simp [max_comm, max_assoc, max_left_comm]

theorem deltaLaws : DeltaLaws D := by
  constructor
  · intro m x₀ x₁ x₂ c
    simp only [D]
    simp [max_comm, max_left_comm]
  · intro l m x c y
    simp only [D]
    simp [max_comm, max_left_comm]

theorem join : Join D :=
  JoinProof.ofArbitraryStateLaws mergeLaws deltaLaws
    (causalDeltaLaw_of_all_comm mergeLaws commutingPeelLaw all_comm)

def issuance : Issuance D where
  CanIssue := fun _ _ => True

def replayAdequacy : ReplayAdequacyCertificate D issuance :=
  ReplayAdequacyCertificate.ofJoin issuance join

/-- Raw LWW updates commute and the default replay policy adds no edge, so
the proof-local replay order is empty. -/
theorem replay_lo_false (C : Configuration D) (first second : Op LWWOp) :
    ¬ Sal.MRDTs.Foundation.lo C.replayContext first second := by
  rintro (⟨_, hnoncomm⟩ | ⟨_, _, horder, _⟩)
  · exact hnoncomm (all_comm first second)
  · exact RcRes.noConfusion horder

/-! ## Public timestamp order and sequential register -/

def interaction : InteractionSpec D where
  interaction := fun first second =>
    if packedWrite first < packedWrite second then .conflict .fstThenSnd
    else if packedWrite second < packedWrite first then .conflict .sndThenFst
    else .conflict .unconstrained
  swap_coherent := by
    intro first second
    by_cases h₁₂ : packedWrite first < packedWrite second
    · have h₂₁ : ¬ packedWrite second < packedWrite first :=
        not_lt_of_ge (le_of_lt h₁₂)
      simp [h₁₂, h₂₁, Interaction.flip, ConcurrentOrder.flip]
    · by_cases h₂₁ : packedWrite second < packedWrite first
      · simp [h₁₂, h₂₁, Interaction.flip, ConcurrentOrder.flip]
      · simp [h₁₂, h₂₁, Interaction.flip, ConcurrentOrder.flip]

/-- The independent sequential machine is an ordinary overwrite register. -/
def spec : SequentialSpec D where
  State := Option Nat
  init := none
  step := fun _ event => some (valueOf event)
  Legal := fun _ => True
  query := fun state _ => state

def stateRel (state : State) (abstract : Option Nat) : Prop :=
  read state = abstract

def writeLE (first second : Op LWWOp) : Prop :=
  packedWrite first ≤ packedWrite second

instance : DecidableRel writeLE := fun first second =>
  inferInstanceAs (Decidable (packedWrite first ≤ packedWrite second))

instance : IsTrans (Op LWWOp) writeLE :=
  ⟨fun _ _ _ firstSecond secondThird => le_trans firstSecond secondThird⟩

instance : Std.Total writeLE :=
  ⟨fun first second => le_total (packedWrite first) (packedWrite second)⟩

def canonical (ops : List (Op LWWOp)) : List (Op LWWOp) :=
  ops.insertionSort writeLE

theorem canonical_perm (ops : List (Op LWWOp)) : (canonical ops).Perm ops := by
  exact List.perm_insertionSort writeLE ops

theorem canonical_pairwise (ops : List (Op LWWOp)) :
    (canonical ops).Pairwise writeLE := by
  exact List.pairwise_insertionSort writeLE ops

theorem interaction_fstBefore_iff (first second : Op LWWOp) :
    (interaction.interaction first second).FstBeforeSnd ↔
      packedWrite first < packedWrite second := by
  by_cases h₁₂ : packedWrite first < packedWrite second
  · simp [interaction, h₁₂, Interaction.FstBeforeSnd]
  · by_cases h₂₁ : packedWrite second < packedWrite first
    · simp [interaction, h₁₂, h₂₁, Interaction.FstBeforeSnd]
    · simp [interaction, h₁₂, h₂₁, Interaction.FstBeforeSnd]

theorem canonical_respects (C : Configuration D) (E : Set (Op LWWOp))
    (ops : List (Op LWWOp)) :
    respects (canonical ops) (interactionLoOn interaction C.replayContext E) := by
  unfold respects
  exact (canonical_pairwise ops).imp fun {first second} hle hedge => by
    rcases hedge with hvisible | hconcurrent
    · have hlt : packedWrite second < packedWrite first := by
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inl (C.causal_mono hvisible.1)
      exact (not_lt_of_ge hle) hlt
    · have hlt := (interaction_fstBefore_iff second first).mp
          hconcurrent.2.2.1
      exact (not_lt_of_ge hle) hlt

theorem fold_refines_sorted : ∀ ops : List (Op LWWOp),
    ops.Pairwise writeLE →
      read (applySeq D.toUpdateSig D.init ops) = spec.run ops := by
  intro ops
  induction ops with
  | nil =>
      intro _
      rfl
  | cons first rest ih =>
      cases rest with
      | nil =>
          intro _
          simp [applySeq, D, update, spec, SequentialSpec.run,
            SequentialMachine.run, read]
      | cons second tail =>
          intro sorted
          have hpair := List.pairwise_cons.mp sorted
          have hle : packedWrite first ≤ packedWrite second :=
            hpair.1 second (by simp)
          have hle' : (↑(packedWrite first) : State) ≤ ↑(packedWrite second) := by
            exact_mod_cast hle
          have htail : (second :: tail).Pairwise writeLE := hpair.2
          simpa [applySeq, D, update, spec, SequentialSpec.run,
            SequentialMachine.run, max_eq_right bot_le, max_eq_right hle'] using
            ih htail

noncomputable def sequentialCorrectness :
    SequentialCorrectnessCertificate D issuance interaction spec stateRel where
  sound := by
    intro C _ replay v state E hver
    obtain ⟨base, hbasePerm, _, hbaseFold⟩ := replay v state E hver
    let ops := canonical base
    have hperm : listPermOf ops E := by
      refine ⟨hbasePerm.1.perm (canonical_perm base).symm, ?_⟩
      intro event
      exact (canonical_perm base).mem_iff.trans (hbasePerm.2 event)
    have hsorted : ops.Pairwise writeLE := canonical_pairwise base
    have hfoldCanonical : applySeq D.toUpdateSig D.init (canonical base) = state :=
      (applySeq_perm_of_all_comm (D' := D.toUpdateSig) all_comm
        (canonical_perm base) D.init).trans hbaseFold
    have hfold : applySeq D.toUpdateSig D.init ops = state := by
      simpa [ops] using hfoldCanonical
    have hrefines : stateRel state (spec.run ops) := by
      unfold stateRel
      rw [← hfold]
      exact fold_refines_sorted ops hsorted
    refine ⟨ops, hperm, canonical_respects C E base, True.intro, hrefines, ?_⟩
    intro query
    cases query
    exact hrefines

noncomputable def verified : VerifiedMRDT D where
  issuance := issuance
  interaction := interaction
  replayAdequacy := replayAdequacy
  Spec := spec
  Rel := stateRel
  sequentialCorrectness := sequentialCorrectness

/-! ## Proof-oriented controls -/

def w₁ : Op LWWOp := (1, 0, .write 10)
def w₂ : Op LWWOp := (2, 1, .write 20)
def w₃ : Op LWWOp := (3, 2, .write 30)

theorem timestamp_chain :
    (interaction.interaction w₁ w₂).FstBeforeSnd ∧
    (interaction.interaction w₂ w₃).FstBeforeSnd := by
  constructor <;> rw [interaction_fstBefore_iff] <;>
    apply Prod.Lex.toLex_lt_toLex.mpr <;> exact Or.inl (by decide)

theorem chronological_winner :
    D.query (applySeq D.toUpdateSig D.init [w₁, w₂, w₃]) () = some 30 := by
  change read (max (max (max (⊥ : State) ↑(packedWrite w₁))
    ↑(packedWrite w₂)) ↑(packedWrite w₃)) = some 30
  rw [max_eq_right bot_le]
  rw [max_eq_right (show (↑(packedWrite w₁) : State) ≤ ↑(packedWrite w₂) by
    exact_mod_cast (show packedWrite w₁ ≤ packedWrite w₂ by
      exact le_of_lt ((interaction_fstBefore_iff w₁ w₂).mp timestamp_chain.1)))]
  rw [max_eq_right (show (↑(packedWrite w₂) : State) ≤ ↑(packedWrite w₃) by
    exact_mod_cast (show packedWrite w₂ ≤ packedWrite w₃ by
      exact le_of_lt ((interaction_fstBefore_iff w₂ w₃).mp timestamp_chain.2)))]
  rfl

theorem reversed_delivery_same_winner :
    D.query (applySeq D.toUpdateSig D.init [w₃, w₁, w₂]) () = some 30 := by
  have hperm : ([w₃, w₁, w₂] : List (Op LWWOp)).Perm [w₁, w₂, w₃] := by
    decide
  have hfold := applySeq_perm_of_all_comm (D' := D.toUpdateSig)
    all_comm hperm D.init
  rw [hfold]
  exact chronological_winner

theorem lower_timestamp_does_not_win :
    D.query (applySeq D.toUpdateSig D.init [w₃, w₁, w₂]) () ≠ some 20 := by
  rw [reversed_delivery_same_winner]
  intro h
  injection h with impossible
  omega

#print axioms join
#print axioms replay_lo_false
#print axioms verified
#print axioms timestamp_chain
#print axioms chronological_winner
#print axioms lower_timestamp_does_not_win

end Sal.MRDTs.Instances.LWWRegister
