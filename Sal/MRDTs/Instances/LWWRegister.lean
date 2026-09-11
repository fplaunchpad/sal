import Sal.MRDTs.Metatheory.Correctness
import Sal.MRDTs.Metatheory.Safety
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.MinMax

/-!
# Last-writer-wins register

The representation stores the greatest timestamped write. Updates and merge
are `max`, so raw effectors commute. Its sole public `rc` policy orders writes
by their timestamped key. A sorted overwrite history is therefore an ordinary
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

def rc : ReplayPolicy D.toUpdateSig where
  order := fun first second =>
    if packedWrite first < packedWrite second then .Fst_then_snd
    else if packedWrite second < packedWrite first then .Snd_then_fst
    else .Either

local instance : ReplayPolicy D.toUpdateSig := rc

theorem rc_fst_iff (first second : Op LWWOp) :
    rc.order first second = RcRes.Fst_then_snd ↔
      packedWrite first < packedWrite second := by
  by_cases h₁₂ : packedWrite first < packedWrite second
  · simp [rc, h₁₂]
  · by_cases h₂₁ : packedWrite second < packedWrite first
    · simp [rc, h₁₂, h₂₁]
    · simp [rc, h₁₂, h₂₁]

/-- The public LWW direction permits chains but cannot contain a cycle because
every edge strictly increases the packed write key. -/
theorem rc_order_acyclic (first : Op LWWOp) :
    ¬ Relation.TransGen
      (fun a b => rc.order a b = RcRes.Fst_then_snd)
      first first := by
  intro hcycle
  have hlt : Relation.TransGen
      (fun a b : Op LWWOp => packedWrite a < packedWrite b)
      first first :=
    hcycle.lift id (fun a b h => (rc_fst_iff a b).mp h)
  have htrans : Transitive
      (fun a b : Op LWWOp => packedWrite a < packedWrite b) :=
    fun _ _ _ => lt_trans
  rw [Relation.transGen_eq_self htrans] at hlt
  exact lt_irrefl _ hlt

/-- The same public timestamp policy is used throughout the concrete replay
and sequential-correctness proofs. Its ordered updates may commute. -/
theorem replayLaws : @ReplayLaws D.toUpdateSig rc :=
  ReplayLaws.of_all_comm all_comm rc_order_acyclic

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

/-! ## Ordinary sequential register -/

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


theorem canonical_respects (C : Configuration D) (E : Set (Op LWWOp))
    (ops : List (Op LWWOp)) :
    respects (canonical ops) (@loOn D.toUpdateSig rc C.replayContext E) := by
  unfold respects
  exact (canonical_pairwise ops).imp fun {first second} hle hedge => by
    rcases hedge with hvisible | hconcurrent
    · have hlt : packedWrite second < packedWrite first := by
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inl (C.causal_mono hvisible.1)
      exact (not_lt_of_ge hle) hlt
    · have hlt := (rc_fst_iff second first).mp hconcurrent.2.2.1
      exact (not_lt_of_ge hle) hlt

def replayAdequacy : @ReplayAdequacyCertificate D issuance rc :=
  ReplayAdequacyCertificate.ofJoin issuance join

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
    SequentialCorrectnessCertificate D issuance rc spec stateRel where
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
  rc := rc
  replayAdequacy := replayAdequacy
  Spec := spec
  Rel := stateRel
  sequentialCorrectness := sequentialCorrectness

/-! ## Proof-oriented controls -/

def w₁ : Op LWWOp := (1, 0, .write 10)
def w₂ : Op LWWOp := (2, 1, .write 20)
def w₃ : Op LWWOp := (3, 2, .write 30)

theorem timestamp_chain :
    rc.order w₁ w₂ = RcRes.Fst_then_snd ∧
    rc.order w₂ w₃ = RcRes.Fst_then_snd := by
  constructor <;> rw [rc_fst_iff] <;>
    apply Prod.Lex.toLex_lt_toLex.mpr <;> exact Or.inl (by decide)

theorem chronological_winner :
    D.query (applySeq D.toUpdateSig D.init [w₁, w₂, w₃]) () = some 30 := by
  change read (max (max (max (⊥ : State) ↑(packedWrite w₁))
    ↑(packedWrite w₂)) ↑(packedWrite w₃)) = some 30
  rw [max_eq_right bot_le]
  rw [max_eq_right (show (↑(packedWrite w₁) : State) ≤ ↑(packedWrite w₂) by
    exact_mod_cast (show packedWrite w₁ ≤ packedWrite w₂ by
      exact le_of_lt ((rc_fst_iff w₁ w₂).mp timestamp_chain.1)))]
  rw [max_eq_right (show (↑(packedWrite w₂) : State) ≤ ↑(packedWrite w₃) by
    exact_mod_cast (show packedWrite w₂ ≤ packedWrite w₃ by
      exact le_of_lt ((rc_fst_iff w₂ w₃).mp timestamp_chain.2)))]
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

/-- PASS: semantic resolution orders writes whose concrete updates commute. -/
theorem ordered_updates_commute :
    rc.Before w₁ w₂ ∧ D.toUpdateSig.commutes w₁ w₂ := by
  exact ⟨(rc_fst_iff w₁ w₂).mpr (by decide), all_comm w₁ w₂⟩

/-- FAIL: concrete noncommutation cannot characterize the semantic policy. -/
theorem concrete_noncomm_iff_rc_refuted :
    ¬ (∀ a b : Op LWWOp,
      ¬ D.toUpdateSig.commutes a b ↔ (rc.Before a b ∨ rc.Before b a)) := by
  intro h
  exact ((h w₁ w₂).mpr (Or.inl ordered_updates_commute.1))
    ordered_updates_commute.2

/-- The ordinary overwrite machine needs the selected order, even though the
concrete implementation tolerates reversed delivery. -/
theorem reversed_assignments_wrong_winner :
    spec.run [w₁, w₂] = some 20 ∧
    spec.run [w₂, w₁] = some 10 ∧
    spec.run [w₂, w₁] ≠ spec.run [w₁, w₂] := by
  change (some 20 : Option Nat) = some 20 ∧
    (some 10 : Option Nat) = some 10 ∧ (some 10 : Option Nat) ≠ some 20
  decide

#print axioms join
#print axioms verified
#print axioms rc_order_acyclic
#print axioms timestamp_chain
#print axioms chronological_winner
#print axioms lower_timestamp_does_not_win
#print axioms replayLaws
#print axioms ordered_updates_commute
#print axioms concrete_noncomm_iff_rc_refuted
#print axioms reversed_assignments_wrong_winner

end Sal.MRDTs.Instances.LWWRegister
