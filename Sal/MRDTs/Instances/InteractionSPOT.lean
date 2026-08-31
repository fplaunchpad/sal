import Sal.MRDTs.Metatheory.Correctness

/-!
# Semantic-interaction SPOTs

These finite examples test the public `InteractionSpec` independently of the
absorber-based replay proof.  LWW needs arbitrarily long concurrent timestamp
chains, so the historical `no_rc_chain` premise cannot be a public MRDT
requirement.  The add-wins example makes a different distinction: its concrete
effectors may commute, while the abstract sequential `add`/`remove` operations
still conflict and require remove-before-add when concurrent.
-/

namespace Sal.MRDTs.Instances.InteractionSPOT

open Sal.MRDTs.Foundation

namespace LWW

/-- A small carrier used only to type the independent sequential spec. -/
def D : MRDTSig where
  State := Nat
  dec_state := inferInstance
  init := 0
  AppOp := Nat
  dec_op := inferInstance
  Query := Unit
  Value := Nat
  update _ e := e.2.2
  query s _ := s
  merge _ a b := max a b

/-- LWW orders concurrent writes by increasing Lamport timestamp. Equal
timestamps are unreachable for distinct events and need no direction. -/
def interaction : InteractionSpec D where
  interaction := fun e₁ e₂ =>
    if e₁.time < e₂.time then .conflict .fstThenSnd
    else if e₂.time < e₁.time then .conflict .sndThenFst
    else .conflict .unconstrained
  swap_coherent := by
    intro e₁ e₂
    by_cases h₁₂ : e₁.time < e₂.time
    · have h₂₁ : ¬ e₂.time < e₁.time := Nat.not_lt_of_ge (Nat.le_of_lt h₁₂)
      simp [h₁₂, h₂₁, Interaction.flip, ConcurrentOrder.flip]
    · by_cases h₂₁ : e₂.time < e₁.time
      · simp [h₁₂, h₂₁, Interaction.flip, ConcurrentOrder.flip]
      · simp [h₁₂, h₂₁, Interaction.flip, ConcurrentOrder.flip]

def w₁ : Op Nat := (1, 0, 10)
def w₂ : Op Nat := (2, 1, 20)
def w₃ : Op Nat := (3, 2, 30)

/-- Positive control: the public policy admits an ordinary three-write chain. -/
example :
    (interaction.interaction w₁ w₂).FstBeforeSnd ∧
    (interaction.interaction w₂ w₃).FstBeforeSnd := by
  simp [interaction, w₁, w₂, w₃, Op.time, Interaction.FstBeforeSnd]

/-- Negative control for the retired interface premise. -/
theorem old_no_chain_refuted :
    ¬ (∀ a b c : Op D.AppOp,
      distinctOps (D := D.toUpdateSig) a b →
      distinctOps (D := D.toUpdateSig) b c →
      ¬ ((interaction.interaction a b).FstBeforeSnd ∧
         (interaction.interaction b c).FstBeforeSnd)) := by
  intro h
  apply h w₁ w₂ w₃
  · simp [distinctOps, w₁, w₂, Op.time]
  · simp [distinctOps, w₂, w₃, Op.time]
  · simp [interaction, w₁, w₂, w₃, Op.time, Interaction.FstBeforeSnd]

def spec : SequentialSpec D where
  State := Nat
  init := 0
  step _ e := e.2.2
  Legal := fun _ => True
  query s _ := s

/-- Timestamp order gives the expected last-writer result. -/
example : (show Nat from spec.run [w₁, w₂, w₃]) = 30 := by native_decide

end LWW

namespace AddWins

inductive AOp where
  | add
  | remove (observed : Finset Nat)
  deriving DecidableEq

def D : MRDTSig where
  State := Finset Nat × Finset Nat
  dec_state := inferInstance
  init := (∅, ∅)
  AppOp := AOp
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update s e := match e.2.2 with
    | .add => (insert e.time s.1, s.2)
    | .remove observed => (s.1, s.2 ∪ observed)
  query s _ := decide (∃ tag ∈ s.1, tag ∉ s.2)
  merge _ a b := (a.1 ∪ b.1, a.2 ∪ b.2)

/-- Add and remove conflict abstractly. Concurrent remove precedes add, which
is precisely the sequential explanation of add-wins. Same-kind operations are
independent. -/
def interaction : InteractionSpec D where
  interaction := fun e₁ e₂ =>
    match e₁.op, e₂.op with
    | .add, .remove _ => .conflict .sndThenFst
    | .remove _, .add => .conflict .fstThenSnd
    | _, _ => .independent
  swap_coherent := by
    intro e₁ e₂
    rcases e₁ with ⟨t₁, r₁, o₁⟩
    rcases e₂ with ⟨t₂, r₂, o₂⟩
    cases o₁ <;> cases o₂ <;> rfl

def add : Op AOp := (2, 0, .add)
def remove : Op AOp := (1, 1, .remove ∅)
def observedRemove : Op AOp := (3, 1, .remove {2})

/-- Representation-level observed-remove effectors commute: the remove carries
its origin view as a payload and only grows the removed-tag set. -/
example : D.toUpdateSig.commutes add remove := by
  intro s
  rfl

def spec : SequentialSpec D where
  State := Bool
  init := false
  step _ e := match e.2.2 with | .add => true | .remove _ => false
  Legal := fun _ => True
  query s _ := s

/-- Positive control: concurrent remove-before-add produces add-wins. -/
example : (show Bool from spec.run [remove, add]) = true := by native_decide

/-- Negative control: reversing the edge produces remove-wins. -/
example : (show Bool from spec.run [add, remove]) = false := by native_decide

example : (interaction.interaction remove add).FstBeforeSnd := by
  simp [interaction, remove, add, Op.op, Interaction.FstBeforeSnd]
example : ¬ (interaction.interaction add remove).FstBeforeSnd := by
  simp [interaction, remove, add, Op.op, Interaction.FstBeforeSnd]

/-- A causally observed add still precedes its conflicting remove through the
visibility arm of `interactionLoOn`, so ordinary remove semantics is retained. -/
example (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
    (hvis : C.vis add observedRemove) :
    interactionLoOn interaction C {add, observedRemove} add observedRemove := by
  exact Or.inl ⟨hvis, by
    simp [interaction, add, observedRemove, Op.op, Interaction.Conflicts]⟩

end AddWins

#print axioms LWW.old_no_chain_refuted

end Sal.MRDTs.Instances.InteractionSPOT
