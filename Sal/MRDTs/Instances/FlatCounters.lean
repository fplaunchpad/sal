import Sal.MRDTs.Metatheory.Correctness

/-! # Integer-delta MRDT family

The signed Counter uses an integer-delta group construction. Its ternary
merge is addition with GCA subtraction.
-/

namespace Sal.MRDTs.Instances.FlatCounters

open Sal.MRDTs.Foundation

variable (A : Type) [DecidableEq A]

/-- An operation contributes an integer delta; ternary merge removes the GCA
contribution exactly once. -/
def D (delta : A → Int) : MRDTSig where
  State := Int
  dec_state := inferInstance
  init := 0
  AppOp := A
  dec_op := inferInstance
  Query := Unit
  Value := Int
  update s e := s + delta e.2.2
  query s _ := s
  merge l a b := a + b - l

variable {A} (delta : A → Int)

theorem all_comm (a b : Op (D A delta).AppOp) :
    (D A delta).toUpdateSig.commutes a b := by
  intro s
  change Op A at a b
  change Int at s
  change (s + delta a.2.2) + delta b.2.2 =
    (s + delta b.2.2) + delta a.2.2
  omega

theorem replayLaws : ReplayLaws (D A delta).toUpdateSig := by
  apply ReplayLaws.of_all_comm (all_comm delta)
  apply replayAcyclic_of_noReplayChain
  intro a b c h
  exact OrderResult.noConfusion h.1

theorem mergeLaws : MergeLaws (D A delta) := by
  refine ⟨replayLaws delta, ?_, ?_⟩
  · intro l a b
    change Int at l a b
    change a + b - l = b + a - l
    omega
  · intro s
    change Int at s
    change (0 : Int) + s - 0 = s
    omega

theorem commutingPeelLaw : CommutingPeelLaw (D A delta) := by
  constructor
  · intro a e π₀ π₂ _ _
    change Int at a
    change Op A at e
    change (a + delta e.2.2) +
      (show Int from applySeq (D A delta).toUpdateSig (D A delta).init π₂) -
      (show Int from applySeq (D A delta).toUpdateSig (D A delta).init π₀) =
      a + (show Int from applySeq (D A delta).toUpdateSig (D A delta).init π₂) -
        (show Int from applySeq (D A delta).toUpdateSig (D A delta).init π₀) + delta e.2.2
    omega

theorem deltaLaws : DeltaLaws (D A delta) := by
  constructor
  · intro m x₀ x₁ x₂ c
    change Int at m x₀ x₁ x₂ c
    change (x₁ + c - m) + (x₂ + c - m) - (x₀ + c - m) =
      x₁ + x₂ - x₀ + c - m
    omega
  · intro l m x c y
    change Int at l m x c y
    change (x + c - m) + y - l = x + y - l + c - m
    omega

theorem join : Join (D A delta) :=
  JoinProof.ofArbitraryStateLaws (mergeLaws delta) (deltaLaws delta)
    (causalDeltaLaw_of_all_comm (mergeLaws delta) (commutingPeelLaw delta)
      (all_comm delta))

def generation : Issuance (D A delta) where
  CanIssue := fun _ _ => True

def replayAdequacy : ReplayAdequacyCertificate (D A delta) (generation delta) :=
  ReplayAdequacyCertificate.ofJoin (generation delta) (join delta)

def spec : SequentialSpec (D A delta) where
  State := Int
  init := 0
  step s e := s + delta e.2.2
  Legal := fun _ => True
  query := fun s _ => s

def sequential : SequentialRefinement (D A delta)
    (spec (A := A) delta).toSequentialMachine where
  Honest := fun _ => True
  Rel := (· = ·)
  init := rfl
  sound := fun _ _ => rfl

noncomputable def verified : VerifiedMRDT (D A delta) where
  issuance := generation delta
  replayOrder := EventOrder.unconstrained (D A delta).toUpdateSig
  replayAdequacy := replayAdequacy delta
  Spec := spec (A := A) delta
  Rel := (· = ·)
  sequentialCorrectness := SequentialCorrectnessCertificate.ofTotal
    (fun C _ => join delta C.replayContext)
    (all_comm delta)
    (fun _ _ => rfl)
    (fun _ => True.intro)
    (fun ops => (sequential delta).sound ops True.intro)
    (fun _ _ => rfl)

inductive CounterOp where | inc | dec deriving DecidableEq

def counterDelta : CounterOp → Int
  | .inc => 1
  | .dec => -1

abbrev Counter := D CounterOp counterDelta

noncomputable def counterVerified : VerifiedMRDT Counter := verified counterDelta

/-- Free signed operations: decrement at zero is negative, never clamped. -/
theorem counter_controls :
    Counter.update (0 : Int) (1,0,.inc) = (1 : Int) ∧
    Counter.update (0 : Int) (1,0,.inc) ≠ (0 : Int) ∧
    Counter.update (0 : Int) (1,0,.dec) = (-1 : Int) ∧
    Counter.update (0 : Int) (1,0,.dec) ≠ (0 : Int) ∧
    Counter.update (-1 : Int) (2,0,.inc) = (0 : Int) ∧
    Counter.update (-1 : Int) (2,0,.dec) = (-2 : Int) := by decide

#print axioms join
#print axioms counterVerified

end Sal.MRDTs.Instances.FlatCounters
