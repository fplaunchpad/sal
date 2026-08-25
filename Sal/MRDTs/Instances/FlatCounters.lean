import Sal.MRDTs.Metatheory.Correctness

/-! # Integer-delta MRDT family

Counter, increment-only counter, and PN-counter are instances of one group
construction.  Sharing the proof makes the production boundary smaller and
makes explicit that their ternary merge is addition with LCA subtraction.
-/

namespace Sal.MRDTs.Instances.FlatCounters

open Sal.MRDTs.Foundation

variable (A : Type) [DecidableEq A]

/-- An operation contributes an integer delta; ternary merge removes the LCA
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
    (D A delta).toCRDTSig.commutes a b := by
  intro s
  change Op A at a b
  change Int at s
  change (s + delta a.2.2) + delta b.2.2 =
    (s + delta b.2.2) + delta a.2.2
  omega

theorem updateVCs : UpdateVCs (D A delta).toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b _ _
    constructor
    · intro h
      exact absurd (all_comm delta a b) h
    · rintro (h | h) <;>
        (rw [show (D A delta).toCRDTSig.replayOrder _ _ = RcRes.Either from rfl] at h;
         exact RcRes.noConfusion h)
  · intro a b c _ _
    rintro ⟨h, _⟩
    rw [show (D A delta).toCRDTSig.replayOrder _ _ = RcRes.Either from rfl] at h
    exact RcRes.noConfusion h
  · intro s a b c π _ _ _ h _
    rw [show (D A delta).toCRDTSig.replayOrder _ _ = RcRes.Either from rfl] at h
    exact RcRes.noConfusion h

theorem coreVCs3 : CoreVCs3 (D A delta) := by
  refine ⟨updateVCs delta, ?_, ?_, ?_, ?_⟩
  · intro l a b
    change Int at l a b
    change a + b - l = b + a - l
    omega
  · intro s
    change Int at s
    change (0 : Int) + s - 0 = s
    omega
  · intro l a b e
    change Int at l a b
    change Op A at e
    change (a + delta e.2.2) + (b + delta e.2.2) -
      (l + delta e.2.2) = a + b - l + delta e.2.2
    omega
  · intro a e π₀ π₂ _ _
    change Int at a
    change Op A at e
    change (a + delta e.2.2) +
      (show Int from applySeq (D A delta).toCRDTSig (D A delta).init π₂) -
      (show Int from applySeq (D A delta).toCRDTSig (D A delta).init π₀) =
      a + (show Int from applySeq (D A delta).toCRDTSig (D A delta).init π₂) -
        (show Int from applySeq (D A delta).toCRDTSig (D A delta).init π₀) + delta e.2.2
    omega

theorem deltaVCs3 : DeltaVCs3 (D A delta) := by
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

theorem join : JoinLemma3 (D A delta) :=
  join_lemma3_of_cd' (coreVCs3 delta) (deltaVCs3 delta)
    (cdVC3_of_all_comm (coreVCs3 delta) (all_comm delta))

def generation : Issuance (D A delta) where
  CanIssue := fun _ _ => True

def convergence : ConvergenceCertificate (D A delta) (generation delta) where
  soundV := fun h => isRALinearizable_of_join
    (ra_of_mintCertifiedV (fun _ _ => join delta _) h)

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
  interaction := InteractionSpec.raw (D A delta)
  convergence := convergence delta
  Spec := spec (A := A) delta
  Rel := (· = ·)
  sequentialCorrectness := SequentialCorrectnessCertificate.ofTotal
    (fun _ => True.intro)
    (fun ops => (sequential delta).sound ops True.intro)
    (fun _ _ => rfl)

abbrev Counter := D Unit (fun _ => 1)

inductive IOCOp where | incr deriving DecidableEq
abbrev IOC := D IOCOp (fun _ => 1)

inductive PNOp where | inc | dec deriving DecidableEq

def pnDelta : PNOp → Int
  | .inc => 1
  | .dec => -1

abbrev PN := D PNOp pnDelta

noncomputable def counterVerified : VerifiedMRDT Counter := verified (fun _ => 1)
noncomputable def iocVerified : VerifiedMRDT IOC := verified (fun _ => 1)
noncomputable def pnVerified : VerifiedMRDT PN := verified pnDelta

#print axioms join
#print axioms counterVerified
#print axioms iocVerified
#print axioms pnVerified

end Sal.MRDTs.Instances.FlatCounters
