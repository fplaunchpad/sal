import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Continuation equivalence and representation lower bounds

Negative results for physical deletion, sibling splicing, and early mark
re-anchoring share one shape: two pasts that a proposed representation
identifies admit a legal continuation with different observations.  This is
the Myhill--Nerode principle for replicated-state representations.
-/

namespace Sal.ConditionedMRDTs

/-- Two histories are observationally indistinguishable under every declared
continuation. -/
def ContinuationEquivalent {History Cont Obs : Type}
    (extend : History → Cont → History) (observe : History → Obs)
    (h₁ h₂ : History) : Prop :=
  ∀ k, observe (extend h₁ k) = observe (extend h₂ k)

namespace ContinuationEquivalent

variable {History Cont Obs : Type}
  {extend : History → Cont → History} {observe : History → Obs}

theorem refl (h : History) : ContinuationEquivalent extend observe h h :=
  fun _ => rfl

theorem symm {h₁ h₂ : History}
    (h : ContinuationEquivalent extend observe h₁ h₂) :
    ContinuationEquivalent extend observe h₂ h₁ :=
  fun k => (h k).symm

theorem trans {h₁ h₂ h₃ : History}
    (h₁₂ : ContinuationEquivalent extend observe h₁ h₂)
    (h₂₃ : ContinuationEquivalent extend observe h₂ h₃) :
    ContinuationEquivalent extend observe h₁ h₃ :=
  fun k => (h₁₂ k).trans (h₂₃ k)

end ContinuationEquivalent

/-- A deterministic representation that supports the declared continuations
and reproduces their observations. -/
structure ContinuationRepresentation (History Cont Obs Repr : Type)
    (extend : History → Cont → History) (observe : History → Obs) where
  encode : History → Repr
  advance : Repr → Cont → Repr
  decode : Repr → Obs
  advance_encode : ∀ h k, advance (encode h) k = encode (extend h k)
  decode_encode : ∀ h, decode (encode h) = observe h

namespace ContinuationRepresentation

variable {History Cont Obs Repr : Type}
  {extend : History → Cont → History} {observe : History → Obs}
  (R : ContinuationRepresentation History Cont Obs Repr extend observe)

/-- Representation equality implies continuation equivalence. -/
theorem continuationEquivalent_of_encode_eq {h₁ h₂ : History}
    (hEq : R.encode h₁ = R.encode h₂) :
    ContinuationEquivalent extend observe h₁ h₂ := by
  intro k
  rw [← R.decode_encode (extend h₁ k), ← R.decode_encode (extend h₂ k),
    ← R.advance_encode h₁ k, ← R.advance_encode h₂ k, hEq]

/-- **Fooling-pair lower bound.** A single distinguishing continuation forces
every correct deterministic representation to retain different states for the
two histories. -/
theorem encode_ne_of_distinguishing {h₁ h₂ : History} {k : Cont}
    (hDist : observe (extend h₁ k) ≠ observe (extend h₂ k)) :
    R.encode h₁ ≠ R.encode h₂ := by
  intro hEq
  exact hDist (R.continuationEquivalent_of_encode_eq hEq k)

/-- A family whose unequal histories always admit a distinguishing
continuation must be represented injectively.  This is the cardinality-free
form of the information lower bound: any finite restriction immediately has
at least as many representation states as distinguishable histories. -/
theorem encode_injective_of_pairwise_distinguishable
    (hDist : ∀ {h₁ h₂ : History}, h₁ ≠ h₂ →
      ∃ k, observe (extend h₁ k) ≠ observe (extend h₂ k)) :
    Function.Injective R.encode := by
  intro h₁ h₂ hEq
  by_cases heq : h₁ = h₂
  · exact heq
  · obtain ⟨k, hk⟩ := hDist heq
    exact False.elim (hk (R.continuationEquivalent_of_encode_eq hEq k))

/-- Finite distinguishability gives a literal state-space lower bound. -/
theorem card_history_le_repr
    (R : ContinuationRepresentation History Cont Obs Repr extend observe)
    [Fintype History] [Fintype Repr]
    (hDist : ∀ {h₁ h₂ : History}, h₁ ≠ h₂ →
      ∃ k, observe (extend h₁ k) ≠ observe (extend h₂ k)) :
    Fintype.card History ≤ Fintype.card Repr :=
  Fintype.card_le_of_injective R.encode
    (R.encode_injective_of_pairwise_distinguishable hDist)

/-- An encoding into `Bits` booleans can distinguish at most `2^Bits`
continuation classes. -/
theorem card_history_le_two_pow_bits [Fintype History] (Bits : ℕ)
    (Rbits : ContinuationRepresentation History Cont Obs (Fin Bits → Bool)
      extend observe)
    (hDist : ∀ {h₁ h₂ : History}, h₁ ≠ h₂ →
      ∃ k, observe (extend h₁ k) ≠ observe (extend h₂ k)) :
    Fintype.card History ≤ 2 ^ Bits := by
  simpa using card_history_le_repr Rbits hDist

end ContinuationRepresentation

/-- A named fooling pair, suitable for packaging concrete countermodels. -/
structure ContinuationFoolingPair (History Cont Obs : Type)
    (extend : History → Cont → History) (observe : History → Obs) where
  left : History
  right : History
  continuation : Cont
  distinguishes :
    observe (extend left continuation) ≠ observe (extend right continuation)

theorem ContinuationFoolingPair.lowerBound
    {History Cont Obs Repr : Type}
    {extend : History → Cont → History} {observe : History → Obs}
    (P : ContinuationFoolingPair History Cont Obs extend observe)
    (R : ContinuationRepresentation History Cont Obs Repr extend observe) :
    R.encode P.left ≠ R.encode P.right :=
  R.encode_ne_of_distinguishing P.distinguishes

#print axioms ContinuationRepresentation.encode_ne_of_distinguishing
#print axioms ContinuationRepresentation.encode_injective_of_pairwise_distinguishable
#print axioms ContinuationRepresentation.card_history_le_repr
#print axioms ContinuationRepresentation.card_history_le_two_pow_bits
#print axioms ContinuationFoolingPair.lowerBound

end Sal.ConditionedMRDTs
