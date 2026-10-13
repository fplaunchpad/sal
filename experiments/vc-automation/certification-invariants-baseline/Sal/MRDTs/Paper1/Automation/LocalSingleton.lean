import Sal.MRDTs.Paper1.Automation.LocalExpansion

/-! Equation-IH coverage for a fixed singleton causal-past contribution.
Only the nested common/opposite scopes must share a replay list. The causal
past is held fixed, avoiding the false three-scope common-chronology premise. -/
namespace Sal.MRDTs.Paper1.Automation.Signature
open Sal.MRDTs.Foundation Classical

def local_empty_sides (D : Signature) : Prop := ∀ B e,
  D.LocalEquation D.init B D.init e

theorem local_empty_sides_of_diagonal (D : Signature)
    (diagonal : ∀ l a, D.merge l a l = a) : D.local_empty_sides := by
  intro B e t
  rw [diagonal D.init _, diagonal D.init _]

/-- The equation-shaped IH fixes the singleton past and quantifies t. Events
outside the common scope require freshness of that singleton; common events
use the synchronized two-scope kernel, including the frozen event h itself. -/
theorem local_singleton_restrictedReplay (D : Signature)
    (seed : D.local_empty_sides) (common : D.local_common_opposite)
    (opposite : D.local_opposite_fresh) (freshBase : D.fresh_base)
    (freshStep : D.fresh_step) (L O : Set (Op D.AppOp)) (subset : L ⊆ O)
    (e h : Op D.AppOp) (π : List (Op D.AppOp))
    (freshE : ∀ q ∈ π, D.distinct e q)
    (outside : ∀ q ∈ π, q ∈ O → q ∉ L → D.distinct q h) :
    D.LocalEquation (D.restrictedReplay π L) (D.step D.init h)
      (D.restrictedReplay π O) e := by
  induction π using List.reverseRecOn with
  | nil => exact seed (D.step D.init h) e
  | append_singleton π q ih =>
    have oldFresh : ∀ x ∈ π, D.distinct e x :=
      fun x hx => freshE x (List.mem_append_left [q] hx)
    have previous := ih oldFresh
      (fun x hx => outside x (List.mem_append_left [q] hx))
    have freshL := D.fresh_restrictedReplay freshBase freshStep π L e oldFresh
    rw [restrictedReplay_append,restrictedReplay_append]
    by_cases commonQ : q ∈ L
    · simp only [commonQ,subset commonQ,if_true]
      exact common _ _ _ e q previous
    · by_cases otherQ : q ∈ O
      · simp only [commonQ,otherQ,if_true,if_false]
        have freshB := freshStep D.init q h
          (outside q (by simp) otherQ commonQ) (freshBase q)
        exact opposite _ _ _ e q freshL freshB previous
      · simpa only [commonQ,otherQ,if_false] using previous

end Sal.MRDTs.Paper1.Automation.Signature


#print axioms Sal.MRDTs.Paper1.Automation.Signature.local_singleton_restrictedReplay
