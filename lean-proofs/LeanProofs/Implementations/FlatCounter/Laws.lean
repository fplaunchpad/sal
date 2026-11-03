import LeanProofs.Implementations.FlatCounter.Definition
import LeanProofs.Interface.Laws

/-!
# The counter: discharging the obligations

Each obligation is an integer identity closed by `omega`.

Nothing here mentions configurations, executions, `lo^C_E`, `can`, or the
join lemma. The counter proves equations; the metatheory proves the theorem.
-/

namespace LeanProofs.Implementations.FlatCounter

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- Every pair of events commutes, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro z
  change Int at z
  change (z + delta e₁.op) + delta e₂.op = (z + delta e₂.op) + delta e₁.op
  omega

theorem rc_either (e₁ e₂ : D.Event) : D.RcEither e₁ e₂ := rfl

/-- **VC1** MERGE-COMM. -/
theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  change Int at l a b
  change a + b - l = b + a - l
  omega

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init (z : D.Sigma) : D.merge D.sigma0 D.sigma0 z = z := by
  change Int at z
  change (0 : Int) + z - 0 = z
  omega

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute (l m x c y : D.Sigma) :
    D.merge l (D.merge m x c) y = D.merge m (D.merge l x y) c := by
  change Int at l m x c y
  change (x + c - m) + y - l = x + y - l + c - m
  omega

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute (m x₀ x₁ x₂ c : D.Sigma) :
    D.merge (D.merge m x₀ c) (D.merge m x₁ c) (D.merge m x₂ c)
      = D.merge m (D.merge x₀ x₁ x₂) c := by
  change Int at m x₀ x₁ x₂ c
  change (x₁ + c - m) + (x₂ + c - m) - (x₀ + c - m) = x₁ + x₂ - x₀ + c - m
  omega

/-- The auxiliary peel law. The metatheory turns this into **VC4**
CAUSAL-DELTA. -/
theorem commuting_peel (a : D.Sigma) (e : D.Event) (pi₀ pi₂ : List D.Event)
    (_ : ∀ x ∈ pi₀, D.Commutes e x) (_ : ∀ x ∈ pi₂, D.Commutes e x) :
    D.merge (D.applyList D.sigma0 pi₀) (D.do_ a e) (D.applyList D.sigma0 pi₂)
      = D.do_ (D.merge (D.applyList D.sigma0 pi₀) a
          (D.applyList D.sigma0 pi₂)) e := by
  change Int at a
  change (a + delta e.op)
      + (show Int from D.applyList D.sigma0 pi₂)
      - (show Int from D.applyList D.sigma0 pi₀)
    = a + (show Int from D.applyList D.sigma0 pi₂)
      - (show Int from D.applyList D.sigma0 pi₀) + delta e.op
  omega

/-- VC1, VC2, VC3, VC5 and the peel law. -/
theorem joinLaws : CanonicalJoinLaws D :=
  ⟨vc1_merge_comm, vc2_merge_init, vc3_local_redistribute,
   vc5_redistribute, commuting_peel⟩

/-- Everything the metatheory consumes. -/
theorem obligations : Obligations D :=
  ⟨all_commute, rc_either, joinLaws⟩

end LeanProofs.Implementations.FlatCounter
