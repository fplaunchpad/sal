import LeanProofs.Implementations.LWWRegister.Definition
import LeanProofs.Interface.Laws

/-!
# The last-writer-wins register: discharging the obligations

`Sigma` is linearly ordered and both `do` and `merge` are `max`, so every
obligation is an instance of commutativity, associativity or idempotence of
`max`, with `bot` as the identity.

Nothing here mentions configurations, executions, `lo^C_E`, `can`, or the
join lemma.
-/

namespace LeanProofs.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

/-- Two writes commute: both orders take the greater key. By RC-NON-COMM
`rc` is therefore empty. -/
theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro s
  change max (max s ↑(packed e₁)) ↑(packed e₂)
    = max (max s ↑(packed e₂)) ↑(packed e₁)
  simp [max_assoc, max_comm, max_left_comm]

theorem rc_either (e₁ e₂ : D.Event) : D.RcEither e₁ e₂ := rfl

/-- **VC1** MERGE-COMM. -/
theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  change max a b = max b a
  exact max_comm _ _

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init (s : D.Sigma) : D.merge D.sigma0 D.sigma0 s = s := by
  change max (⊥ : St) s = s
  exact max_eq_right bot_le

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute (l m x c y : D.Sigma) :
    D.merge l (D.merge m x c) y = D.merge m (D.merge l x y) c := by
  change max (max x c) y = max (max x y) c
  simp [max_assoc, max_comm, max_left_comm]

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute (m x₀ x₁ x₂ c : D.Sigma) :
    D.merge (D.merge m x₀ c) (D.merge m x₁ c) (D.merge m x₂ c)
      = D.merge m (D.merge x₀ x₁ x₂) c := by
  change max (max x₁ c) (max x₂ c) = max (max x₁ x₂) c
  simp [max_assoc, max_comm, max_left_comm]

/-- The auxiliary peel law. The metatheory turns this into **VC4**
CAUSAL-DELTA. -/
theorem commuting_peel (a : D.Sigma) (e : D.Event) (pi₀ pi₂ : List D.Event)
    (_ : ∀ x ∈ pi₀, D.Commutes e x) (_ : ∀ x ∈ pi₂, D.Commutes e x) :
    D.merge (D.applyList D.sigma0 pi₀) (D.do_ a e) (D.applyList D.sigma0 pi₂)
      = D.do_ (D.merge (D.applyList D.sigma0 pi₀) a
          (D.applyList D.sigma0 pi₂)) e := by
  change max (max a ↑(packed e)) (D.applyList D.sigma0 pi₂)
    = max (max a (D.applyList D.sigma0 pi₂)) ↑(packed e)
  simp [max_assoc, max_comm, max_left_comm]

/-- VC1, VC2, VC3, VC5 and the peel law. -/
theorem joinLaws : CanonicalJoinLaws D :=
  ⟨vc1_merge_comm, vc2_merge_init, vc3_local_redistribute,
   vc5_redistribute, commuting_peel⟩

/-- Everything the metatheory consumes. -/
theorem obligations : Obligations D :=
  ⟨all_commute, rc_either, joinLaws⟩

end LeanProofs.Implementations.LWWRegister
