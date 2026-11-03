import LeanProofs.Implementations.FlatGrowOnlyMap.Definition
import LeanProofs.Interface.Laws

/-!
# The flat grow-only map: discharging the obligations

Both `do` and `merge` are pointwise Boolean disjunctions, so every obligation
reduces to associativity, commutativity and idempotence of `or` at each point.

Nothing here mentions configurations, executions, `lo^C_E`, `can`, or the
join lemma.
-/

namespace LeanProofs.Implementations.FlatGrowOnlyMap

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- Two insertions commute, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : (D A).Event) : (D A).Commutes e₁ e₂ := by
  intro S
  change (fun x => (S x || decide (x = e₁.op)) || decide (x = e₂.op))
    = (fun x => (S x || decide (x = e₂.op)) || decide (x = e₁.op))
  funext x
  cases S x <;> cases decide (x = e₁.op) <;> cases decide (x = e₂.op) <;> rfl

theorem rc_either (e₁ e₂ : (D A).Event) : (D A).RcEither e₁ e₂ := rfl

/-- **VC1** MERGE-COMM. -/
theorem vc1_merge_comm (l a b : (D A).Sigma) :
    (D A).merge l a b = (D A).merge l b a := by
  change (fun x => l x || a x || b x) = (fun x => l x || b x || a x)
  funext x; cases l x <;> cases a x <;> cases b x <;> rfl

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init (S : (D A).Sigma) :
    (D A).merge (D A).sigma0 (D A).sigma0 S = S := by
  change (fun x => (false || false) || S x) = S
  funext x; cases S x <;> rfl

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute (l m x c y : (D A).Sigma) :
    (D A).merge l ((D A).merge m x c) y = (D A).merge m ((D A).merge l x y) c := by
  change (fun z => l z || (m z || x z || c z) || y z)
    = (fun z => m z || (l z || x z || y z) || c z)
  funext z
  cases l z <;> cases m z <;> cases x z <;> cases c z <;> cases y z <;> rfl

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute (m x₀ x₁ x₂ c : (D A).Sigma) :
    (D A).merge ((D A).merge m x₀ c) ((D A).merge m x₁ c) ((D A).merge m x₂ c)
      = (D A).merge m ((D A).merge x₀ x₁ x₂) c := by
  change (fun z => (m z || x₀ z || c z) || (m z || x₁ z || c z) || (m z || x₂ z || c z))
    = (fun z => m z || (x₀ z || x₁ z || x₂ z) || c z)
  funext z
  cases m z <;> cases x₀ z <;> cases x₁ z <;> cases x₂ z <;> cases c z <;> rfl

/-- The auxiliary peel law. The metatheory turns this into **VC4**
CAUSAL-DELTA. -/
theorem commuting_peel (a : (D A).Sigma) (e : (D A).Event)
    (pi₀ pi₂ : List (D A).Event)
    (_ : ∀ x ∈ pi₀, (D A).Commutes e x) (_ : ∀ x ∈ pi₂, (D A).Commutes e x) :
    (D A).merge ((D A).applyList (D A).sigma0 pi₀) ((D A).do_ a e)
        ((D A).applyList (D A).sigma0 pi₂)
      = (D A).do_ ((D A).merge ((D A).applyList (D A).sigma0 pi₀) a
          ((D A).applyList (D A).sigma0 pi₂)) e := by
  set P₀ := (D A).applyList (D A).sigma0 pi₀ with hP₀
  set P₂ := (D A).applyList (D A).sigma0 pi₂ with hP₂
  change (fun x => P₀ x || (a x || decide (x = e.op)) || P₂ x)
    = (fun x => (P₀ x || a x || P₂ x) || decide (x = e.op))
  funext x
  cases P₀ x <;> cases a x <;> cases P₂ x <;> cases decide (x = e.op) <;> rfl

/-- VC1, VC2, VC3, VC5 and the peel law. -/
theorem joinLaws : CanonicalJoinLaws (D A) :=
  ⟨vc1_merge_comm, vc2_merge_init, vc3_local_redistribute,
   vc5_redistribute, commuting_peel⟩

/-- Everything the metatheory consumes. -/
theorem obligations : Obligations (D A) :=
  ⟨all_commute, rc_either, joinLaws⟩

end LeanProofs.Implementations.FlatGrowOnlyMap
