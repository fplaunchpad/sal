import LeanProofs.Implementations.GrowOnlySet.Definition
import LeanProofs.Interface.Laws

/-!
# The grow-only set: discharging the obligations

Each obligation is a set identity. Because `merge(l,a,b) = a union b` ignores
its base and `do` only inserts, every one reduces to commutativity,
associativity and idempotence of union.

Nothing here mentions configurations, executions, `lo^C_E`, `can`, or the
join lemma.
-/

namespace LeanProofs.Implementations.GrowOnlySet

open Artifact.MRDTs Artifact.MRDTs.Foundation LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- Two insertions commute, so by RC-NON-COMM `rc` is empty. -/
theorem all_commute (e₁ e₂ : (D A).Event) : (D A).Commutes e₁ e₂ := by
  intro S
  change Set A at S
  change insert e₂.op (insert e₁.op S) = insert e₁.op (insert e₂.op S)
  exact Set.insert_comm _ _ _

theorem rc_either (e₁ e₂ : (D A).Event) : (D A).RcEither e₁ e₂ := rfl

/-- **VC1** MERGE-COMM. -/
theorem vc1_merge_comm (l a b : (D A).Sigma) :
    (D A).merge l a b = (D A).merge l b a := by
  change Set A at l a b
  change a ∪ b = b ∪ a
  exact Set.union_comm _ _

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init (S : (D A).Sigma) :
    (D A).merge (D A).sigma0 (D A).sigma0 S = S := by
  change Set A at S
  change (∅ : Set A) ∪ S = S
  exact Set.empty_union _

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute (l m x c y : (D A).Sigma) :
    (D A).merge l ((D A).merge m x c) y = (D A).merge m ((D A).merge l x y) c := by
  change Set A at l m x c y
  change (x ∪ c) ∪ y = (x ∪ y) ∪ c
  ext z; simp only [Set.mem_union]; tauto

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute (m x₀ x₁ x₂ c : (D A).Sigma) :
    (D A).merge ((D A).merge m x₀ c) ((D A).merge m x₁ c) ((D A).merge m x₂ c)
      = (D A).merge m ((D A).merge x₀ x₁ x₂) c := by
  change Set A at m x₀ x₁ x₂ c
  change (x₁ ∪ c) ∪ (x₂ ∪ c) = (x₁ ∪ x₂) ∪ c
  ext z; simp only [Set.mem_union]; tauto

/-- The auxiliary peel law. The metatheory turns this into **VC4**
CAUSAL-DELTA. -/
theorem commuting_peel (a : (D A).Sigma) (e : (D A).Event)
    (pi₀ pi₂ : List (D A).Event)
    (_ : ∀ x ∈ pi₀, (D A).Commutes e x) (_ : ∀ x ∈ pi₂, (D A).Commutes e x) :
    (D A).merge ((D A).applyList (D A).sigma0 pi₀) ((D A).do_ a e)
        ((D A).applyList (D A).sigma0 pi₂)
      = (D A).do_ ((D A).merge ((D A).applyList (D A).sigma0 pi₀) a
          ((D A).applyList (D A).sigma0 pi₂)) e := by
  change Set A at a
  change insert e.op a ∪ (D A).applyList (D A).sigma0 pi₂
    = insert e.op (a ∪ (D A).applyList (D A).sigma0 pi₂)
  ext z; simp only [Set.mem_union, Set.mem_insert_iff]; tauto

/-- VC1, VC2, VC3, VC5 and the peel law. -/
theorem joinLaws : CanonicalJoinLaws (D A) :=
  ⟨vc1_merge_comm, vc2_merge_init, vc3_local_redistribute,
   vc5_redistribute, commuting_peel⟩

/-- Everything the metatheory consumes. -/
theorem obligations : Obligations (D A) :=
  ⟨all_commute, rc_either, joinLaws⟩

end LeanProofs.Implementations.GrowOnlySet
