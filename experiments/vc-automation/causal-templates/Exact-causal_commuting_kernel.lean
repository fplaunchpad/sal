import InductiveLeaves

/-! Supplementary finite equations required by Sal's metadata histories.
These are NEW obligations, not members of Neem's exact 21-equation inventory.
They admit same-replica commuting pairs, which can arise when concrete metadata
omits commuting causal predecessors. Proofs use only operation unfolding and
collection membership; no history invariant or production VC is reused. -/
namespace NeemExpansion.Signature
open Sal.MRDTs.Foundation

def Commutes (D : Signature) (p q : Op D.AppOp) : Prop :=
  ∀ s, D.step (D.step s p) q = D.step (D.step s q) p

def base2_commuting (D : Signature) : Prop := ∀ l p q,
  D.distinct p q → D.Commutes p q → D.Q2 l l l p q

def left_suffix_commuting (D : Signature) : Prop := ∀ l a b p q o,
  D.distinct p q → D.Commutes p q →
  D.Q2 l a b p q → D.Q2 l (D.step a o) b p q
def causal_common_kernel (D : Signature) : Prop := ∀ B s e h,
  D.merge B s (D.step B e) = D.step s e →
  D.merge (D.step B h) (D.step s h) (D.step (D.step B h) e) =
    D.step (D.step s h) e

def causal_commuting_kernel (D : Signature) : Prop := ∀ B s e q,
  D.Commutes e q → D.merge B s (D.step B e) = D.step s e →
  D.merge B (D.step s q) (D.step B e) = D.step (D.step s q) e

def causal_absorber_kernel (D : Signature) : Prop := ∀ B s e q p,
  D.order e p = .Fst_then_snd → D.order q p = .Fst_then_snd →
  D.merge B (D.step s q) (D.step B e) = D.step (D.step s q) e

end NeemExpansion.Signature

namespace NeemExpansion.Exact
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1.ORSet
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem trial : (signature (α := α)).causal_commuting_kernel := by
  intro B s e q commutes ih
  have hc := commutes (∅ : State α)
  dsimp [signature] at ih ⊢
  rcases e with ⟨et, er, eo⟩; rcases q with ⟨qt, qr, qo⟩
  cases eo <;> cases qo <;> ext x <;>
    have hi := Finset.ext_iff.mp ih x <;>
    have he := Finset.ext_iff.mp hc x <;>
    simp [signature, merge, step] at *
  -- SOLVER
end NeemExpansion.Exact
