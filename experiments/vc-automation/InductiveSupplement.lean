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

theorem base2_commuting : (signature (α := α)).base2_commuting := by
  intro l p q fresh commutes
  have hc := commutes (∅ : State α)
  rcases p with ⟨tp, rp, po⟩; rcases q with ⟨tq, rq, qo⟩
  cases po <;> cases qo <;> dsimp [Signature.Q2, signature] at * <;> ext x <;>
    have he := Finset.ext_iff.mp hc x <;>
    simp [Signature.distinct, signature, merge, step] at * <;>
    grind (splits := 20)

theorem left_suffix_commuting : (signature (α := α)).left_suffix_commuting := by
  intro l a b p q o hpq commutes ih
  have hc := commutes (∅ : State α)
  dsimp [Signature.Q2, signature] at ih ⊢
  rcases p with ⟨tp, rp, po⟩; rcases q with ⟨tq, rq, qo⟩
  rcases o with ⟨ots, ro, oo⟩
  cases po <;> cases qo <;> cases oo <;> ext x <;>
    have he := Finset.ext_iff.mp hc x <;>
    have hi := Finset.ext_iff.mp ih x <;>
    simp [Signature.distinct, signature, merge, step] at * <;>
    grind (splits := 20)
theorem causal_common_kernel : (signature (α := α)).causal_common_kernel := by
  intro B s e h ih
  dsimp [signature] at ih ⊢
  rcases e with ⟨et, er, eo⟩; rcases h with ⟨ht, hr, ho⟩
  cases eo <;> cases ho <;> ext x <;>
    have hi := Finset.ext_iff.mp ih x <;>
    simp [merge, step] at * <;> grind (splits := 20)

theorem causal_commuting_kernel : (signature (α := α)).causal_commuting_kernel := by
  intro B s e q commutes ih
  have hc := commutes (∅ : State α)
  dsimp [signature] at ih ⊢
  rcases e with ⟨et, er, eo⟩; rcases q with ⟨qt, qr, qo⟩
  cases eo <;> cases qo <;> ext x <;>
    have hi := Finset.ext_iff.mp ih x <;>
    have he := Finset.ext_iff.mp hc x <;>
    simp [signature, merge, step] at * <;> grind (splits := 20)

theorem causal_absorber_kernel : (signature (α := α)).causal_absorber_kernel := by
  intro B s e q p hep hqp
  dsimp [signature] at *
  rcases e with ⟨et, er, eo⟩; rcases q with ⟨qt, qr, qo⟩
  rcases p with ⟨pt, pr, po⟩
  cases eo <;> cases qo <;> cases po <;> ext x <;>
    simp [order, merge, step] at * <;> grind (splits := 20)

end NeemExpansion.Exact

namespace NeemExpansion.Efficient
open Sal.MRDTs.Foundation Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem base2_commuting : (signature (α := α)).base2_commuting := by
  intro l p q fresh commutes
  have hc := commutes (∅ : State α)
  rcases p with ⟨tp, rp, po⟩; rcases q with ⟨tq, rq, qo⟩
  cases po <;> cases qo <;> dsimp [Signature.Q2, signature] at * <;> ext x <;>
    have he := Finset.ext_iff.mp hc x <;>
    simp [Signature.distinct, signature, merge, update] at * <;>
    grind (splits := 20)

theorem left_suffix_commuting : (signature (α := α)).left_suffix_commuting := by
  intro l a b p q o hpq commutes ih
  have hc := commutes (∅ : State α)
  dsimp [Signature.Q2, signature] at ih ⊢
  rcases p with ⟨tp, rp, po⟩; rcases q with ⟨tq, rq, qo⟩
  rcases o with ⟨ots, ro, oo⟩
  cases po <;> cases qo <;> cases oo <;> ext x <;>
    have he := Finset.ext_iff.mp hc x <;>
    have hi := Finset.ext_iff.mp ih x <;>
    simp [Signature.distinct, signature, merge, update] at * <;>
    grind (splits := 20)
theorem causal_common_kernel : (signature (α := α)).causal_common_kernel := by
  intro B s e h ih
  dsimp [signature] at ih ⊢
  rcases e with ⟨et, er, eo⟩; rcases h with ⟨ht, hr, ho⟩
  cases eo <;> cases ho <;> ext x <;>
    have hi := Finset.ext_iff.mp ih x <;>
    simp [merge, update] at * <;> grind (splits := 20)

theorem causal_commuting_kernel : (signature (α := α)).causal_commuting_kernel := by
  intro B s e q commutes ih
  have hc := commutes (∅ : State α)
  dsimp [signature] at ih ⊢
  rcases e with ⟨et, er, eo⟩; rcases q with ⟨qt, qr, qo⟩
  cases eo <;> cases qo <;> ext x <;>
    have hi := Finset.ext_iff.mp ih x <;>
    have he := Finset.ext_iff.mp hc x <;>
    simp [signature, merge, update] at * <;> grind (splits := 20)

theorem causal_absorber_kernel : (signature (α := α)).causal_absorber_kernel := by
  intro B s e q p hep hqp
  dsimp [signature] at *
  rcases e with ⟨et, er, eo⟩; rcases q with ⟨qt, qr, qo⟩
  rcases p with ⟨pt, pr, po⟩
  cases eo <;> cases qo <;> cases po <;> ext x <;>
    simp [rc, merge, update] at * <;> grind (splits := 20)

end NeemExpansion.Efficient

namespace NeemExpansion.Signature
open Sal.MRDTs.Foundation

/-- The new commuting suffix leaf lifts to arbitrary inserted histories. No
freshness is needed for inserted events: the finite kernel proves this stronger
schema directly. Frozen p/q timestamps remain distinct. -/
theorem commuting_left_log (D : Signature) (law : D.left_suffix_commuting)
    (l a b : D.State) (p q : Op D.AppOp) (fresh : D.distinct p q)
    (commutes : D.Commutes p q) (base : D.Q2 l a b p q)
    (π : List (Op D.AppOp)) : D.Q2 l (π.foldl D.step a) b p q := by
  induction π using List.reverseRecOn with
  | nil => exact base
  | append_singleton π h ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact law l (π.foldl D.step a) b p q h fresh commutes ih

/-- Kernel-checked causal coverage for an arbitrary common state and arbitrary
local suffix whose events commute with the frozen e. Same-replica commuting
predecessors are covered; no causal/Join IH or history invariant is assumed. -/
theorem causal_commuting_suffix (D : Signature)
    (b2 : D.base2_commuting) (left : D.left_suffix_commuting) (comm : D.comm)
    (diagonal : ∀ l a, D.merge l a l = a)
    (B : D.State) (e : Op D.AppOp) (π : List (Op D.AppOp)) :
    (∀ q ∈ π, D.distinct e q ∧ D.Commutes e q) →
    D.merge B (π.foldl D.step B) (D.step B e) =
      D.step (π.foldl D.step B) e := by
  induction π using List.reverseRecOn with
  | nil =>
      intro _
      simp only [List.foldl_nil]
      rw [comm B B _, diagonal]
  | append_singleton π q ih =>
      intro guards
      have previous := ih (fun h hh => guards h (List.mem_append_left [q] hh))
      have gq := guards q (by simp)
      have distinct : D.distinct q e := Ne.symm gq.1
      have commutes : D.Commutes q e := fun s => (gq.2 s).symm
      have start := b2 B q e distinct commutes
      have equation := D.commuting_left_log left B B B q e distinct commutes start π
      change D.merge B (D.step (π.foldl D.step B) q) (D.step B e) =
        D.step (D.merge B (π.foldl D.step B) (D.step B e)) q at equation
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [equation, previous]
      exact gq.2 (π.foldl D.step B)

end NeemExpansion.Signature

namespace NeemExpansion.Signature
open Sal.MRDTs.Foundation

/-- A generic equation-construction certificate for causal history pairs.
This is not a datatype invariant: its constructors are precisely finite
synchronized-history steps and a frozen-absorber reset. A representation
adapter must still construct this evidence, or an equivalent stronger one. -/
inductive CausalHistory (D : Signature) (e : Op D.AppOp) : D.State → D.State → Prop
  | diagonal (B) : CausalHistory D e B B
  | common {B s} (h) : CausalHistory D e B s →
      CausalHistory D e (D.step B h) (D.step s h)
  | local_commuting {B s} (q) : D.Commutes e q → CausalHistory D e B s →
      CausalHistory D e B (D.step s q)
  | absorber (B s q p) : D.order e p = .Fst_then_snd →
      D.order q p = .Fst_then_snd → CausalHistory D e B (D.step s q)

theorem CausalHistory.sound (D : Signature) (comm : D.comm)
    (diagonal : ∀ l a, D.merge l a l = a)
    (common : D.causal_common_kernel) (localStep : D.causal_commuting_kernel)
    (absorber : D.causal_absorber_kernel) (e : Op D.AppOp)
    {B s : D.State} (history : D.CausalHistory e B s) :
    D.merge B s (D.step B e) = D.step s e := by
  induction history with
  | diagonal B => rw [comm B B _, diagonal]
  | common h _ ih => exact common _ _ e h ih
  | local_commuting q commute _ ih => exact localStep _ _ e q commute ih
  | absorber B s q p hep hqp => exact absorber B s e q p hep hqp

/-- Arbitrarily interleaved synchronized common events are kernel sound,
including noncommuting common predecessors of the frozen event. -/
theorem causal_common_log (D : Signature) (kernel : D.causal_common_kernel)
    (B s : D.State) (e : Op D.AppOp)
    (equation : D.merge B s (D.step B e) = D.step s e)
    (π : List (Op D.AppOp)) :
    D.merge (π.foldl D.step B) (π.foldl D.step s)
      (D.step (π.foldl D.step B) e) = D.step (π.foldl D.step s) e := by
  induction π using List.reverseRecOn with
  | nil => exact equation
  | append_singleton π h ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact kernel _ _ e h ih

end NeemExpansion.Signature
