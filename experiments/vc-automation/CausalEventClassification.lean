import Sal.MRDTs.Paper1.ORSet
import Sal.MRDTs.Instances.EfficientORSet

/-! New finite operation classification proofs for causal reset coverage.
Only operation constructors, implementation definitions, finite-set algebra,
and the empty-state noncommutation witness are used. -/
namespace CausalEventClassification
open Sal.MRDTs.Foundation

namespace Exact
open Sal.MRDTs.Paper1.ORSet
variable {α : Type} [DecidableEq α]
def element : Update α → α
  | .add x | .remove x => x

theorem commute_distinct_elements (a b : Op (Update α))
    (ne : element a.2.2 ≠ element b.2.2) : (D α).toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> dsimp [D] <;> ext p <;> simp [D,step,element] at * <;> grind

theorem conflict_classification (a b : Op (Update α))
    (nc : ¬ (D α).toUpdateSig.commutes a b) :
    order a b = .Fst_then_snd ∨ order b a = .Fst_then_snd ∨ a.rep = b.rep := by
  by_contra hn
  apply nc
  intro s
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> dsimp [D] <;> ext p <;> simp [D,step,order,Op.rep] at * <;> grind

theorem remove_add_noncomm (et er ct cr : Nat) (x : α) :
    ¬ (D α).toUpdateSig.commutes (et,er,.remove x) (ct,cr,.add x) := by
  intro hc
  have h := hc (∅ : State α)
  have hp := Finset.ext_iff.mp h (x,ct)
  simp [D,step] at hp

theorem absorber_classification (e h c : Op (Update α))
    (prior : order e h = .Fst_then_snd)
    (nc : ¬ (D α).toUpdateSig.commutes h c) :
    order c h = .Fst_then_snd ∨
      (order e c = .Fst_then_snd ∧ ¬ (D α).toUpdateSig.commutes e c) := by
  rcases e with ⟨et,er,eo⟩; rcases h with ⟨ht,hr,ho⟩; rcases c with ⟨ct,cr,co⟩
  cases eo <;> cases ho <;> simp [order,ite_eq_iff] at prior
  rename_i x y
  subst y
  cases co with
  | add z =>
    by_cases eq : x = z
    · subst z
      exact Or.inr ⟨by simp [order],remove_add_noncomm et er ct cr x⟩
    · exact False.elim (nc (commute_distinct_elements _ _ eq))
  | remove z =>
    by_cases eq : z = x
    · subst z; exact Or.inl (by simp [order])
    · exact False.elim (nc (commute_distinct_elements _ _ (Ne.symm eq)))

theorem strict_asymmetric (a b : Op (Update α)) (prior : order a b = .Fst_then_snd) :
    order b a ≠ .Fst_then_snd := by
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> simp_all [order,ite_eq_iff]
end Exact

namespace Efficient
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]
def element : SetOp α → α
  | .add x | .remove x => x

theorem commute_distinct_elements (a b : Op (SetOp α))
    (ne : element a.2.2 ≠ element b.2.2) : (D α).toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> dsimp [D] <;> ext p <;> simp [D,update,element] at * <;> grind

theorem conflict_classification (a b : Op (SetOp α))
    (nc : ¬ (D α).toUpdateSig.commutes a b) :
    rc.order a b = .Fst_then_snd ∨ rc.order b a = .Fst_then_snd ∨ a.rep = b.rep := by
  by_contra hn
  apply nc
  intro s
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> dsimp [D] <;> ext p <;> simp [D,update,rc,Op.rep] at * <;> grind

theorem remove_add_noncomm (et er ct cr : Nat) (x : α) :
    ¬ (D α).toUpdateSig.commutes (et,er,.remove x) (ct,cr,.add x) := by
  intro hc
  have h := hc (∅ : State α)
  have hp := Finset.ext_iff.mp h (cr,ct,x)
  simp [D,update] at hp

theorem absorber_classification (e h c : Op (SetOp α))
    (prior : rc.order e h = .Fst_then_snd)
    (nc : ¬ (D α).toUpdateSig.commutes h c) :
    rc.order c h = .Fst_then_snd ∨
      (rc.order e c = .Fst_then_snd ∧ ¬ (D α).toUpdateSig.commutes e c) := by
  rcases e with ⟨et,er,eo⟩; rcases h with ⟨ht,hr,ho⟩; rcases c with ⟨ct,cr,co⟩
  cases eo <;> cases ho <;> simp [rc,ite_eq_iff] at prior
  rename_i x y
  subst y
  cases co with
  | add z =>
    by_cases eq : x = z
    · subst z
      exact Or.inr ⟨by simp [rc],remove_add_noncomm et er ct cr x⟩
    · exact False.elim (nc (commute_distinct_elements _ _ eq))
  | remove z =>
    by_cases eq : z = x
    · subst z; exact Or.inl (by simp [rc])
    · exact False.elim (nc (commute_distinct_elements _ _ (Ne.symm eq)))

theorem strict_asymmetric (a b : Op (SetOp α)) (prior : rc.order a b = .Fst_then_snd) :
    rc.order b a ≠ .Fst_then_snd := by
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> simp_all [rc,ite_eq_iff]
end Efficient
end CausalEventClassification
