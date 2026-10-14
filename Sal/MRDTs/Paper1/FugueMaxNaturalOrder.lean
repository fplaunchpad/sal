import Sal.MRDTs.Paper1.FugueMaxProjectedVisibility
import Sal.MRDTs.Paper1.CertifiedFugueInvariant

/-! The natural witness respects the existing invariant-scoped implementation
order. This does not assert commutation on malformed, unsorted raw states. -/
namespace Sal.MRDTs.Paper1.FugueMaxNaturalOrder
open Foundation
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
open FugueMaxProjectedVisibility

theorem respects_order {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e) (π : List (Op Payload))
    (supported : ∀ e ∈ π, e ∈ C.events)
    (inv : KInv Γ (π.map recordOf)) (births : π.Pairwise BirthsFirst)
    (E : Set (Op Payload)) :
    respects π (InvariantOrder.order (CertifiedFugueInvariant.Valid Γ C.replayContext)
      CertifiedFugueVCReplay.policy C.replayContext E) := by
  apply births.imp_of_mem
  intro a b ha hb birthFirst edge
  rcases edge with ⟨causal,conflict⟩ | ⟨_,_,impossible,_⟩
  · have semantic : ¬ CertifiedFugueInvariant.SemanticCommutes b a :=
      fun h => conflict ((CertifiedFugueInvariant.invariant_commutes_iff Γ C mint trans
        b a (supported b hb) (supported a ha)).mpr h)
    cases ao : a.2.2.op <;> cases bo : b.2.2.op
    all_goals simp only [CertifiedFugueInvariant.SemanticCommutes,ao,bo] at semantic
    all_goals try exact semantic trivial
    case ins.del parent side target =>
      have same : a.time = target := Classical.not_not.mp semantic
      have positive := inv.pos (recordOf a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
      exact delete_before_own_birth_impossible C mint trans irrefl (birth := a) (deletion := b) (supported a ha)
        (supported b hb) (Nat.lt_of_lt_of_le (by decide : 0 < 1) positive)
        (by change b.2.2.op = .del a.time; simpa [same] using bo) causal
    case del.ins target parent side =>
      have bad := birthFirst (by simp [mIsIns,recordOf,ao])
      simp [mIsIns,recordOf,bo] at bad
  · exact impossible

#print axioms respects_order
end Sal.MRDTs.Paper1.FugueMaxNaturalOrder
