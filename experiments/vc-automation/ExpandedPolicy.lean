import InductivePolicy
import Sal.MRDTs.Paper1.GuardedORSet

/-! Policy bundles whose conditional field is obtained by equation induction,
without supplying a datatype-specific history invariant. -/
namespace NeemExpansion.Exact
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Paper1.ORSet
variable {α : Type} [DecidableEq α]

theorem expandedUniform : RestrictedLaws (D α).toUpdateSig (conflict α) := by
  constructor
  · intro a b
    simpa only [rc_iff, conflict, Op.op] using noncomm_iff_rc a b
  · rintro a b c ⟨⟨x, ha, hb⟩, ⟨y, hb', hc⟩⟩
    rw [hb] at hb'; cases hb'
  · intro s a b c between before nc
    obtain ⟨x, ha, hb⟩ := before
    have ord : (signature (α := α)).order a b = .Fst_then_snd := by
      change order a b = .Fst_then_snd
      rcases a with ⟨ta,ra,ao⟩; rcases b with ⟨tb,rb,bo⟩
      change ao = .remove x at ha
      change bo = .add x at hb
      subst ao; subst bo
      simp [order]
    exact (Signature.conditional_log (signature (α := α)) conditionalBase
      kernelStable s a b c ord nc between).symm

theorem expandedLaws : GuardedReplay.Laws (D α).toUpdateSig (conflict α) :=
  GuardedReplay.ofUniform expandedUniform
end NeemExpansion.Exact

namespace NeemExpansion.Efficient
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem expandedLaws : GuardedReplay.Laws (D α).toUpdateSig
    (EfficientORSet.EventSpec.conflict α) := by
  constructor
  · intro a b _ ne
    exact EfficientORSet.NeemScope.guarded_noncomm_exact a b ne
  · intro a b c _ _
    exact EfficientORSet.EventSpec.no_chain a.op b.op c.op
  · intro s a b c between _ _ _ before nc
    obtain ⟨x, ha, hb⟩ := before
    have ord : (signature (α := α)).order a b = .Fst_then_snd := by
      change (rc (α := α)).order a b = .Fst_then_snd
      rcases a with ⟨ta,ra,ao⟩; rcases b with ⟨tb,rb,bo⟩
      change ao = .remove x at ha
      change bo = .add x at hb
      subst ao; subst bo
      simp [rc]
    exact (Signature.conditional_log (signature (α := α)) conditionalBase
      kernelStable s a b c ord nc between).symm
end NeemExpansion.Efficient
