import Sal.MRDTs.Paper1.GuardedRawModel
import Sal.MRDTs.Paper1.AbstractCompatibility
import Sal.MRDTs.Instances.LWWRegister

/-! LWW's existing timestamp-order policy violates no-chain. This is a
fixed-policy exclusion, not impossibility for every alternative payload policy:
its max-based concrete effectors commute and admit the empty guarded policy. -/
namespace Sal.MRDTs.Paper1.GuardedLWWExclusion
open Foundation Instances.LWWRegister

def SourceNoChain : Prop :=
  ∀ a b c : Op LWWOp, distinctOps (D := D.toUpdateSig) a b →
    distinctOps (D := D.toUpdateSig) b c →
    ¬ (rc.order a b = .Fst_then_snd ∧ rc.order b c = .Fst_then_snd)

theorem source_policy_excluded : ¬ SourceNoChain := by
  intro h
  exact h w₁ w₂ w₃ (by change 1 ≠ 2; decide) (by change 2 ≠ 3; decide) timestamp_chain

/-- Positive companion prevents interpreting the source-policy exclusion as
an impossibility theorem for the implementation under every possible policy. -/
theorem empty_policy_possible :
    GuardedReplay.Laws D.toUpdateSig (commutingPolicy D.AppOp) :=
  GuardedReplay.ofUniform (restricted_of_all_commute all_comm)

theorem control :
    distinctOps (D := D.toUpdateSig) w₁ w₂ ∧ w₁.rep ≠ w₂.rep ∧
    distinctOps (D := D.toUpdateSig) w₂ w₃ ∧ w₂.rep ≠ w₃.rep ∧
    (rc.order w₁ w₂ = .Fst_then_snd ∧ rc.order w₂ w₃ = .Fst_then_snd) ∧
    ¬ SourceNoChain :=
  ⟨by change 1 ≠ 2; decide, by decide, by change 2 ≠ 3; decide, by decide, timestamp_chain, source_policy_excluded⟩

end Sal.MRDTs.Paper1.GuardedLWWExclusion
