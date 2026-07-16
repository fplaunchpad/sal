import Sal.ConditionedMRDTs.Development.RGA_EqJoin_NF_Residual
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeLinearization
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate

/-!
# End-to-end RGA `≈`-linearizability via the canonical route, modulo an explicit residual

*Additive; modifies no existing file; 0 `sorry` (residual carried as explicit hypotheses).*

**The correction (see the conversation with KC).** The whole point of the framework is to minimise
per-RDT proof work; the earlier six-piece route (`eq_merge_two_sided_final` with the swap oracle
`hMSR` and `BranchInv` threading `hB`) was NOT that — those were artifacts of proving merge=fold by
*interleave swaps*. The framework's own canonical engine gives merge=fold for free from a single
per-RDT fact:

* `RGACanonConvergence.canon_fold` → `CanonMatch F (fold)` — "a disciplined fold IS the canonical
  state of its event set." GENERIC.
* `RGACanonConvergence.eq_of_canonMatch2` — canonical-state UNIQUENESS. GENERIC.

So `eq (merge σ₀' σ₁' σ₂') (applySeqR σ₀' π₀)` is just `eq_of_canonMatch2` fed the merge's and the
fold's `CanonMatch`. No swaps, no `BranchInv`.

**The residual, plugged end-to-end (bottom-up meets top-down).** We admit the RGA-specific facts as
EXPLICIT hypotheses and wire the generic chain through them, so `RgaEqJoinResidualLit` → (existing,
proved) `rga_eqJoin_of_residualLit_NF` → `EqJoinLemma3C_NF` → (existing, proved)
`rga_RA_linearizable_NF` → `IsRALinearizable3` all typecheck. Two hypotheses:

* `hEnum` — a canonical δ-enum exists. GENERIC (born-applicable delivery; not RGA-specific content).
* `hCanon` — the merge and the δ-fold are BOTH the canonical state of `ρ₀ ++ π₀`. The FOLD half is
  generic (`canon_fold`); the MERGE half `CanonMatch F (merge …)` is the sole irreducible RGA fact —
  "the RGA merge computes the canonical state of the union" — which reduces (mechanized:
  `canonBirthBridge_via_branchCanon` → `hin_of_survFilterEq`) to the crisp subsequence equality
  `hFiltEq : rcSuf.filter (survB F) = cw.filter (survB F)` (`RGA_BranchCanon`). That `hFiltEq` is the
  genuine two-sided reconstruction semantics of the RGA — NOT derivable from any single branch's
  `CanonMatch`, NOT removable by framework generality. It is THE residual.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGAEqJoinNF

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient (loOnEq EqJoinLemma3C_NF fullClosureRel)
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv')
open Sal.ConditionedMRDTs (noopFeasible)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch eq_of_canonMatch2)
open Sal.ConditionedMRDTs.RGAConditionedConvergence (applySeqR_append)

/-- **`RgaEqJoinResidualLit` via the canonical route.**  Reduces the merge=fold identity to:
`hEnum` (a canonical δ-enum exists — generic delivery) and `hCanon` (merge and δ-fold are both the
canonical state of `ρ₀ ++ π₀` — the fold half generic `canon_fold`, the merge half the RGA residual).
Merge=fold is then `eq_of_canonMatch2` verbatim — NO swap oracle, NO `BranchInv`. Context fully
threaded (both hypotheses receive every `RgaEqJoinResidualLit` premise). -/
theorem rgaResidualLit_of_canon (W : op_t → concrete_st → Prop)
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' W vis (ev₁ ∩ ev₂)) →
          noopFeasible RGACondSig' ρ₀ init_st →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' W vis ev₁) →
          noopFeasible RGACondSig' ρ₁ init_st →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' W vis ev₂) →
          noopFeasible RGACondSig' ρ₂ init_st →
        ∃ π₀ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀))
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀)) :
    RgaEqJoinResidualLit W := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ htr hir hdts hev1 hev2 hcl1 hcl2
    h₀p h₀r hnf₀ h₁p h₁r hnf₁ h₂p h₂r hnf₂
  obtain ⟨π₀, hπp, hπr, hnfπ⟩ :=
    hEnum vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ htr hir hev1 hev2 hcl1 hcl2
      h₀p h₀r hnf₀ h₁p h₁r hnf₁ h₂p h₂r hnf₂
  obtain ⟨hCMmerge, hCMfold⟩ :=
    hCanon vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2
      h₀p h₁p h₂p hπp hπr hnfπ
  exact ⟨π₀, hπp, hπr, hnfπ,
    eq_of_canonMatch2 (ρ₀ ++ π₀) (ρ₀ ++ π₀) _ _ (fun _ => Iff.rfl) hCMmerge hCMfold⟩

/-- **`EqJoinLemma3C_NF` for the RGA, via the canonical route.**  Composes with the proved
`rga_eqJoin_of_residualLit_NF`. The RGA's datatype merge VC follows from `hEnum` + `hCanon`. -/
theorem rga_eqJoinNF_of_canon (W : op_t → concrete_st → Prop)
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' W vis (ev₁ ∩ ev₂)) →
          noopFeasible RGACondSig' ρ₀ init_st →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' W vis ev₁) →
          noopFeasible RGACondSig' ρ₁ init_st →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' W vis ev₂) →
          noopFeasible RGACondSig' ρ₂ init_st →
        ∃ π₀ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀))
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' W vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀)) :
    EqJoinLemma3C_NF RGACondSig' rgaEqEquiv' W :=
  rga_eqJoin_of_residualLit_NF W (rgaResidualLit_of_canon W hEnum hCanon)

/-! `rga_eqJoinNF_of_canon WfOpA hEnum hCanon` plugs directly into the first argument of
`Sal.ConditionedMRDTs.RGAInstanceNF.rga_RA_linearizable_NF` (`hJoinNF : EqJoinLemma3C_NF … WfOpA`), giving
RGA RA-linearizability up to `≈` gated ONLY on `hEnum` (generic delivery) + `hCanon` (fold half
generic `canon_fold`; merge half = the RGA residual, reducing to `hFiltEq`) + the legitimate
honest-execution hyps `hBA`/`hReach`/`hgenW`. NO swap oracle, NO `BranchInv`, NO `GenDisc2CEq`.

## Axiom audit -/

#print axioms rgaResidualLit_of_canon
#print axioms rga_eqJoinNF_of_canon

end Sal.ConditionedMRDTs.RGAEqJoinNF
