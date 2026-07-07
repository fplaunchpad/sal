import Sal.ConditionedMRDTs.Development.RGA_BranchInv_Fold
import Sal.ConditionedMRDTs.Development.RGA_NoopFeasible_CanonFold

/-!
# Branch-decomposition — (B) piece (2), and the full `BranchInv` reduction

*Additive; modifies no existing file; 0 `sorry`.*

The branch-a fold `σ₁' = applySeqR init_st ρ₁` and the LCA-fold-then-branch-a-δ `applySeqR σ₀' Ea =
applySeqR init_st (ρ₀ ++ Ea)` both enumerate branch a's event set `E = ev₁`, so they converge by the
GenDisc-free update convergence (`RGA_update_convergence_noop`). `branchDecomp_of_enum` packages that
equality; `branchInv_of_enum` composes it with `branchInv_of_decomp` (RGA_BranchInv_Fold), giving

    BranchInv σ₀' σ₁'   from   GoodBranchFold σ₀' σ₀' Ea + wf/id_mono/RgaInv σ₀'
                              + the two enumerations' reachability facts.

So `BranchInv` now rests only on execution/reachability facts shared with `hReady`/`hEnum`.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGABranchDecomp

open Sal.Emulation
open RGANoopFeasible (RGA_update_convergence_noop RefEdge)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpGenQ)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open RGAMergeLinearization (applySeqR BranchInv GoodBranchFold)
open Sal.ConditionedMRDTs.RGABranchInvFold (branchInv_of_decomp)

/-- **The branch-decomposition** (piece 2).  `applySeqR σ₀' Ea ≈ σ₁'` for `σ₀' = applySeqR init_st ρ₀`,
`σ₁' = applySeqR init_st ρ₁`: `ρ₀ ++ Ea` and `ρ₁` are two born-applicable, `R`-respecting enumerations
of the same branch event set `E`, hence converge (`RGA_update_convergence_noop`). -/
theorem branchDecomp_of_enum (ρ₀ Ea ρ₁ : List op_t) (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RefEdge E R)
    (hperm_a : listPermOf (ρ₀ ++ Ea) E) (hperm_1 : listPermOf ρ₁ E)
    (hresp_a : respects (ρ₀ ++ Ea) R) (hresp_1 : respects ρ₁ R)
    (hnf_a : noopFeasible RGACondSig (ρ₀ ++ Ea) init_st)
    (hnf_1 : noopFeasible RGACondSig ρ₁ init_st) :
    eq (applySeqR (applySeqR init_st ρ₀) Ea) (applySeqR init_st ρ₁) := by
  have h := RGA_update_convergence_noop E R hdts hids0 hgen href (ρ₀ ++ Ea) ρ₁
    hperm_a hperm_1 hresp_a hresp_1 hnf_a hnf_1
  rwa [show applySeqR init_st (ρ₀ ++ Ea) = applySeqR (applySeqR init_st ρ₀) Ea from by
    simp only [applySeqR, List.foldl_append]] at h

#print axioms branchDecomp_of_enum

/-- **`BranchInv σ₀' σ₁'` from the branch enumerations** — the full (B) reduction.  Composes
`branchInv_of_decomp` (fold + ≈-transport) with `branchDecomp_of_enum` (convergence). Reduces
`BranchInv σ₀' σ₁'` to: `GoodBranchFold σ₀' σ₀' Ea` (the per-op branch discipline) and the two
enumerations' reachability facts (perm/respects/born-applicable + generation) — all execution-model
inputs. Everything structural (threading, base, ≈-transport, convergence) is discharged. -/
theorem branchInv_of_enum (ρ₀ Ea ρ₁ : List op_t) (E : Set op_t) (R : op_t → op_t → Prop)
    (hlwf : wf (applySeqR init_st ρ₀)) (hlmono : id_mono (applySeqR init_st ρ₀))
    (hlR : RgaInv (applySeqR init_st ρ₀))
    (hgf : GoodBranchFold (applySeqR init_st ρ₀) (applySeqR init_st ρ₀) Ea)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RefEdge E R)
    (hperm_a : listPermOf (ρ₀ ++ Ea) E) (hperm_1 : listPermOf ρ₁ E)
    (hresp_a : respects (ρ₀ ++ Ea) R) (hresp_1 : respects ρ₁ R)
    (hnf_a : noopFeasible RGACondSig (ρ₀ ++ Ea) init_st)
    (hnf_1 : noopFeasible RGACondSig ρ₁ init_st) :
    BranchInv (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) :=
  branchInv_of_decomp (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) Ea hlwf hlmono hlR hgf
    (branchDecomp_of_enum ρ₀ Ea ρ₁ E R hdts hids0 hgen href
      hperm_a hperm_1 hresp_a hresp_1 hnf_a hnf_1)

#print axioms branchInv_of_enum

end Sal.ConditionedMRDTs.RGABranchDecomp
