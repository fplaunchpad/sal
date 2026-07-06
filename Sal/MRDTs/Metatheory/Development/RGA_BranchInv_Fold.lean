import Sal.MRDTs.Metatheory.Development.RGA_MergeThreadDischarge

/-!
# `BranchInv` from a good branch fold — the start of (B)

*Additive; modifies no existing file; 0 `sorry`.*

The threading is already proved (`RGAMergeLinearization.branchInv_triple_fold`): `BranchInv l` is
preserved along a `GoodBranchFold`. Starting from the reflexive base `branchInv_refl : BranchInv l l`,
this gives `BranchInv l (applySeqR l Ea)` directly. So the σ₀'↔σ₁' relation `BranchInv σ₀' σ₁'` reduces
(via the branch-decomposition `σ₁' ≈ applySeqR σ₀' Ea` + ≈-transport, still to do) to a `GoodBranchFold
σ₀' σ₀' Ea` — the per-op reachability discipline on branch a's δ-events (each `accurate`/`fresh`/
`mono_alloc`/fresh-in-`l`), which the honest execution supplies.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.Metatheory.RGABranchInvFold

open Sal.Emulation
open RGAMergeLinearization (BranchInv branchInv_refl branchInv_triple_fold GoodBranchFold applySeqR)

/-- **`BranchInv l (applySeqR l Ea)` from a good branch fold.**  Reflexive base
(`branchInv_refl`) threaded through `Ea` by `branchInv_triple_fold`. Reduces `BranchInv` to the
per-op branch discipline `GoodBranchFold l l Ea` (+ `l`'s own well-formedness). -/
theorem branchInv_of_fold (l : concrete_st) (Ea : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hlR : RgaInv l)
    (hgf : GoodBranchFold l l Ea) :
    BranchInv l (applySeqR l Ea) :=
  (branchInv_triple_fold l hlwf hlmono Ea l hlR hlmono (branchInv_refl l hlwf) hgf).2.2

#print axioms branchInv_of_fold

end Sal.Metatheory.RGABranchInvFold
