import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeThreadDischarge

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

namespace Sal.ConditionedMRDTs.RGABranchInvFold

open Sal.Emulation
open RGAMergeLinearization (BranchInv branchInv_refl branchInv_triple_fold GoodBranchFold applySeqR
  contains_eq_domain)

/-- **`BranchInv l (applySeqR l Ea)` from a good branch fold.**  Reflexive base
(`branchInv_refl`) threaded through `Ea` by `branchInv_triple_fold`. Reduces `BranchInv` to the
per-op branch discipline `GoodBranchFold l l Ea` (+ `l`'s own well-formedness). -/
theorem branchInv_of_fold (l : concrete_st) (Ea : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hlR : RgaInv l)
    (hgf : GoodBranchFold l l Ea) :
    BranchInv l (applySeqR l Ea) :=
  (branchInv_triple_fold l hlwf hlmono Ea l hlR hlmono (branchInv_refl l hlwf) hgf).2.2

#print axioms branchInv_of_fold

/-- **≈-transport of `BranchInv`** (piece 3).  `BranchInv l` reads only `contains`/`el`/`anc`/`domain`
of its second argument, all of which `eq` preserves — so `BranchInv l a` transports along `eq a a'`.
This carries `BranchInv σ₀' (applySeqR σ₀' Ea)` (from the fold) onto the actual branch state `σ₁'`. -/
theorem branchInv_eq_transport (l a a' : concrete_st) (hbi : BranchInv l a) (heq : eq a a') :
    BranchInv l a' := by
  obtain ⟨hI2, hI4, hI3⟩ := hbi
  have hdom : domain a = domain a' := by
    funext k; rw [← contains_eq_domain, ← contains_eq_domain]; exact (heq k).1
  refine ⟨?_, ?_, ?_⟩
  · intro k hlk ha'k
    have hak : contains a k = true := by rw [(heq k).1]; exact ha'k
    have hsel : sel a k = sel a' k := (heq k).2 hak
    have hel : el a' k = el a k := by simp only [el, hsel]
    rw [hel]; exact hI2 k hlk hak
  · intro k hlk ha'k
    have hak : contains a k = true := by rw [(heq k).1]; exact ha'k
    have hsel : sel a k = sel a' k := (heq k).2 hak
    have hanc : anc a' k = anc a k := by simp only [anc, hsel]
    rw [hanc, ← hdom]; exact hI4 k hlk hak
  · intro k hlk ha'k
    have hak : contains a k = true := by rw [(heq k).1]; exact ha'k
    have hsel : sel a k = sel a' k := (heq k).2 hak
    have hanc : anc a' k = anc a k := by simp only [anc, hsel]
    rw [hanc]; exact hI3 k hlk hak

#print axioms branchInv_eq_transport

/-- **`BranchInv l σ₁'` from a good fold + the branch-decomposition** — the (B) assembly.  Combines
the fold (`branchInv_of_fold`) with the decomposition `eq (applySeqR l Ea) σ₁'` via ≈-transport. What
remains for an unconditional `BranchInv σ₀' σ₁'` is exactly these two inputs: `GoodBranchFold l l Ea`
(the per-op branch discipline) and the decomposition equality. -/
theorem branchInv_of_decomp (l σ₁' : concrete_st) (Ea : List op_t)
    (hlwf : wf l) (hlmono : id_mono l) (hlR : RgaInv l)
    (hgf : GoodBranchFold l l Ea)
    (hdecomp : eq (applySeqR l Ea) σ₁') :
    BranchInv l σ₁' :=
  branchInv_eq_transport l (applySeqR l Ea) σ₁' (branchInv_of_fold l Ea hlwf hlmono hlR hgf) hdecomp

#print axioms branchInv_of_decomp

end Sal.ConditionedMRDTs.RGABranchInvFold
