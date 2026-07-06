import Sal.MRDTs.Metatheory.Development.RGA_EndToEnd
import Sal.MRDTs.Metatheory.Development.RGA_MergeCanon

/-!
# Gluing `RGA_EndToEnd.hCanon` down to the concrete leaf bundles

*Additive; modifies no existing file; 0 `sorry`.*

`rga_RA_linearizable_end_to_end` was gated on `hEnum` + `hCanon`. This file discharges `hCanon`'s
STRUCTURE — reduces it to two concrete leaf bundles via the merge glue (`canonMatch_merge_of_inputs`)
and the fold engine — so the whole RGA capstone is gated on:

* `hEnum` — the δ-enum (unchanged);
* `hFoldCanon` — the four `CanonMatch` facts (three branches + the union fold), each = the generic
  engine `canonMatch_of_noopFeasible_enum` + execution-model plumbing;
* `hMergeInputs` — σ₀' wf + causal facts + per-survivor membership + per-survivor `CanonBirthBridge`.

No structural glue remains: what's LEFT is discharging `hFoldCanon`/`hMergeInputs`/`hEnum` from the
execution context (the plumbing + the `BranchInv`-threading `CanonBirthBridge`).
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAEndToEnd

open Sal.Emulation
open Sal.Metatheory.GenericEqQuotient
open Sal.Metatheory.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC' WfOpA rgaInvPresA rgaInvInvVCA)
open Sal.Metatheory.UpdateFeasibilityGate (noopFeasible)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch survP insertedIn deletedIn)
open RGAMergeFoldChain (CanonBirthBridge)
open Sal.Metatheory.RGAMergeCanon (canonMatch_merge_of_inputs)

/-- **`hCanon` from the leaf bundles.**  Produces exactly the `hCanon` hypothesis of
`rga_RA_linearizable_end_to_end` from: `hFoldCanon` (the four canonical characterizations) and
`hMergeInputs` (the merge glue's five leaf inputs). Pure structural wiring — `canonMatch_merge_of_inputs`
for the merge half, `hFoldCanon` for the fold half. -/
theorem hCanon_of_leaves
    (hFoldCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        CanonMatch ρ₀ (applySeqR init_st ρ₀) ∧ CanonMatch ρ₁ (applySeqR init_st ρ₁)
          ∧ CanonMatch ρ₂ (applySeqR init_st ρ₂)
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀))
    (hMergeInputs : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        (∀ y, contains (applySeqR init_st ρ₀) y = true → y ≠ 0 → anc (applySeqR init_st ρ₀) y < y)
        ∧ (∀ y, contains (applySeqR init_st ρ₀) y = true →
            (anc (applySeqR init_st ρ₀) y = 0 ∨ contains (applySeqR init_st ρ₀) (anc (applySeqR init_st ρ₀) y) = true))
        ∧ contains (applySeqR init_st ρ₀) 0 = false
        ∧ (∀ c, (insertedIn ρ₀ c ↔ insertedIn ρ₁ c ∧ insertedIn ρ₂ c)
            ∧ (deletedIn ρ₁ c → insertedIn ρ₁ c) ∧ (deletedIn ρ₂ c → insertedIn ρ₂ c)
            ∧ (deletedIn ρ₀ c → deletedIn ρ₁ c) ∧ (deletedIn ρ₀ c → deletedIn ρ₂ c)
            ∧ (insertedIn (ρ₀ ++ π₀) c ↔ insertedIn ρ₁ c ∨ insertedIn ρ₂ c)
            ∧ (deletedIn (ρ₀ ++ π₀) c ↔ deletedIn ρ₁ c ∨ deletedIn ρ₂ c))
        ∧ (∀ (t r e a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            (contains (applySeqR init_st ρ₀) t = true → (t, r, .Ins e p a) ∈ ρ₀)
            ∧ (contains (applySeqR init_st ρ₁) t = true → (t, r, .Ins e p a) ∈ ρ₁)
            ∧ (contains (applySeqR init_st ρ₂) t = true → (t, r, .Ins e p a) ∈ ρ₂)
            ∧ (contains (applySeqR init_st ρ₀) t = true ∨ contains (applySeqR init_st ρ₁) t = true
                ∨ contains (applySeqR init_st ρ₂) t = true))
        ∧ (∀ (t r e a : ℕ) (p : List ℕ),
            (t, r, .Ins e p a) ∈ ρ₀ ++ π₀ → survP (ρ₀ ++ π₀) t →
            CanonBirthBridge (applySeqR init_st ρ₀) (ρ₀ ++ π₀)
                (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t) (a :: p)
            ∧ (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t = 0
                ∨ survivors (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂)
                    (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t) = true))) :
    ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀) →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀) := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr hnfπ
  obtain ⟨hcm0, hcm1, hcm2, hfold⟩ :=
    hFoldCanon vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr hnfπ
  obtain ⟨Hdec, Hstay, h0, hcaus, hins_branch, hbridge⟩ :=
    hMergeInputs vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr hnfπ
  exact ⟨canonMatch_merge_of_inputs (applySeqR init_st ρ₀) (applySeqR init_st ρ₁)
      (applySeqR init_st ρ₂) ρ₀ π₀ ρ₁ ρ₂ hcm0 hcm1 hcm2 Hdec Hstay h0 hcaus hins_branch hbridge,
    hfold⟩

#print axioms hCanon_of_leaves

/-! `hCanon_of_leaves hFoldCanon hMergeInputs` is exactly the `hCanon` argument of
`rga_RA_linearizable_end_to_end`. So the whole RGA capstone is now gated on `hEnum` + `hFoldCanon` +
`hMergeInputs` + the honest-execution hypotheses — NO structural glue left, only the leaf discharges
(execution-model plumbing + the `BranchInv`-threading `CanonBirthBridge` + the δ-enum). -/

end Sal.Metatheory.RGAEndToEnd
