import Sal.ConditionedMRDTs.Development.RGA_Skeleton
import Sal.ConditionedMRDTs.Development.RGA_Corrected_Assembly
import Sal.ConditionedMRDTs.Framework.Base.CRDT_Signature
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Framework.Base.Labeled_TS
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.BornApplicable_Guard
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_CanonConvergence
import Sal.ConditionedMRDTs.Development.RGA_ChainFaithful_doDel
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Corrected_Residual
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_EqQuotient
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_Instance_NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeCanon
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeFoldChain
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_MergeLinearization
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_WfOpA_VCs
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate
import Sal.ConditionedMRDTs.Development.RGA_SwapRoute_Residuals

/-!
# The CORRECTED end-to-end skeleton — `hEnum` re-based on `CanonFoldOK` + union re-enumerability

*Additive; modifies no existing file; 0 `sorry`.*

`RGA_HEnum_Refutation` killed the old skeleton's `hEnum` (`noopFeasible π₀` from the LCA fold is
unsatisfiable — a concurrent LCA anchor-kill is pre-applied by the shape). This is the corrected
capstone, same discipline as before: every type locked, kernel-clean, the residual as EXPLICIT named
hypotheses. Changes against `rga_RA_linearizable_skeleton`:

* `hEnum` (corrected) — produces `π₀` with the ENGINE-NATIVE per-event discipline
  `CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀` (K1 — `ChainOK`/`DelOK` are rehome-tolerant: they hold
  in the refutation's scenario where `noopFeasible` is false), the LCA's own discipline
  `CanonFoldOK [] init_st ρ₀`, AND a from-`init` union re-enumeration `ρᵤ` (K2 — the induction
  invariant: a merged version is again presentable as an honest delivery).
* `hReady` — THREE `EngineReady` legs (`ρ₀`, `ρ₁`, `ρ₂`). The old fourth (union) leg is GONE: the
  union `CanonMatch` is DERIVED here by `canonFoldOK_concat` + `canon_fold` run mid-stream from the
  LCA fold (`canonInv_init` → `CanonInv ρ₀ σ₀` is subsumed by folding `ρ₀ ++ π₀` from `init`).
* `hMergeInputs` — same leaf bundle, premises re-based on the `CanonFoldOK` facts.
* `hBA`/`hReach`/`hgenW`/`C` — unchanged honest scope.
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGASkeleton2

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
open Sal.ConditionedMRDTs (noopFeasible)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch CanonFoldOK CanonInv canon_fold canonInv_init
  canonMatch_of_canonInv survP insertedIn deletedIn)
open RGAMergeFoldChain (CanonBirthBridge)
open Sal.ConditionedMRDTs.RGASkeleton (EngineReady canonMatch_of_engineReady)
open Sal.ConditionedMRDTs.RGACorrectedResidual (canonFoldOK_concat rga_eqJoinNF_of_canon2)
open Sal.ConditionedMRDTs.RGAMergeCanon (canonMatch_merge_of_inputs)

/-- **The corrected end-to-end.**  As `rga_RA_linearizable_end_to_end`, over the corrected leaves:
`hEnum` carries K1 (`CanonFoldOK` delta discipline) + K2 (union re-enumeration) instead of the
refuted `noopFeasible π₀`; `hCanon`'s premises are re-based accordingly. -/
theorem rga_RA_linearizable_end_to_end2
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
          noopFeasible RGACondSig' ρ₀ init_st →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
          noopFeasible RGACondSig' ρ₁ init_st →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
          noopFeasible RGACondSig' ρ₂ init_st →
        ∃ π₀ ρᵤ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK [] init_st ρ₀ ∧
          CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ ∧
          listPermOf ρᵤ (ev₁ ∪ ev₂) ∧
          respects ρᵤ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∪ ev₂)) ∧
          noopFeasible RGACondSig' ρᵤ init_st ∧
          CanonFoldOK [] init_st ρᵤ)
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀))
    (hBA : ∀ {C₀ C₁ : Sal.ConditionedMRDTs.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
      {v : Sal.ConditionedMRDTs.Version}
      {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)},
      (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
      Sal.ConditionedMRDTs.Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
        C₀ (Sal.ConditionedMRDTs.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable rgaEqEquiv' WfOpA rgaInvInvVCA (t, r, o) sh ∧
        (∀ s', RGACondSig'.applicable (t, r, o) s' → WfOpA (t, r, o) s'))
    (C : Sal.ConditionedMRDTs.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA))
    (hReach : (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C)
    (hgenW : ∀ o ∈ (Sal.ConditionedMRDTs.Configuration.core C).events,
        ∀ s', RGACondSig'.applicable o s' → WfOpA o s') :
    Sal.ConditionedMRDTs.IsRALinearizable3 C :=
  Sal.ConditionedMRDTs.RGAInstanceNF.rga_RA_linearizable_NF
    (rga_eqJoinNF_of_canon2 WfOpA hEnum hCanon) hBA C hReach hgenW

/-- **Bridge #1, corrected.**  THREE engine-ready folds (the branches) + the `CanonFoldOK`
premises assemble `hCanon`'s fold half: the branch `CanonMatch`es via the engine
(`canonMatch_of_engineReady`, unchanged), the union `CanonMatch` DERIVED by composing the
disciplines (`canonFoldOK_concat`) and running `canon_fold` from `init` — no union `EngineReady`,
no feasibility at the LCA-first fold. -/
theorem hFoldCanon2_of_engineReady
    (hReady : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        EngineReady events (ev₁ ∩ ev₂) ρ₀ ∧ EngineReady events ev₁ ρ₁
          ∧ EngineReady events ev₂ ρ₂) :
    ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch ρ₀ (applySeqR init_st ρ₀) ∧ CanonMatch ρ₁ (applySeqR init_st ρ₁)
          ∧ CanonMatch ρ₂ (applySeqR init_st ρ₂)
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀) := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr h₀OK hπOK
  obtain ⟨hr0, hr1, hr2⟩ :=
    hReady vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr h₀OK hπOK
  refine ⟨canonMatch_of_engineReady events (ev₁ ∩ ev₂) ρ₀ hdts hr0,
    canonMatch_of_engineReady events ev₁ ρ₁ hdts hr1,
    canonMatch_of_engineReady events ev₂ ρ₂ hdts hr2, ?_⟩
  -- the union fold: compose the disciplines and run the engine from `init`
  have hcat : CanonFoldOK [] init_st (ρ₀ ++ π₀) :=
    canonFoldOK_concat ρ₀ [] init_st π₀ h₀OK hπOK
  have hci : CanonInv ([] ++ (ρ₀ ++ π₀)) (applySeqR init_st (ρ₀ ++ π₀)) :=
    canon_fold (ρ₀ ++ π₀) [] init_st canonInv_init hcat
  rw [List.nil_append] at hci
  have hcm : CanonMatch (ρ₀ ++ π₀) (applySeqR init_st (ρ₀ ++ π₀)) :=
    canonMatch_of_canonInv (ρ₀ ++ π₀) _ hci
  have happ : applySeqR init_st (ρ₀ ++ π₀) = applySeqR (applySeqR init_st ρ₀) π₀ := by
    simp only [applySeqR, List.foldl_append]
  rw [happ] at hcm
  exact hcm

/-- **`hCanon` from the corrected leaf bundles.**  As `hCanon_of_leaves`, over the corrected
premise chain: the merge half is `canonMatch_merge_of_inputs` fed the three branch `CanonMatch`es
and the merge-glue leaves; the fold half is the (now derived) union `CanonMatch`. -/
theorem hCanon_of_leaves2
    (hFoldCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
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
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
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
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        CanonMatch (ρ₀ ++ π₀)
            (merge (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂))
          ∧ CanonMatch (ρ₀ ++ π₀) (applySeqR (applySeqR init_st ρ₀) π₀) := by
  intro vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr h₀OK hπOK
  obtain ⟨hcm0, hcm1, hcm2, hfold⟩ :=
    hFoldCanon vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr h₀OK hπOK
  obtain ⟨Hdec, Hstay, h0, hcaus, hins_branch, hbridge⟩ :=
    hMergeInputs vis events ev₁ ev₂ ρ₀ ρ₁ ρ₂ π₀ htr hir hdts hev1 hev2 hcl1 hcl2 h0p h1p h2p hπp hπr h₀OK hπOK
  exact ⟨canonMatch_merge_of_inputs (applySeqR init_st ρ₀) (applySeqR init_st ρ₁)
      (applySeqR init_st ρ₂) ρ₀ π₀ ρ₁ ρ₂ hcm0 hcm1 hcm2 Hdec Hstay h0 hcaus hins_branch hbridge,
    hfold⟩

/-- **The CORRECTED capstone skeleton.**  RGA per-version RA-linearizability up to `≈`, plugged
END-TO-END to the unconditional `IsRALinearizable3 C`, gated on the corrected residual:

* `hEnum` — K1 (delta enum with the engine-native `CanonFoldOK` discipline — TRUE in the scenario
  that refuted the old `noopFeasible` phrasing) + K2 (from-`init` union re-enumeration — the
  induction invariant that a merged version is again an honest delivery);
* `hReady` — three `EngineReady` folds (the branches; the union leg is DERIVED);
* `hMergeInputs` — the merge glue's leaf bundle (unchanged content, corrected premises);
* `hBA`/`hReach`/`hgenW` — the honest-execution premises.

0 `sorry`; axioms `⊆ {propext, Classical.choice, Quot.sound}`. -/
theorem rga_RA_linearizable_skeleton2
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
          noopFeasible RGACondSig' ρ₀ init_st →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
          noopFeasible RGACondSig' ρ₁ init_st →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
          noopFeasible RGACondSig' ρ₂ init_st →
        ∃ π₀ ρᵤ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          CanonFoldOK [] init_st ρ₀ ∧
          CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ ∧
          listPermOf ρᵤ (ev₁ ∪ ev₂) ∧
          respects ρᵤ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∪ ev₂)) ∧
          noopFeasible RGACondSig' ρᵤ init_st ∧
          CanonFoldOK [] init_st ρᵤ)
    (hReady : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
        EngineReady events (ev₁ ∩ ev₂) ρ₀ ∧ EngineReady events ev₁ ρ₁
          ∧ EngineReady events ev₂ ρ₂)
    (hMergeInputs : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a b : op_t, a ∈ events → b ∈ events → a ≠ b → a.1 ≠ b.1) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → listPermOf ρ₁ ev₁ → listPermOf ρ₂ ev₂ →
        listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) →
        respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) →
        CanonFoldOK [] init_st ρ₀ →
        CanonFoldOK ρ₀ (applySeqR init_st ρ₀) π₀ →
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
                    (birthAnc (applySeqR init_st ρ₀) (applySeqR init_st ρ₁) (applySeqR init_st ρ₂) t) = true)))
    (hBA : ∀ {C₀ C₁ : Sal.ConditionedMRDTs.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)}
      {t : Sal.Emulation.Timestamp} {r : Sal.Emulation.Replica} {o : app_op_t}
      {v : Sal.ConditionedMRDTs.Version}
      {sh : QState RGACondSig' rgaEqEquiv'} {evh : Set (Op app_op_t)},
      (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C₀ →
      Sal.ConditionedMRDTs.Step3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)
        C₀ (Sal.ConditionedMRDTs.Label3.apply t r o) C₁ →
      C₀.head r = some v → C₀.ver v = some (sh, evh) →
      qapplicable rgaEqEquiv' WfOpA rgaInvInvVCA (t, r, o) sh ∧
        (∀ s', RGACondSig'.applicable (t, r, o) s' → WfOpA (t, r, o) s'))
    (C : Sal.ConditionedMRDTs.Configuration
        (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA))
    (hReach : (labeledTS3 (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA)).ReachableFrom
        (Sal.ConditionedMRDTs.initConfig
          (QSig rgaEqEquiv' WfOpA rgaInvPresA rgaCongVC' rgaInvInvVCA) trivial) C)
    (hgenW : ∀ o ∈ (Sal.ConditionedMRDTs.Configuration.core C).events,
        ∀ s', RGACondSig'.applicable o s' → WfOpA o s') :
    Sal.ConditionedMRDTs.IsRALinearizable3 C :=
  rga_RA_linearizable_end_to_end2 hEnum
    (hCanon_of_leaves2 (hFoldCanon2_of_engineReady hReady) hMergeInputs)
    hBA C hReach hgenW

/-! ## Axiom audit -/

#print axioms rga_RA_linearizable_end_to_end2
#print axioms hFoldCanon2_of_engineReady
#print axioms hCanon_of_leaves2
#print axioms rga_RA_linearizable_skeleton2

end Sal.ConditionedMRDTs.RGASkeleton2
