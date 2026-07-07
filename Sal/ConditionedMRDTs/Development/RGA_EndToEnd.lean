import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance_NF
import Sal.ConditionedMRDTs.Development.RGA_EqJoin_NF_Assembly
import Sal.ConditionedMRDTs.Framework.Base.CRDT_Signature
import Sal.ConditionedMRDTs.Framework.Base.CRDT_TS
import Sal.ConditionedMRDTs.Framework.Base.Labeled_TS
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.BornApplicable_Guard
import Sal.ConditionedMRDTs.Metatheory.GenericEqQuotient
import Sal.ConditionedMRDTs.Metatheory.GoodConfig3NF
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonConvergence
import Sal.ConditionedMRDTs.Development.RGA_ChainFaithful_doDel
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_EqQuotient
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeLinearization
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_WfOpA_VCs
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate

/-!
# RGA `≈`-linearizability, plugged END-TO-END modulo the explicit residual

*Additive; modifies no existing file; 0 `sorry`.*

The whole chain, as ONE theorem concluding `IsRALinearizable3`, with the residual carried as explicit
named hypotheses (skeleton-first / admit-the-residual discipline). Top-down (RA-lin ← metatheorem ←
`EqJoinLemma3C_NF`) meets bottom-up (`hEnum`/`hCanon` → merge=fold via `eq_of_canonMatch2`) — nothing
hidden, kernel-clean.

`rga_RA_linearizable_end_to_end` :  `hEnum` + `hCanon` + (`hBA`/`hReach`/`hgenW`) → `IsRALinearizable3 C`.

**Residual classification (what a real close must still discharge):**
* `hEnum` — a canonical δ-enum exists. GENERIC (born-applicable delivery; framework's job, not RGA's).
* `hCanon` — merge & δ-fold are both the canonical state of `ρ₀ ++ π₀`. The FOLD half is generic
  (`RGACanonConvergence.canon_fold`); the MERGE half `CanonMatch F (merge …)` is the ONE irreducible
  RGA fact ("the RGA merge computes the canonical state of the union"), reducing (mechanized) to the
  crisp `hFiltEq : rcSuf.filter (survB F) = cw.filter (survB F)` — the RGA's two-sided reconstruction
  semantics, not derivable from any single branch's `CanonMatch`, not removable by framework generality.
* `hBA`/`hReach`/`hgenW` — the legitimate honest-execution premises the metatheorem already requires.

NO `hMSR` swap oracle, NO `BranchInv` threading, NO six pieces, NO `GenDisc2CEq`.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAEndToEnd

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.GoodConfig3NF
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC' WfOpA rgaInvPresA rgaInvInvVCA)
open Sal.ConditionedMRDTs (noopFeasible)
open RGAMergeLinearization (applySeqR)
open RGACanonConvergence (CanonMatch)

/-- **End-to-end.**  RGA per-version RA-linearizability up to `≈`, plugged through the canonical
route, gated on the explicit residual (`hEnum` + `hCanon`, both classified above) and the honest-
execution premises. The merge=fold engine is `eq_of_canonMatch2` (canonical uniqueness); the RGA
supplies exactly one fact (`CanonMatch F (merge …)` inside `hCanon`). -/
theorem rga_RA_linearizable_end_to_end
    (hEnum : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ : List op_t),
        (∀ {a b c : op_t}, vis a b → vis b c → vis a c) → (∀ a : op_t, ¬ vis a a) →
        (∀ a ∈ ev₁, a ∈ events) → (∀ a ∈ ev₂, a ∈ events) →
        fullClosureRel (D := RGACondSig') vis ev₁ → fullClosureRel (D := RGACondSig') vis ev₂ →
        listPermOf ρ₀ (ev₁ ∩ ev₂) → respects ρ₀ (loOnEq rgaEqEquiv' WfOpA vis (ev₁ ∩ ev₂)) →
          noopFeasible RGACondSig' ρ₀ init_st →
        listPermOf ρ₁ ev₁ → respects ρ₁ (loOnEq rgaEqEquiv' WfOpA vis ev₁) →
          noopFeasible RGACondSig' ρ₁ init_st →
        listPermOf ρ₂ ev₂ → respects ρ₂ (loOnEq rgaEqEquiv' WfOpA vis ev₂) →
          noopFeasible RGACondSig' ρ₂ init_st →
        ∃ π₀ : List op_t,
          listPermOf π₀ ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂)) ∧
          respects π₀ (loOnEq rgaEqEquiv' WfOpA vis ((ev₁ ∪ ev₂) \ (ev₁ ∩ ev₂))) ∧
          noopFeasible RGACondSig' π₀ (applySeqR init_st ρ₀))
    (hCanon : ∀ (vis : op_t → op_t → Prop) (events ev₁ ev₂ : Set op_t) (ρ₀ ρ₁ ρ₂ π₀ : List op_t),
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
    (Sal.ConditionedMRDTs.RGAEqJoinNF.rga_eqJoinNF_of_canon WfOpA hEnum hCanon) hBA C hReach hgenW

/-! ## Axiom audit -/

#print axioms rga_RA_linearizable_end_to_end

end Sal.ConditionedMRDTs.RGAEndToEnd
