import Sal.ConditionedMRDTs.Development.RGA_NoopFeasible_CanonFold
import Sal.ConditionedMRDTs.Development.RGA_ConvergenceEq
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_InvUpdateQ
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeLinearization
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate

/-!
# `CanonMatch` for a reachable born-applicable fold — the generic fold half

*Additive; modifies no existing file; 0 `sorry`.*

Packages the canonical-state engine into one reusable lemma: a `noopFeasible`, `R`-respecting,
reference-closed (`GoodEnumR`) enumeration of `E` folds from `init_st` to a state that IS the
canonical state of that enumeration (`CanonMatch`). `canon_fold` + `canonFoldOK_of_noopFeasible` +
`canonMatch_of_canonInv`, GenDisc-free. This is the FOLD half of `hCanon` (`RGA_EndToEnd.lean`) and
supplies each branch's canonical characterization (`σᵢ'` = canonical state of `ρᵢ`).
-/

set_option maxHeartbeats 1000000

open Classical

namespace Sal.ConditionedMRDTs.RGACanonMatchReachable

open Sal.Emulation
open RGACanonConvergence
open RGANoopFeasible (canonFoldOK_of_noopFeasible)
open Sal.ConditionedMRDTs.RGAConvergenceEq (GoodEnumR)
open RGAMergeLinearization (applySeqR)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpGenQ)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)

/-- **`CanonMatch` for a reachable born-applicable fold.**  A `GoodEnumR`, `noopFeasible`
enumeration `σ` of `E` (`R` any order with `RefEdge E R`, ids distinct/nonzero, ops `WfOpGenQ`) folds
from `init_st` to the canonical state of `σ`. Reusable for the union fold `ρ₀ ++ π₀` and each branch
`ρᵢ`. -/
theorem canonMatch_of_noopFeasible_enum
    (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RGANoopFeasible.RefEdge E R)
    (σ : List op_t) (hgood : GoodEnumR E R σ)
    (hnf : noopFeasible RGACondSig σ init_st) :
    CanonMatch σ (applySeqR init_st σ) := by
  have hfok : CanonFoldOK [] init_st σ :=
    canonFoldOK_of_noopFeasible E R hdts hids0 hgen href σ.length σ le_rfl hgood hnf
  have hci : CanonInv ([] ++ σ) (applySeqR init_st σ) :=
    canon_fold σ [] init_st canonInv_init hfok
  rw [List.nil_append] at hci
  exact canonMatch_of_canonInv σ (applySeqR init_st σ) hci

#print axioms canonMatch_of_noopFeasible_enum

/-- **Packaged for a context delivery.**  `GoodEnumR` is DERIVED from a `listPermOf` + `respects`
(both handed by the `RgaEqJoinResidualLit`/`hFoldCanon` context) — for a full enumeration the
backward-closure clause is trivial. So a branch/union fold's `CanonMatch` reduces to exactly the
generation facts `hids0`/`hgen`/`href` (nonzero ids, `WfOpGenQ`, reference edges) plus the
framework-provided `hdts`. This is the per-fold shape #37 applies four times. -/
theorem canonMatch_reachable_of_facts
    (E : Set op_t) (R : op_t → op_t → Prop) (ρ : List op_t)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RGANoopFeasible.RefEdge E R)
    (hperm : listPermOf ρ E) (hresp : respects ρ R)
    (hnf : noopFeasible RGACondSig ρ init_st) :
    CanonMatch ρ (applySeqR init_st ρ) :=
  canonMatch_of_noopFeasible_enum E R hdts hids0 hgen href ρ
    ⟨fun x hx => (hperm.2 x).mp hx, hperm.1, hresp,
      fun _x _hx z hz _hne _hR => (hperm.2 z).mpr hz⟩ hnf

#print axioms canonMatch_reachable_of_facts

/-! ## The `CanonInv`-exposing variant — carries the per-survivor `LiveChain`

`CanonMatch` records only `el`/`anc = canonAnc`, dropping the `LiveChain` carrier that `CanonInv`
holds. The merge-side birth bridge (`RGA_BirthBridge.canonBirthBridge_per_survivor`) needs each
survivor's branch `LiveChain σᵢ' k (a::p)` to build the four carriers, so we expose `CanonInv`
directly (same fold, just the stronger invariant). Identical hypotheses to
`canonMatch_reachable_of_facts`; only the conclusion strengthens `CanonMatch` → `CanonInv`. -/

/-- **`CanonInv` for a reachable born-applicable fold** — as `canonMatch_of_noopFeasible_enum` but
returning the full `CanonInv` (hence the per-survivor `LiveChain`). -/
theorem canonInv_of_noopFeasible_enum
    (E : Set op_t) (R : op_t → op_t → Prop)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RGANoopFeasible.RefEdge E R)
    (σ : List op_t) (hgood : GoodEnumR E R σ)
    (hnf : noopFeasible RGACondSig σ init_st) :
    CanonInv σ (applySeqR init_st σ) := by
  have hfok : CanonFoldOK [] init_st σ :=
    canonFoldOK_of_noopFeasible E R hdts hids0 hgen href σ.length σ le_rfl hgood hnf
  have hci : CanonInv ([] ++ σ) (applySeqR init_st σ) :=
    canon_fold σ [] init_st canonInv_init hfok
  rw [List.nil_append] at hci
  exact hci

#print axioms canonInv_of_noopFeasible_enum

/-- **Packaged `CanonInv` for a context delivery** — as `canonMatch_reachable_of_facts` but yielding
`CanonInv` (the per-survivor `LiveChain` carrier), for the merge birth-bridge. -/
theorem canonInv_reachable_of_facts
    (E : Set op_t) (R : op_t → op_t → Prop) (ρ : List op_t)
    (hdts : ∀ a b : op_t, a ∈ E → b ∈ E → a ≠ b → a.1 ≠ b.1)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (hgen : ∀ o ∈ E, WfOpGenQ o)
    (href : RGANoopFeasible.RefEdge E R)
    (hperm : listPermOf ρ E) (hresp : respects ρ R)
    (hnf : noopFeasible RGACondSig ρ init_st) :
    CanonInv ρ (applySeqR init_st ρ) :=
  canonInv_of_noopFeasible_enum E R hdts hids0 hgen href ρ
    ⟨fun x hx => (hperm.2 x).mp hx, hperm.1, hresp,
      fun _x _hx z hz _hne _hR => (hperm.2 z).mpr hz⟩ hnf

#print axioms canonInv_reachable_of_facts

end Sal.ConditionedMRDTs.RGACanonMatchReachable
