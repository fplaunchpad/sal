import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_CanonFoldOK
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_Instance
import Sal.ConditionedMRDTs.Framework.ConditionedConvergence
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_InvUpdateQ
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_MergeFoldChain
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_BranchCanon
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_SubchainResolve

/-!
# The RGA capstone, over `WfOpQ` — assembly + the honestly-pinned Join residual

*Additive; modifies no existing file; 0 `sorry`.*

`RGA_Instance.lean` threaded TWO hypotheses into its capstone: `hP : InvPres
RGACondSig' WfOp` (§5, unprovable at `WfOp`) and `hJoinEq` (§7, blocked on the
`loOnA`/`loOnEq` order mismatch and the merge `hin` residual).  Since then:
`RGA_InvUpdateQ` closed the FULL `InvPres` at the strengthened guard `WfOpQ`
(`rgaInvPresQ`, with `rga_wfOpReachableQ` at `WfOpGenQ`), `RGA_ConvergenceEq`
re-derived convergence over the framework's own order `loOnEq rgaEqEquiv' WfOpQ`
(no order mismatch left), and `RGA_HinFilterEq` closed the merge bridge's `hin`.

This file re-bases the whole wiring on `WfOpQ`:

* **§1** `rgaInvInvVCQ : InvInvVC RGACondSig' rgaEqEquiv' WfOpQ` — `WfOp`'s
  `wf_congr` re-proved for the strengthened guard (its extra conjuncts are
  `resolve`-driven, hence `≈`-invariant via `resolve_dom_eq`).
* **§2** raw folds of `Nodup`/distinct-ts/`WfOpGenQ` enumerations carry `qInv`
  (`qInv_fold`), seating merge congruence at fold states.
* **§3** the **union adapter** `isCanonicalStateEq_union_of_fold`:
  `IsCanonicalStateEq`'s ∃/order shape IS reachable from a merge-fold fact —
  prefix the LCA enumeration, use `loOnEqQ_reduce` (the RGA's `loOnEq` is
  index-free) and full closure (no `loOnEq`-edge points from the delta back
  into the LCA set).  The shape match is CLEAN; no order translation remains.
* **§4** `rga_eqJoin_of_oracle` — the `≈`-Join with THREE premises beyond
  `EqJoinLemma3C`'s signature: distinct timestamps on `ev₁ ∪ ev₂`, `WfOpGenQ`
  on `ev₁ ∪ ev₂`, and `MergeFoldOracle` (the merge-fold identity
  `eq_merge_two_sided_eq` would discharge given its `hD`/`hB`/`hBE`/`hcm`/
  `hbridge`/`hMSR` package).  These pin EXACTLY what still separates the RGA
  from the unconditioned `EqJoinLemma3C` — see the STATUS block.
* **§5** the capstone `RGA_is_RA_linearizable`, `RA_linearizable_up_to_eq`
  wired with the five CONCRETE `WfOpQ`-VCs; `hJoinEq` is its one remaining
  non-execution hypothesis.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAInstanceFinal

open Sal.Emulation
open Sal.ConditionedMRDTs.GenericEqQuotient
open Sal.ConditionedMRDTs.RGAInstance (RGACondSig' rgaEqEquiv' rgaCongVC' rga_inv_init' RGACondSig'_init)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpQ)
open RGAMergeLinearization (applySeqR)

/-! ## §1  `InvInvVC` over the strengthened guard `WfOpQ`

`RGA_Instance.rgaInvInvVC'` is stated at `W := WfOp`; the metatheorem must be
instantiated at ONE `W` throughout, and `InvPres` only exists at `WfOpQ`.  The
`Ins` extra (`resolve s (a :: pre) < t`) and the `Del` extras (`resolve`-valued)
descend through `≈` exactly like `WfOp`'s conjuncts: `contains` via `(h t).1`,
`resolve` via `resolve_dom_eq`. -/

/-- `InvInvVC RGACondSig' rgaEqEquiv' WfOpQ` — full, both fields. -/
theorem rgaInvInvVCQ : InvInvVC RGACondSig' rgaEqEquiv' WfOpQ where
  wf_congr := by
    intro o s s' _ _ h
    obtain ⟨t, r, ao⟩ := o
    cases ao with
    | Ins e pre a =>
      show ((t ≠ 0 ∧ contains s t = false) ∧ resolve s (a :: pre) < t)
        ↔ ((t ≠ 0 ∧ contains s' t = false) ∧ resolve s' (a :: pre) < t)
      rw [(h t).1, resolve_dom_eq s s' (a :: pre) (fun c _ => (h c).1)]
    | Del pre x =>
      show (resolve s pre ≠ x ∧ (resolve s pre = 0 ∨ resolve s pre < x))
        ↔ (resolve s' pre ≠ x ∧ (resolve s' pre = 0 ∨ resolve s' pre < x))
      rw [resolve_dom_eq s s' pre (fun c _ => (h c).1)]
  applicable_congr := by
    intro o s s' _ _ h
    exact and_congr (RGAEqQuotient.accurate_eq_iff o h)
      (RGAEqQuotient.fresh_ts_eq_iff o h)

#print axioms rgaInvInvVCQ

/-! ## §2  `qInv` at raw folds of genuine enumerations -/

/-- The framework's `applySeq` on `RGACondSig'` IS the RGA's raw `applySeqR`. -/
theorem applySeq_eq_applySeqR (s : concrete_st) (ρ : List op_t) :
    applySeq RGACondSig'.toCRDTSig s ρ = applySeqR s ρ := by
  induction ρ generalizing s with
  | nil => rfl
  | cons o ρ ih => exact ih (do_ s o)

/-! ## §3  The union adapter: `IsCanonicalStateEq`'s ∃/order shape is CLEAN

`IsCanonicalStateEq … (ev₁ ∪ ev₂) m` demands ONE `loOnEq`-respecting
enumeration of the union folding raw from `init_st` to `≈ m`.  Given the LCA
enumeration `ρ₀` (of `ev₁ ∩ ev₂`) and a delta enumeration `π₀` whose continued
fold is `≈ m`, the witness is literally `ρ₀ ++ π₀`:

* `loOnEq rgaEqEquiv' WfOpQ` is INDEX-FREE (`loOnEqQ_reduce`: `rc ≡ Either`
  empties the tiebreak arm), so `respects` transports across event-set indexes;
* full closure of `ev₁`/`ev₂` kills every cross edge — a `loOnEq`-edge is a
  vis-edge, and a vis-edge from the delta into the LCA set would pull the delta
  event into `ev₁ ∩ ev₂`.

No order translation, no re-enumeration: the shape match is clean. -/

end Sal.ConditionedMRDTs.RGAInstanceFinal
