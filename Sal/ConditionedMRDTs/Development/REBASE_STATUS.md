# RGA re-base onto born-applicable delivery — status

*The re-base off `GenDisc2CEq` onto the honest `applicable`/`noopFeasible` discipline.
Motivation and the pen-and-paper in `LOONA_VS_LOONEQ_ANALYSIS.md`.*

## The decision (KC-confirmed)

Guard the conditioned quotient with **`WfOpA := WfOpQ ∧ accurate`** (⟹ `applicable`) instead of the
weaker `WfOpQ`. Then born-applicability / `noopFeasible` is INTRINSIC (the guard skips inaccurate ops,
which are exactly the divergent ones), and `GenDisc2CEq` vanishes. Reachability route: **option B**
(parallel `GoodConfig3NF`, no CRDT-scope / sorry-file surgery).

## DONE — kernel-clean (axioms ⊆ {propext, Classical.choice, Quot.sound}, no `sorryAx`)

### `BornApplicable_Guard.lean` — the guard foundation
- `appOrNoop_qsig` — **generic**: any guarded quotient whose guard ⟹ `applicable` is born-applicable
  (every `QSig` step is `appOrNoop`). Guard fires → applicable branch; guard fails → `qdo` = identity.
- `WfOpA`, `wfOpQ_of_wfOpA`, `applicable_of_wfOpA`, `wfOpA_of_genQ_applicable` (`applicable ⟹ WfOpA` on
  genuine ops — the bridge's `hWA`), `rgaInvPresA` (`InvPres RGACondSig' WfOpA`, reuses `qInv_doOp`),
  `rga_appOrNoop_qsig`. BONUS: `WfOpA` closes the old `inv_update` residual `RGA_Instance §5` lamented.

### `RGA_NoopFeasible_CanonFold.lean` — the convergence engine
- §1–2 CRUX: `chainOK_of_accurate_ins`, `delOK_of_accurate_del`, `chainOK_of_appOrNoop_ins`,
  `delOK_of_appOrNoop_del` — accuracy at the ACTUAL prefix ⟹ engine per-step obligation (`ChainOK`/`DelOK`)
  DIRECTLY, no dependency-prefix transport.
- §3 `canonFoldOK_of_noopFeasible` (+ `canonStepOK_of_noopFeasible`, `noopFeasible_snoc`, `RefEdge`,
  `refsOf`) — the `GenDisc2CEq`-free engine discipline. The causal-ref subtlety (noopFeasible alone
  permits a noop-Del referencing a future id) is captured by ONE hypothesis `RefEdge` (references induce
  order edges), discharged at reachability from causal-ref + creator/user non-commutation.
- §4 `RGA_update_convergence_noop` (abstract order `R`) + `_loEq` — two `noopFeasible` enums converge;
  the `GenDisc2CEq`-free analog of `RGA_update_convergence_eq`. **The RGA update side is fully re-based.**

### `GenericEqQuotient_NF.lean` — the generic NF interface + exec bridge
- `IsCanonicalStateEqNF` (witness + `noopFeasible`), `EqJoinLemma3C_NF` (no `GenDisc`),
  `isCanonicalStateEq_of_NF`.
- `GuardNoopChain`, `applySeqW_eq_applySeq_of_guardNoop` — **guard transparency for born-applicable
  chains** (guarded = raw when each step is `W` OR a literal no-op; the `WfOpReachable` shift).
- `guardNoop_of_noopFeasible`, `isCanonicalState_of_NF` — the one-way bridge datatype-NF ⟹ exec-canonical
  (sidesteps the hard eqv→literal direction; the reverse isn't needed).
- `noopFeasible_append` — the union witness `ρ₀ ++ π₀` composition.

## The key architectural finding (recorded, non-obvious)

At `WfOpA` the GUARDED fold skips inaccurate ops, and accuracy is ORDER-DEPENDENT, so guarded folds of
different orders can DIVERGE (e.g. `{Ins b, Ins a@b, Del b, Ins e [] a}`: `[b,a,o,del]`→`{a@0}` skips o,
`[b,a,del,o]`→`{a@0,n@a}`). NOT fatal: (1) `canon_fold` runs on RAW folds, which converge; (2)
`canonFoldOK_of_noopFeasible` applies only to `noopFeasible` enums, and the divergent order is NOT
`noopFeasible`; (3) the only `noopFeasible` order is the CAUSAL one; (4) RA-lin is EXISTENTIAL (needs one
witness = the causal delivery). So `WfOpA` is correct; the divergence is on non-witness orders that
`noopFeasible` excludes. `del_noop_general` (UpdateFeasibility_Gate.lean:133) makes redundant deletes
LITERAL no-ops, so guarded = raw on `noopFeasible` witnesses.

### `RGA_EqJoin_NF.lean` — the `≈`-Join reduced to the merge residual
- `loOnEqQ_reduce_gen` / `loOnEqQ_index_free_gen` — the order reductions at ANY guard `W` (guard-independent,
  `rc = Either`), so they apply at `WfOpA`.
- `isCanonicalStateEqNF_union_of_fold` — the born-applicable union canonical-state SHAPE (mirror of
  `RGA_Instance_Final`'s + the `noopFeasible` clause via `noopFeasible_append`), parametric in `W`.
- `RgaEqJoinResidual_NF`, `rga_eqJoin_of_mergeFoldResidual_NF` — **`EqJoinLemma3C_NF` reduces to exactly the
  merge=delta-fold residual**, `GenDisc`-free. The entire union shape is closed; only the residual remains.

### `RGA_WfOpA_VCs.lean` — the guard-shift VCs
- `rgaInvInvVCA : InvInvVC RGACondSig' rgaEqEquiv' WfOpA`. **All 4 quotient VCs at `WfOpA` now hold**:
  InvPres (`rgaInvPresA`), CongVC (`rgaCongVC'`, guard-independent), InvInvVC (`rgaInvInvVCA`),
  WfOpReachable → `GuardNoopChain` (`applySeqW_eq_applySeq_of_guardNoop`).

## REMAINING (large; needs deliberate, non-blind work)

**Guard coupling** (`loOn_qsig_iff`): the quotient guard `W` and the order's `W` are the SAME, and
born-applicability forces `W = WfOpA`. So the `WfOpQ`-hardcoded shape machinery must be re-proved at
`WfOpA`. The small order lemmas generalize trivially (`loOnEqQ_reduce`'s proof is W-independent — only
`rc = Either`); `isCanonicalStateEq_union_of_fold` needs a mechanical re-statement at `WfOpA` + the
`noopFeasible` clause via `noopFeasible_append` (→ `isCanonicalStateEqNF_union_of_fold`).

1. **RGA discharges `EqJoinLemma3C_NF`** (the merge side). Mirror `rga_eqJoin_of_mergeFoldResidual`
   (`RGA_Instance_Final.lean:222`) for NF → isolates `RgaEqJoinResidual_NF`. The update side is DONE
   (`RGA_update_convergence_noop`); the residual is the merge=delta-fold bridge. Two walls (per
   `RGA_Instance_Final §4` STATUS):
   - **WALL 0** (config facts from abstract `vis`) — the re-base ADDRESSES this: the born-applicable
     discipline (`noopFeasible` + `WfOpGenQ` + `RefEdge`) carries `distinct_ts`/`causal_mono`/`BackClosed`,
     so no strengthened `GenDisc` is needed.
   - **WALL 1** (branch pieces `hD`/`hB`/`hBE`/`hBN`, merge = live-set / birth-anchor fold) — genuinely
     UNMECHANIZED, independent of the re-base. This is the real remaining research wall.
2. **`GoodConfig3NF`** (`GoodConfig3NF.lean`) — STRUCTURE + apply core + result direction DONE (kernel-clean):
   - `IsCanonicalStateNF` (exec-side: `IsCanonicalState` + `noopFeasible` over `QSig`, folded by guarded `qdo`).
   - `isCanonicalState_of_NFcls` — drop the feasibility clause → base `IsCanonicalState` (trivial; no bridge).
   - **`isCanonicalStateNF_extend`** — the apply-step core: extend the parent witness by the fresh vis-maximal
     event; `noopFeasible` is FREE via `appOrNoop_qsig` (`W ⟹ applicable`). Shape reuses
     `isCanonicalState_extend`. **The key new reachability lemma.**
   - `GoodConfig3NF := GoodConfig3 ∧ canonicalNF` (over `core C`); `isRALinearizable3_of_goodNF` (trivial via `.1`).
   - `isCanonicalStateNF_congr` — transport under `vis`-agreement (NF analog of `isCanonicalState_congr`).
   - **`goodConfig3NF_init`, `goodConfig3NF_createReplica`, `goodConfig3NF_apply`** — 3 of 4 step preservations
     DONE (kernel-clean). The apply step needs NO born-applicable premise beyond `hWapp : W ⟹ applicable` —
     the new version state IS the guarded fold `qdo s e`, exactly what the extend produces.
   - `goodConfig3NF_merge_of_canonical` DONE (kernel-clean) — the store-bookkeeping half of the merge, takes the
     merged canonical `h_mergedNF` as a premise (design-agnostic).
   - `loOnEq_antimono` DONE (kernel-clean, `GenericEqQuotient_NF`) — for the datatype extension.

   **DATATYPE-SIDE REBUILD DONE (kernel-clean).** The exec-side `noopFeasible (QSig)` clause was found VACUOUS
   (`appOrNoop_qsig` makes every `QSig` step `appOrNoop`), so `IsCanonicalStateNF` is now datatype-side:
   `∃ σ hσ, q = qmk σ ∧ IsCanonicalStateEqNF ev σ`. Rebuilt over it (all kernel-clean):
   - Generic (`GenericEqQuotient_NF`): `isCanonicalStateEqNF_congr`, **`isCanonicalStateEqNF_extend`** (datatype
     apply extension: `loOnEq_antimono` + `applicable_congr`/`update_congr` + `hInvCong` for `Inv` of the fold),
     `loOnEq_antimono`.
   - `GoodConfig3NF.lean`: `IsCanonicalStateNF` (datatype), `isCanonicalState_of_NFcls`, `isCanonicalStateNF_congr`,
     `isCanonicalStateNF_extend` (class-level, threads `qmk` relation + honest premise `qapplicable e s` + `hgenW`),
     `GoodConfig3NF`, `isRALinearizable3_of_goodNF` (trivial), and **ALL 4 step preservations**: `goodConfig3NF_init`,
     `_createReplica`, `_apply`, `_merge_of_canonical`.
   - **`mergedNF_of_join`** — the NF join: feeds `EqJoinLemma3C_NF` **DIRECTLY** (no bridge — the earlier
     exec↔datatype worry dissolved) + `qmergeL_qmk`. So `goodConfig3NF_merge` = `merge_of_canonical` +
     `mergedNF_of_join`, fully reduced to `EqJoinLemma3C_NF` (WALL 1).

   - **`goodConfig3NF_merge`** (full merge step) + **`goodConfig3NF_of_reachF`** (the `Step3` reachability
     induction, threading `hgenW` + the born-applicable `hBA`) + **`RA_linearizable_up_to_eq_NF`** — ALL DONE,
     kernel-clean. `hBA` = the born-applicable delivery discipline (reachable apply ⟹ `qapplicable` at the head +
     `applicable ⟹ W`), the honest-execution hypothesis the RAW-fold witness genuinely needs (the guarded fold
     hid it via skip).

## ✅ THE GENERIC METATHEOREM IS COMPLETE (kernel-clean, no `sorryAx`)

`RA_linearizable_up_to_eq_NF` : a reachable `QSig`-config under the born-applicable discipline (`hBA`) with genuine
events (`hgenW`) and `Inv`-`≈`-invariance (`hInvCong`) is per-version RA-linearizable — GATED ONLY on the datatype's
merge VC `EqJoinLemma3C_NF`. **No `GenDisc`, no `GDSupply`, no `WfOpReachable`.** This is the born-applicable analog
of the original `RA_linearizable_up_to_eq`, with `GenDisc2CEq` fully eliminated from the framework.

## ✅ RGA INSTANTIATION DONE (kernel-clean) — `RGA_Instance_NF.lean`

`rga_RA_linearizable_NF` : the RGA instance of `RA_linearizable_up_to_eq_NF` at `W := WfOpA`. `hInvCong`
discharged (`rga_invCong` — `qInv` `≈`-invariant via `wf_eq_invariant`/`contains_zero_eq_iff`/`id_mono_eq_invariant`);
the 4 quotient VCs plugged in (`rgaInvPresA`, `rgaCongVC'`, `rgaInvInvVCA`, `GuardNoopChain`). Any reachable RGA
configuration under the born-applicable discipline is per-version RA-linearizable — GATED ONLY on `hJoinNF`
(`EqJoinLemma3C_NF` for the RGA = WALL 1), `hBA` (born-applicable delivery: clients apply accurate ops), and
`hgenW` (genuine events). **`GenDisc2CEq` is gone.**

## WALL 1 — the `≈`-vs-literal obstruction (GAP-1) is RESOLVED (kernel-clean)

`WALL1_ANALYSIS.md` has the pen-and-paper. The residual reduces (`merge_fold_indep_canon`,
`eq_merge_two_sided_final`, `canonBirthBridge_via_branchCanon`, `hin_of_survFilterEq`) to: produce one delta
enum `π₀` with `eq (merge l a b) (applySeqR l π₀)` from six pieces (hD/hB/hBE/hcm/hbridge/hMSR). The GAP-1 wall
was that the branch machinery needs LITERAL branch folds but `IsCanonicalStateEq` gives only `≈`.

**The born-applicable re-base dissolves GAP-1** (`RGA_EqJoin_NF.mergeFold_transport`,
`RGA_EqJoin_NF_Residual.rga_eqJoin_of_residualLit_NF` — both kernel-clean): the deliveries `ρ₀/ρ₁/ρ₂` fold to
LITERAL states `σ_i' ≈ s_i`; run the six-piece machinery on the literal folds (where the branch `LiveChain`
structure genuinely exists), then transport to the `≈`-classes `mergeL s₀ s₁ s₂` by ONE `merge`-congruence
(`mergeL_congr`). **`EqJoinLemma3C_NF` now reduces to `RgaEqJoinResidualLit` — a PURE literal-fold merge
identity, no `≈`-vs-literal, no `GenDisc`.**

## THE SOLE REMAINING GAP (now a bounded mechanization, not a wall)

**`RgaEqJoinResidualLit`** — produce, from the three born-applicable literal folds, the delta enum `π₀` and
the literal merge=fold. The six pieces, now UNBLOCKED (literal branches):
- `hMSR` — born-applicable (`conditioned_premises`); `hcm` — `canon_fold`; `hbridge` — `hFiltEq` (survivor-
  subsequence coincidence, from path accuracy);
- `hD` (OR-set = live-set), `hB` (`BranchInv`), `hBE` (branch-new element) — honest inductions on the LITERAL
  branch folds (`RGA_MergeThreadDischarge` scope). Grind, not a wall.

Everything else — guard, update side, `≈`-Join shape, all VCs, the full reachability metatheorem, the RGA
instantiation, AND the GAP-1 reconciliation — is done and kernel-clean.
3. **Top-level** `RA_linearizable_up_to_eq_NF` : `GoodConfig3NF C → IsRALinearizable3 C` (via
   `goodConfig3_of_NF` + `isRALinearizable3_of_good`). No `GenDisc2CEq`, no exec-model premise.
4. Remaining quotient VCs at `WfOpA`: `InvPres` ✓; `CongVC` W-independent ✓; `InvInvVC` `wf_congr` for
   `WfOpA = WfOpQ ∧ accurate`; `WfOpReachable` → the `GuardNoopChain` shift (done generically as
   `applySeqW_eq_applySeq_of_guardNoop`).

**Net:** the update side and the whole born-applicable interface are done and verified. The end-to-end
result is gated on (1)+(2), of which WALL 1 (merge branch pieces) is the sole genuine research wall — the
SAME wall the `GenDisc2CEq` version faced, now on an honest, dischargeable foundation.
