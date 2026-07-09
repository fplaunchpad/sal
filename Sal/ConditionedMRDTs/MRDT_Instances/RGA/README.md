# The tombstone-free RGA — the fully general conditioned instance

This directory is ONE instance of the generic conditioned framework: the
tombstone-free RGA (implementation:
[`Sal/MRDTs/RGA_Tombstone_Free/`](../../../MRDTs/RGA_Tombstone_Free/)),
instantiated at full generality — non-trivial `Inv` (forest
well-formedness), non-trivial `applicable` (accuracy ∧ freshness), and a
non-identity `≈` (dead-node representation residue quotiented away). The
entry point is [`RA_Lin.lean`](RA_Lin.lean):

    rga_ra_linearizable3_eq :
      HonestDelivery →
      ∀ C reachable from initConfig (states quotiented by ≈),
        IsRALinearizable3Eq … C

Everything here is kernel-clean: axioms ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}, zero `sorry`. The chain is ~40 files because the RGA cannot
take the flat route — it re-proves, under conditioning, everything the
eight flat VCs give a flat datatype for free; each sub-chain below was a
separate wall of the investigation. (A kernel-level dependency audit
retired the investigation's superseded first route — the seventeen
swap/faithfulness files — to `Development/`; see History below.)

A file-naming note: several files keep the name of the *investigation* that
produced them (`*_Gate`, `*_PBT`). Their load-bearing content is what the
map below says.

## The signature

| file | provides |
|---|---|
| `RGA_CondSig.lean` | **`RGAM`** (the raw `MRDTSig`: `do_`, three-way merge, `rc = Either`) and **`RGACondSig`** (`Inv := RgaInv`, `applicable := accurate ∧ fresh_ts`), plus the order-stable `opOK` layer discharging Inv-transport (`obligation_A_RGA`); namespace `Sal.ConditionedMRDTs.RGASig` |

## Update-side survivors

Of the original swap/faithfulness route only two files remain load-bearing
(the rest retired to `Development/` — the canonical-state engine subsumed
pairwise swapping):

| file | provides |
|---|---|
| `RGA_SubchainResolve.lean` | the Key Lemma: a captured live ancestor chain resolves to the current anchor (`subchain_resolve`) |
| `RGA_ConditionedConvergence.lean` | the `applySeqR` replay machinery and per-step goodness facts the canonical engine consumes |

## Canonical states and the two orders

The canonical-state characterization of reachable RGA states, and the
`loOnA` vs `loOnEq` bridge:

| file | provides |
|---|---|
| `RGA_CanonConvergence.lean` | `CanonMatch`, `CanonInv`, `CanonFoldOK` — the canonical-state characterization (`RGA_update_convergence_canon`) |
| `RGA_CanonFoldOK.lean` | `DepC`, `GenDisc2C`, `canonFoldOK_of_genDisc` — canonical folds from the generation discipline |
| `RGA_K1_DeltaDiscipline.lean` | K1: `canonFoldOK_delta` over canonical delta tuples |
| `RGA_K1_Wiring.lean` | K1 closure hypotheses discharged (`K1_canonFoldOK`, `exists_loOnA_perm`) |
| `RGA_GenDisc_Peel.lean` | the pointwise peel bricks (`isDepPreC_of_restrict`, `depC_mem_pastE`) |
| `RGA_DeltaEnum.lean` | a `loOnEq`-respecting enumeration of the delta exists (`exists_loOnEq_enum`) |
| `RGA_LoOnEq_Causal.lean` | `loOnEq` collapses to pure causal non-commutation for the RGA (`not_loOnEq_of_not_vis`) |

## Merge side

Merge linearization and the canonical shape of the merged state:

| file | provides |
|---|---|
| `RGA_MergeLinearization.lean` | `BranchInv`, the merge-linearization bridge (`eq_merge_branch_single`) |
| `RGA_MergeLinearization_TwoSided.lean` | the two-sided version, `BranchInv2` (`eq_merge_two_sided`) |
| `RGA_MergeBranchNew.lean` | GAP-1: the branch-new survivor anchor coincidence (`eq_merge_two_sided_of_foldChain`) |
| `RGA_MergeFoldChain.lean` | `CanonBirthBridge`; closing `FoldBirthChain` (`eq_merge_two_sided_final`) |
| `RGA_MergeCanon.lean` | the merge half of `hCanon` (`canonMatch_merge_of_inputs`) |
| `RGA_MergeCanon_Fix.lean` | the birth-anchor premise weakened and derived (`canonMatch_merge_of_inputs'`) |
| `RGA_BranchCanon.lean` | `CanonBirthBridge`'s merge-side residuals (`canonBirthBridge_via_branchCanon`) |
| `RGA_CanonBirthBridge.lean` | `canonBirthBridge_holds` |
| `RGA_MergeCong.lean` | merge congruence under `eq` (`merge_eq_congr_inv`) |

## Quotient instance and well-formedness

Instantiating the `QSig` quotient for the RGA, and the well-formedness
ladder `WfOp → WfOpQ → WfOpA`:

| file | provides |
|---|---|
| `RGA_EqQuotient.lean` | the RGA `QState` quotient basics (`accurate_eq_iff`, …) |
| `RGA_Instance.lean` | the framework instantiation: `rgaEqEquiv'`, `rgaCongVC'`, `rgaInvInvVC'` (`RGA_is_RA_linearizable`) |
| `RGA_InvFresh.lean` | `WfOp`; `RgaInv` preserved on any fresh op (`rgaInv_doOp_fresh`) |
| `RGA_InvUpdateQ.lean` | `qInv`, **`WfOpQ`** — the strengthened guard closing `InvPres` |
| `BornApplicable_Guard.lean` | **`WfOpA`** (= `WfOpQ` ∧ accurate ⟹ applicable) — born-applicability intrinsic to the quotient guard (`rga_appOrNoop_qsig`, `rgaInvPresA`) |
| `RGA_WfOpA_VCs.lean` | the remaining quotient VC at `WfOpA` (`rgaInvInvVCA`) |
| `RGA_Instance_Final.lean` | assembly over `WfOpQ` + the honestly-pinned Join residual (`rga_eqJoin_of_mergeFoldResidual`) |
| `RGA_Instance_NF.lean` | the born-applicable instantiation (`rga_RA_linearizable_NF`, `rga_invCong`) |
| `RGA_EqJoin_NF.lean` | the `≈`-Join in union canonical-state shape (`rga_eqJoin_of_mergeFoldResidual_NF`) |
| `RGA_Corrected_Residual.lean` | the corrected literal-fold residual: union re-enumerability instead of `noopFeasible π₀` (`rga_eqJoin_of_residualLit_NF2`) |

## Capstone dischargers and assembly

The four proof leaves of the H-parameterized metatheorem, discharged at
`H := rgaH` and `HonJ := rgaHonJ`, then the final reduction to
`HonestDelivery`:

| file | provides |
|---|---|
| `RGA_HEnum_Discharge.lean` | **`rgaHonJ`** (the join-context discipline) and hEnum (`rga_hEnum_discharged`) |
| `RGA_GenDisc_Assembly.lean` | `GenDisc2C` at reachable cores from born accuracy (`genDisc2C_of_born`) — consumed by the `HonCore` induction in `RGA_Honest_Residual.lean` |
| `RGA_FiltEq.lean` | the filtered-fold membership bridge (`hin_of_genDisc`) — consumed by `RGA_Hbridge_Discharge.lean` |
| `RGA_Hbridge_Discharge.lean` | hbridge: per-survivor `CanonBirthBridge` from the join context (`rga_hbridge_discharged`) |
| `RGA_HcausHdec_Discharge.lean` | hcaus + Hdec: hMergeInputs complete (`rga_hMergeInputs_discharged`) |
| `RGA_HHext_Discharge.lean` | hHext: the discipline extends at applicable applies (`rga_hHext_discharged`) |
| `RGA_Skeleton3.lean` | **`rgaH`** (= `CanonFoldOK` ∧ `HonestPayloads`) and the raw-`≈` capstone skeleton (`rga_RA_linearizable_skeleton3`) |
| `RGA_Skeleton3_Leaves.lean` | `hCanon` from the minimal merge bundle (`hCanon_of_leaves3`) |
| `RGA_Final_Assembly.lean` | **`rga_RA_linearizable_final`** — all proof-theoretic leaves discharged; residual = hHon + hBA |
| `RGA_Honest_Residual.lean` | **`HonestDelivery`** and the honest capstone **`rga_RA_linearizable_honest`** |
| `RA_Lin.lean` | the entry point: `rga_ra_linearizable3_eq` |

## History

Two strata of this chain's history live in
[`../../Development/`](../../Development/), all still 0-sorry:

- **The retired swap/faithfulness route** (seventeen files:
  `RGA_GeneralSwap`, `RGA_BothFaithfulSwap`, `RGA_BubbleWiring`,
  `RGA_ChainFaithful_doDel`, `RGA_EnablementBase`, `RGA_RecPathFaithful`,
  `RGA_InterleavedThreading`, `RGA_FaithfulThreading_Gate`,
  `RGA_StaledDel_Gate`, `RGA_Faithful_PBT`, `RGA_UpdateConvergence_Assembly`,
  `RGA_UpdateConvergence_Final`, `RGA_GenDischarge`, `RGA_ConvergenceEq`,
  `RGA_WfOpReachable`, `RGA_MergeThreadDischarge`, `RGA_OrderBridge`, plus
  `RGA_SwapRoute_Residuals.lean` with the bridge theorems cut from living
  files). This was the investigation's first attack — repair the flat
  theory's pairwise-swap argument under `Faithful` invariants. It is fully
  proved, and the capstone needs none of it: a kernel-level dependency
  audit showed the canonical-state engine subsumes it entirely.
- **Earlier capstone generations** (skeletons, assembly routes, discharge
  intermediates) retired in previous passes.

The negative results that shaped the chain are in
[`../../Refutations/`](../../Refutations/).
