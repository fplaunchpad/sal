# `Conditioned/` — the proof cone of the conditioned metatheory

This directory holds every Lean file the two mainline entry points depend on:

| entry point (in `Sal/MRDTs/Metatheory/`) | main theorem | what it says |
|---|---|---|
| `RGA_TombstoneFree_RA_Lin.lean` | `rga_tombstone_free_ra_linearizable3_eq` | the tombstone-free RGA is per-version RA-linearizable up to `≈` at every reachable configuration, assuming only `HonestDelivery` (per-step born accuracy + born-applicable delivery) |
| `MRDT_Instances_Generic.lean` | `*_ra_linearizable3_eq` (11 theorems) | every flat production MRDT is RA-linearizable through the same generic framework, at the identity instantiation (`≈` = `=`, `Inv` = `applicable` = `⊤`) |

It exists so that the mainline root of `Sal/MRDTs/Metatheory/` never imports
`Development/`. The layering contract is:

- **root** (`Sal/MRDTs/Metatheory/*.lean`) may import `Conditioned/`, never `Development/`;
- **`Conditioned/`** may import the root core (`MRDTSig`, `Sigma_LoOn3`, `Adequacy`, …)
  and itself, never `Development/`;
- **`Development/`** may import anything. Superseded or exploratory files live there.

Everything here is kernel-clean: axioms ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}, zero `sorry`.

A file-naming note: several files keep the name of the *investigation* that
produced them (`*_Probe`, `*_Gate`, `G2_*`). The load-bearing definitions that
were first written inside those investigations now live in properly-named
homes — `RGA_CondSig.lean` (the signature), `LoOnC.lean` (the baseline order),
`NoopFeasible.lean` (the feasibility predicate) — and the investigation files
keep what their names promise: the counterexamples, gates, and verdicts.

## `Base/` — the transition-system core

The vendored LTS and CRDT-signature layer. These files carry the
`Sal.Emulation` namespace (they originated in the emulation study, and the
top-level `Sal/Emulation/*.lean` files are forwarding stubs that re-export
them), but the directory is named for what it is here: the base layer the
metatheory's `Configuration` lives in. It was moved into the metatheory tree
because the metatheory extends `Configuration` with structural fields
(Lamport-monotone timestamps, per-replica visibility totality) that the
honest-execution reduction treats as part of the execution model.

| file | provides |
|---|---|
| `Base/Labeled_TS.lean` | `LabeledTS`, `Steps`, `Execution`, `Reachable`, `ReachableFrom` |
| `Base/CRDT_Signature.lean` | `Op`, `Timestamp`, `Replica`, `CRDTSig`, `RcRes`, `applySeq` |
| `Base/CRDT_TS.lean` | `Configuration` (with the structural fields), `Label`, `Step`, `initConfig`, `lo`/`loOn`, `IsCanonicalState` |

## The generic conditioned framework (datatype-generic)

In dependency order. This is ONE framework: a `ConditionedMRDTSig`
(⟨Σ, σ₀, do, merge, mergeL, rc, Inv, applicable⟩) plus an observational
equivalence bundle `EqEquiv` (`≈`), with a single `≈`-parameterized definition
of RA-linearizability.

| file | provides |
|---|---|
| `LoOnC.lean` | **`loOnC`** — the set-relative conditioned linearization order (`lo` with `commutes ↦ commutesOn`), the baseline the update layer runs against |
| `NoopFeasible.lean` | **`noopFeasible`** — the relaxed feasibility predicate (each op applicable or a no-op at its prefix-fold) |
| `G2_Transport_Probe.lean` | the G2 refutation: unconditioned applicability-transport fails (`G2_conditioned_convergence_refuted`), with the `insOpE`/`delOpE` counterexample; the ⚑-site map of the convergence induction |
| `G2_Applicability_Aware.lean` | the probe-level `loOnA`/`appliesDependsOn` and the separation results against plain `loOnC` (the framework's `loOnA` is `ConditionedConvergence.lean`) |
| `UpdateFeasibility_Gate.lean` | the `Del` no-op algebra and the verdict that `loOnA + noopFeasible` is the right feasibility notion (`loOnA_noopFeasible_verdict`) |
| `Reunification_Peel_Obstruction.lean` | the K2 example (`K2Op`, `k2Update`, …) proving the full-closure peel does not exist (`reunification_peel_obstruction`); `JoinLemma3C.lean` reuses the K2 machinery for its boundary results |
| `JoinLemma3C.lean` | `ClosurePred` (`weakClosure`/`fullClosure`), **`JoinLemma3C 𝒞`** — the closure-indexed Join Lemma — and the peel-compatibility boundary |
| `GenericEqQuotient.lean` | **`EqEquiv`** (`≈`), `CongVC`, `InvInvVC`, `InvState`, the **`QSig` quotient functor** `D ↦ D≈`, and the conditioned metatheorem up to `≈` (`RA_linearizable_up_to_eq`) |
| `GenericEqQuotient_NF.lean` | the born-applicable (`noopFeasible`) rendering: `IsCanonicalStateEqNF`, `EqJoinLemma3C_NF` |
| `GenericEqQuotient_H.lean` | the H-parameterized rendering: feasibility clause replaced by an abstract delivery discipline `H` (`IsCanonicalStateEqH`, `EqJoinLemma3C_H`) |
| `GoodConfig3NF.lean` | the reachability invariant `GoodConfig3NF` and `RA_linearizable_up_to_eq_NF` |
| `GoodConfig3H.lean` | `GoodConfig3S`, `GoodConfig3H`, **`IsRALinearizable3Eq`** (THE definition of RA-linearizability up to `≈`), and **`RA_linearizable_up_to_eq_H`** — the metatheorem the RGA capstone instantiates |
| `ConditionedContract.lean` | `ConditionedContract` (fields `D`, `𝒞`, `join`, …) with `ofVCs`/`ofJoinF` constructors — the data an instance supplies |
| `ConditionedConvergence.lean` | the conditioned convergence theorem: `commutesOn`-swaps under `Inv` + joint applicability (`applySeq_swap_commutesOn`, `UpdateVCsC`) |
| `ConditionedExecutionModel.lean` | `ConditionedConfiguration`, `BackClosed`, enumeration existence lemmas (`exists_loOnA_noopFeasible_enum`) |
| `FlatGeneric_Bridge.lean` | the **flat collapse**: `eqOfEq` (identity `≈`), `WTop`, `eqCommutesOn_iff_commutes`, the synthetic `flatCfg`, and **`flat_ra_linearizable3_eq`** — how all 11 flat instances ride the one framework |

## The tombstone-free RGA instance chain

The RGA (`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean`)
instantiated into the framework. The signature every file below builds on:

| file | provides |
|---|---|
| `RGA_CondSig.lean` | **`RGAM`** (the raw `MRDTSig`: `do_`, three-way merge, `rc = Either`) and **`RGACondSig`** (`Inv := RgaInv`, `applicable := accurate ∧ fresh_ts`), plus the order-stable `opOK` layer discharging Inv-transport (`obligation_A_RGA`); namespace `Sal.Metatheory.RGASig` |

Sub-chains, each in dependency order.

**Update-side swaps and faithfulness** — commutation of concurrent updates,
conditioned on the `Faithful`/`ChainFaithful` state predicates:

| file | provides |
|---|---|
| `RGA_GeneralSwap.lean` | the general update-side swap VC under `Faithful` (`general_swap`) |
| `RGA_BothFaithfulSwap.lean` | the BOTH-`Faithful` swap (`general_swap_bothFaithful`) |
| `RGA_BubbleWiring.lean` | `ChainFaithful`, wiring the swap into the bubble-sort argument (`chainFaithful_doIns`) |
| `RGA_ChainFaithful_doDel.lean` | `ChainFaithful` preserved by accurate `Del` (`chainFaithful_doDel`) |
| `RGA_Faithful_PBT.lean` | executable `chainFaithfulB` + SPOT harness; `RGA_StaledDel_Gate` uses the executable forms |
| `RGA_StaledDel_Gate.lean` | the staled-`Del` gate: locates the clash-`Ins` obstruction (`chainFaithful_not_preserved_under_clash_ins`) |
| `RGA_FaithfulThreading_Gate.lean` | the faithful-threading gate: `chainFaithful_incompStep`/`_incompFold` |
| `RGA_EnablementBase.lean` | the enablement base lemma (`faithful_at_enablement_ins`) |
| `RGA_SubchainResolve.lean` | the Key Lemma: a captured live ancestor chain resolves to the current anchor (`subchain_resolve`) |
| `RGA_RecPathFaithful.lean` | per-event faithfulness in reachable folds (`faithful_of_recPathFaithful`) |
| `RGA_InterleavedThreading.lean` | faithfulness through interleaved folds (`faithful_at_interleaved_fold`) |
| `RGA_UpdateConvergence_Assembly.lean` | stage-1 assembly facts (`fresh_ts_state_of_ids`) |
| `RGA_UpdateConvergence_Final.lean` | the update-layer capstone (`RGA_update_convergence`) |
| `RGA_GenDischarge.lean` | per-event generation discipline `GenDisc` ⟹ update-layer bundle (`RGA_update_convergence_genDisc`) |
| `RGA_ConditionedConvergence.lean` | RGA conditioned convergence up to `eq` (`RGA_conditioned_convergence_bothFaithful`) |

**Canonical states and the two orders** — the canonical-state
characterization of reachable RGA states, and the `loOnA` vs `loOnEq` bridge:

| file | provides |
|---|---|
| `RGA_CanonConvergence.lean` | `CanonMatch`, `CanonInv`, `CanonFoldOK` — the canonical-state characterization (`RGA_update_convergence_canon`) |
| `RGA_CanonFoldOK.lean` | `DepC`, `GenDisc2C`, `canonFoldOK_of_genDisc` — canonical folds from the generation discipline |
| `RGA_K1_DeltaDiscipline.lean` | K1: `canonFoldOK_delta` over canonical delta tuples |
| `RGA_K1_Wiring.lean` | K1 closure hypotheses discharged (`K1_canonFoldOK`, `exists_loOnA_perm`) |
| `RGA_GenDisc_Peel.lean` | the pointwise peel bricks (`isDepPreC_of_restrict`, `depC_mem_pastE`) |
| `RGA_DeltaEnum.lean` | a `loOnEq`-respecting enumeration of the delta exists (`exists_loOnEq_enum`) |
| `RGA_LoOnEq_Causal.lean` | `loOnEq` collapses to pure causal non-commutation for the RGA (`not_loOnEq_of_not_vis`) |
| `RGA_OrderBridge.lean` | `loOnEq` vs `loOnA` are incomparable; `rc_is_Either'` |
| `RGA_ConvergenceEq.lean` | convergence and merge bridge over the framework's `loOnEq` (`canonFoldOK_of_loOnEq`, `eq_merge_two_sided_eq`) |

**Merge side** — merge linearization and the canonical shape of the merged
state:

| file | provides |
|---|---|
| `RGA_MergeLinearization.lean` | `BranchInv`, the merge-linearization bridge (`eq_merge_branch_single`) |
| `RGA_MergeLinearization_TwoSided.lean` | the two-sided version, `BranchInv2` (`eq_merge_two_sided`) |
| `RGA_MergeThreadDischarge.lean` | `BranchInv2` from pieces at reachable configs (`eq_merge_two_sided_of_reachable`) |
| `RGA_MergeBranchNew.lean` | GAP-1: the branch-new survivor anchor coincidence (`eq_merge_two_sided_of_foldChain`) |
| `RGA_MergeFoldChain.lean` | `CanonBirthBridge`; closing `FoldBirthChain` (`eq_merge_two_sided_final`) |
| `RGA_MergeCanon.lean` | the merge half of `hCanon` (`canonMatch_merge_of_inputs`) |
| `RGA_MergeCanon_Fix.lean` | the birth-anchor premise weakened and derived (`canonMatch_merge_of_inputs'`) |
| `RGA_BranchCanon.lean` | `CanonBirthBridge`'s merge-side residuals (`canonBirthBridge_via_branchCanon`) |
| `RGA_CanonBirthBridge.lean` | `canonBirthBridge_holds` |
| `RGA_MergeCong.lean` | merge congruence under `eq` (`merge_eq_congr_inv`) |

**Quotient instance and well-formedness** — instantiating the `QSig` quotient
for the RGA, and the well-formedness ladder `WfOp → WfOpQ → WfOpA`:

| file | provides |
|---|---|
| `RGA_EqQuotient.lean` | the RGA `QState` quotient basics (`accurate_eq_iff`, …) |
| `RGA_Instance.lean` | the framework instantiation: `rgaEqEquiv'`, `rgaCongVC'`, `rgaInvInvVC'` (`RGA_is_RA_linearizable`) |
| `RGA_InvFresh.lean` | `WfOp`; `RgaInv` preserved on any fresh op (`rgaInv_doOp_fresh`) |
| `RGA_InvUpdateQ.lean` | `qInv`, **`WfOpQ`** — the strengthened guard closing `InvPres` |
| `RGA_WfOpReachable.lean` | `WfOpGen`; the `WfOpReachable` VC (`rga_wfOpReachable`) |
| `BornApplicable_Guard.lean` | **`WfOpA`** (= `WfOpQ` ∧ accurate ⟹ applicable) — born-applicability intrinsic to the quotient guard (`rga_appOrNoop_qsig`, `rgaInvPresA`) |
| `RGA_WfOpA_VCs.lean` | the remaining quotient VC at `WfOpA` (`rgaInvInvVCA`) |
| `RGA_Instance_Final.lean` | assembly over `WfOpQ` + the honestly-pinned Join residual (`rga_eqJoin_of_mergeFoldResidual`) |
| `RGA_Instance_NF.lean` | the born-applicable instantiation (`rga_RA_linearizable_NF`, `rga_invCong`) |
| `RGA_EqJoin_NF.lean` | the `≈`-Join in union canonical-state shape (`rga_eqJoin_of_mergeFoldResidual_NF`) |
| `RGA_Corrected_Residual.lean` | the corrected literal-fold residual: union re-enumerability instead of `noopFeasible π₀` (`rga_eqJoin_of_residualLit_NF2`) |

**Capstone dischargers and assembly** — the four proof leaves of the
H-parameterized metatheorem, discharged at `H := rgaH` and
`HonJ := rgaHonJ`, then the final reduction to `HonestDelivery`:

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
| `RGA_Honest_Residual.lean` | **`HonestDelivery`** and the honest capstone **`rga_RA_linearizable_honest`** — the theorem the mainline entry point re-exports |

## Retired files

On 2026-07-07, thirteen files that earlier generations of the proof produced
but the living chain no longer consumes were moved back to `Development/`
(each was imported only for its import chain; no declaration of any of them is
used by the cone): `RGA_CanonMatch_Reachable`, `RGA_Corrected_Assembly`,
`RGA_EndToEnd`, `RGA_EqJoin_NF_Assembly`, `RGA_EqJoin_NF_Residual`,
`RGA_GenDisc_Assembly` — retracted, see below — `RGA_GenDischarge2`,
`RGA_HinFilterEq`, `RGA_NoopFeasible_CanonFold`, `RGA_ReachDischarge`,
`RGA_Skeleton`, `RGA_Skeleton2`, `RGA_UpdateConvergence`, `RGA_hCanon_Glue`.
They still build there (`Development/` may import `Conditioned/`), and record
earlier assembly routes — e.g. `RGA_EndToEnd` is the pre-honest capstone over
the NF residual, and `RGA_Skeleton`/`RGA_Skeleton2` are the first two capstone
skeletons that `RGA_Skeleton3` superseded.

Two candidates were retracted from that retirement because a *transitive*
importer consumes a declaration of theirs even though no direct importer does:
`RGA_FiltEq` (`hin_of_genDisc`, used by `RGA_Hbridge_Discharge`) and
`RGA_GenDisc_Assembly` (`genDisc2C_of_born`, used by `RGA_Honest_Residual`).
Both consumers now import them directly, so the dependency is visible in the
import graph.
