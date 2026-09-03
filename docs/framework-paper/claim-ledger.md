# Framework paper claim ledger

This ledger maps each load-bearing paper claim to its machine-checked source.
It is an audit aid, not part of the paper's argument. The paper states the
definitions and theorems independently of Lean names.

| Paper claim | Lean evidence | Status / boundary |
| --- | --- | --- |
| The raw signature has one ancestor-aware `merge` and no independent binary merge, issuance, invariant, applicability, interaction, or replay-policy field. Paper `do` is Lean `MRDTSig.update`. | `Framework/Signature.lean`: `MRDTSig`; `Framework/Base/UpdateSignature.lean`: `UpdateSig`, `HistoricalBinaryMerge`; `Framework/Base/ReplayContext.lean`; `Framework/Execution.lean`: `Configuration.replayContext` | Machine-checked interface. `UpdateSig` is merge-free. Retained binary proofs request a separate historical capability whose MRDT instance is the initial-state slice; it defines no second execution semantics. `ReplayPolicy` is proof-local. |
| Raw execution has fork, apply, merge, and query; fork copies a source head into a fresh child, and ordinary merge reads an actual greatest common ancestor. | `Framework/Execution.lean`: `Configuration`, `Configuration.headState`, `Configuration.headEvents`, `IsGCA`, `IsMaximalCommonAncestor`, `Step`, `Step.fork_copies_source`, `Step.fork_head_ne_root`; `Metatheory/StoreInvariant.lean`: `isGCA_unique` | Machine-checked. Multiple incomparable maximal merge bases may exist; in that case there is no `IsGCA` witness. The paper and Lean use the same semantic configuration components. |
| A configuration-global replay order is insufficient. | `Metatheory/Join/Convergence_CounterModel.lean`: `convergence_over_backward_closed_subsets_false` | Machine-checked countermodel. |
| A fully GCA-legal execution of the published add-wins OR-set can bury both removes inside state-correct side witnesses, blocking the published bottom-up peel construction. | Published datatype at commit `8c22e47dc85a98991b2f77b8f5d010d852637dac`: `CaseStudies/Fstar_like_implementations/MRDTs/SAL/OR_Set_MRDT.lean`; historically checked one-element projection at commit `dbaded620a1f2667377ee326b603eaacfd222e2e`: `Sal/ConditionedMRDTs/Refutations/InterLca2op_Defeater_Arbiter.lean`, especially `awset_rem_output_empty`, `no_inter_lca_2op_rem_peel_of_defeater`, and `crack1_witness` | The paper gives the published element--timestamp presentation; the archived proof checks its one-element add/dead-set projection. Neither archived artifact is part of the current branch's Lean build, and the figure contracts snapshot-preserving fork versions. |
| A bounded join-semilattice merge plus the core update laws does not imply Join. | `Metatheory/Join/VC_Independence.lean`: `binaryLaws_insufficient` | Machine-checked countermodel. |
| Canonical states use a set-relative replay order. | `Metatheory/Join/SetRelativeReplay.lean`: `loOn`, `IsCanonicalState` | Machine-checked definition. |
| `JoinAt` is the single contextual merge-preservation obligation; `Join` requires it at every replay context and `JoinOn` restricts it by an explicit context predicate. All-context Join implies ordinary per-version replay linearizability. | `Framework/MergeLaws.lean`: `JoinAt`, `Join`, `JoinOn`; `Metatheory/Adequacy.lean`: `replayWitness_of_join` | Machine-checked. |
| `CanonicalJoinLaws` packages the reusable eight-obligation canonical-state contract for all-context Join; stronger universal equations are an adapter into this contract. | `Framework/ReplayLaws.lean`: `ReplayLaws`; `Framework/MergeLaws.lean`: `JoinCoreLaws`, `FeasibleDeltaLaws`, `CausalDeltaLaw`, `CanonicalJoinLaws`; `Metatheory/Adequacy.lean`: `CanonicalJoinLaws.join`, `CanonicalJoinLaws.ofArbitrary` | Machine-checked sufficient route, not mandatory public API. |
| Issuance restricts minting at the origin state; honest provenance persists as a trace certificate. | `Framework/Certificates.lean`: `Issuance`, `IssuedStep`, `MintHonest`, `MintCertifiedReach`, `MintCertifiedReachV` | Machine-checked. |
| Client correctness uses an independent interaction policy and sequential specification. | `Framework/Certificates.lean`: `InteractionSpec`, `interactionLoOn`, `SequentialSpec`; `Metatheory/Correctness.lean`: `IsSpecLinearizable`, `VerifiedMRDT` | Machine-checked public interface. |
| The LWW register has an empty proof-local replay order because timestamped `max` updates commute under the default `Either` policy, while its public interaction order has a constructive timestamp-sorted witness refining to a total overwrite register. | `Instances/LWWRegister.lean`: `replay_lo_false`, `canonical_respects`, `verified`, `timestamp_chain`, `chronological_winner`, `lower_timestamp_does_not_win` | Machine-checked. The timestamp-max representation and public ordering policy are trusted definitions; no JavaScript correspondence is claimed. |
| The observed-remove set refines tagged storage to an ordinary add-wins finite set, and honest issuance is load-bearing. | `Instances/ORSet.lean`: `spec`, `versionWellFormed_of_execution`, `setSequentialCorrectness`, `omitted_tag_breaks_ordinary_refinement` | Machine-checked positive theorem and negative control. The public remove ignores its observed-tag payload. |
| TreeMove's public sequential state is an ordinary tree, not a copy of its replicated event set. | `Instances/TreeMove.lean`: `spec`, `stateRel`, `sequentialSound` | Machine-checked after removing the dead proof-only event-set component. |
| Canonical virtual merge bases reuse the same Join obligation. | `Metatheory/VirtualMergeBase.lean`: `canonicalVirtualMergeBase`, `virtualMergeBaseState_canonical`; `Metatheory/Adequacy.lean`: `replayWitnessV_of_join` | Machine-checked. Synthetic bases are ghost state. |
| Distributed history GC needs only local head/commit holdings plus derived frontier evidence. | `GC/Distributed.lean`: `Local`, `Envelope`, `DerivedEvidence`, `EvidenceComplete`, `World` | Machine-checked logical protocol. Author and roster are fixed parameters, not duplicated local state. |
| Retention closed under pairwise maximal common ancestors preserves reachability and GCA answers without retaining the root or ancestor paths. | `GC/CompressedDAG.lean`; `GC/Distributed.lean`: `Certificate.ofMaximalCommonAncestorClosed` | Machine-checked. |
| The collecting protocol trace-refines the no-GC protocol. | `GC/Distributed.lean`: `refines_noGC`, `execution_refines_noGC`, `read_preserved` | Machine-checked store-level theorem. |
| Distributed history GC integrates with ordinary and virtual-merge-base MRDT execution. | `GC/Refinement.lean`: `runtime_refines_core`, `runtime_refines_coreV` | Machine-checked runtime lifting. Core configuration is ghost simulation state. |
| Datatype-state GC is optional and refines virtual execution by erasing silent steps. | `Framework/StateGC.lean`: `StateGCProtocol`, `StateGCProtocol.refines` | Machine-checked framework interface. |
| History GC and datatype-state GC compose. | `GC/StateComposition.lean`: `combinedProtocol`, `CombinedSteps.refinesV`, `CombinedSteps.refinesRaw` | Machine-checked. The two collectors remove different objects. |
| A production entry stores a name, a raw signature, and the complete public certificate for that exact signature. | `Metatheory/Correctness.lean`: `PackagedMRDT`; `Metatheory/ProductionLedger.lean` | Machine-checked packaging boundary. |

## Deliberate nonclaims

- The JavaScript runtime is validated and benchmarked; it is not extracted
  from Lean.
- The framework does not verify crash recovery or a hostile-network threat
  model.
- Root-free collection preserves completed traces; it does not prove liveness
  of every future fork or merge under arbitrary message loss.
- A state-GC protocol is not supplied by the framework for every datatype.
- The reusable VC decomposition is sufficient, not necessary; an implementer
  may prove contextual Join directly.
- Internal replay linearizability is not the client theorem. The public result
  additionally requires legality, representation agreement, and query
  agreement with an independent sequential specification.
