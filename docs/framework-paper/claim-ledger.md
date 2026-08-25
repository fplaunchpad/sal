# Framework paper claim ledger

This ledger maps each load-bearing paper claim to its machine-checked source.
It is an audit aid, not part of the paper's argument. The paper states the
definitions and theorems independently of Lean names.

| Paper claim | Lean evidence | Status / boundary |
| --- | --- | --- |
| The raw signature has one ancestor-aware `merge` and no independent binary merge, issuance, invariant, applicability, interaction, or replay-policy field. | `Framework/Signature.lean`: `MRDTSig`, `MRDTSig.toCRDTSig_merge` | Machine-checked interface. The binary merge used by older replay infrastructure is the derived initial-state slice; `ReplayPolicy` is proof-local. |
| Raw execution has create, apply, merge, and query; merge reads an actual LCA. | `Framework/Execution.lean`: `Configuration`, `Step` | Machine-checked. Paper omits only the derivable `N` and `L` caches. |
| A configuration-global replay order is insufficient. | `Metatheory/Join/Convergence_CounterModel.lean`: `convergence_over_backward_closed_subsets_false` | Machine-checked countermodel. |
| A bounded join-semilattice merge plus the core update laws does not imply Join. | `Metatheory/Join/VC_Independence.lean`: `coreVCs_lattice_insufficient` | Machine-checked countermodel. |
| Canonical states use a set-relative replay order. | `Metatheory/Join/Merge_Linearization_Set.lean`: `loOn`, `IsCanonicalState` | Machine-checked definition. |
| Contextual ternary Join implies ordinary per-version replay linearizability. | `Framework/VCSet.lean`: `JoinLemma3`; `Metatheory/Adequacy.lean`: `ra_linearizable3_of_join` | Machine-checked. |
| The reusable eight-obligation route implies Join. | `Framework/SigmaLoOn.lean`: `UpdateVCs`; `Framework/VCSet.lean`: `CoreVCs3CD`, `FeasibleDeltaVCs3`, `CDVC3`; `Metatheory/Adequacy.lean`: `join_lemma3_of_cd_feasible` | Machine-checked sufficient route, not mandatory public API. |
| Issuance restricts minting at the origin state; honest provenance persists as a trace certificate. | `Framework/Certificates.lean`: `Issuance`, `IssuedStep`, `MintHonest`, `MintCertifiedReach`, `MintCertifiedReachV` | Machine-checked. |
| Client correctness uses an independent interaction policy and sequential specification. | `Framework/Certificates.lean`: `InteractionSpec`, `interactionLoOn`, `SequentialSpec`; `Metatheory/Correctness.lean`: `IsSpecRALinearizable`, `VerifiedMRDT` | Machine-checked public interface. |
| Canonical virtual LCAs reuse the same Join obligation. | `Metatheory/VirtualLCA.lean`: `canonicalVirtualLCA`, `virtualLCAState_canonical`; `Metatheory/Adequacy.lean`: `ra_linearizable3V_of_join` | Machine-checked. Synthetic bases are ghost state. |
| Distributed history GC needs only local head/commit holdings plus derived frontier evidence. | `GC/Distributed.lean`: `Local`, `Envelope`, `DerivedEvidence`, `EvidenceComplete`, `World` | Machine-checked logical protocol. Author and roster are fixed parameters, not duplicated local state. |
| MCA-closed retention preserves reachability and LCA answers without retaining the root or ancestor paths. | `GC/CompressedDAG.lean`; `GC/Distributed.lean`: `Certificate.ofMCAClosed` | Machine-checked. |
| The collecting protocol trace-refines the no-GC protocol. | `GC/Distributed.lean`: `refines_noGC`, `execution_refines_noGC`, `read_preserved` | Machine-checked store-level theorem. |
| Distributed history GC integrates with ordinary and virtual-LCA MRDT execution. | `GC/Refinement.lean`: `runtime_refines_core`, `runtime_refines_coreV` | Machine-checked runtime lifting. Core configuration is ghost simulation state. |
| Datatype-state GC is optional and refines virtual execution by erasing silent steps. | `Framework/StateGC.lean`: `StateGCProtocol`, `StateGCProtocol.refines` | Machine-checked framework interface. |
| History GC and datatype-state GC compose. | `GC/StateComposition.lean`: `combinedProtocol`, `CombinedSteps.refinesV`, `CombinedSteps.refinesRaw` | Machine-checked. The two collectors remove different objects. |
| Production entries carry the complete public certificate for the exact signature. | `Metatheory/Correctness.lean`: `PackagedMRDT`; `Production/Registry.lean` | Machine-checked packaging boundary. |

## Deliberate nonclaims

- The JavaScript runtime is validated and benchmarked; it is not extracted
  from Lean.
- The framework does not verify crash recovery or a hostile-network threat
  model.
- A state-GC protocol is not supplied by the framework for every datatype.
- The reusable VC decomposition is sufficient, not necessary; an implementer
  may prove contextual Join directly.
- Internal replay linearizability is not the client theorem. The public result
  additionally requires legality, representation agreement, and query
  agreement with an independent sequential specification.
