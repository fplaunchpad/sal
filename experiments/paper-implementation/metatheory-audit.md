# Implementation-section metatheory audit

Read-only source audit on `sal` branch `paper1`, HEAD `c9e945d62cb04e26515e35a7792ff91d0b7addf0`, 14 October 2026. The updated manuscript was read from `/Users/kc/repos/Sal_paper` after the parent pulled Overleaf `6b2d00f`. No production source was edited.

## Suggested scholarly prose

The Lean development checks the sufficient-condition argument from algebraic merge obligations to exact state reconstruction, convergence, and explicit per-query RA-linearizability. The proof retains the representation, replay-supply, metadata-closure, and issuance hypotheses needed by each datatype. It covers finite executions with ordinary ancestors and recursively synthesized virtual merge bases. Independent sequential simulations or execution-scoped histories connect implementation replay to admitted specification histories. Representation and specification simulation serve different purposes: the former reconstructs the concrete implementation state; the latter establishes the meaning of its query answers.

The selected generic theorem dependencies comprise 4,020 nonblank, noncomment lines of Lean theorem statements and proofs, with a further 1,688 lines proving the shared automation templates sound. Their associated definitions occupy 917 and 258 lines respectively. These are dependency-closure measurements, not all-source or tactic-body-only counts. The audited generic endpoints use only Lean's standard logical axioms.

The parent’s draft `/private/tmp/sal-implementation-draft/implementation.tex` already makes the important representation/replay premises explicit and is accurately scoped. Retain “selected generic theorem dependencies”; do not replace it with “the full formalization has 4,020 proof lines.”

## Checked theorem chain and evidence

All paths below are relative to `/Users/kc/repos/sal`.

| Stage | Checked evidence and source | Load-bearing scope |
|---|---|---|
| Public history language | `HistorySpec`, `HistoryMachine.toSpec`, `Paper1/HistorySpec.lean:20,62` | Admission is a prefix-closed language; finite-path acceptance does not assume totality or determinism. Labels may retain complete events or an explicitly selected projection. |
| Explicit RA criterion | `RALinearizable`, `VersionsRALinearizable`, `UniformVersionsRALinearizable`, `Paper1/RALinearizability.lean:24,36,47` | Literal public predicate quantifies over each active replica and query. Historical-version and uniform-witness predicates are separately stronger. The active mathematical predicate has no issuance premise; certification restricts the guarantee. |
| Full-event/specification-visible criterion | `EventVersionsSpecificationRA`, `EventBridge.lean:66`; `VersionsWitness`, `ConcreteFormalism.lean:34` | Requires the same original-event permutation to respect implementation order and specification-conflicting visibility and to explain the stored query. Do not identify this silently with the older payload-only literal criterion. |
| Exact representation and canonicality | `Representation`, `RepresentationJoin`, `Canonical`, `Paper1/ConcreteFormalism.lean:10,13,29` | State equality is actual Lean equality. Replay is exact equality with a fold from the initial implementation state. |
| Five equations | `Raw.MergeVCs`, `Paper1/ConcreteJoin.lean:39` | Indexed by representation and metadata scheme; fields are `merge_comm`, `init`, `causal_delta`, `local_redistribute`, `shared`. Reconstruction hypotheses on smaller unions remain explicit. |
| Replay/peel prerequisites | `Raw.Unique`, `Raw.ReplaySupply`, `Raw.PeelChoice`, `Paper1/ConcreteJoin.lean:69,71,20` | Unique represented state, finite replay supply, and a represented peel witness maximal for both semantic order and metadata dependencies. The witness represents the remainder and operation past and reconstructs both after the peeled event. |
| Five VCs to Join | `Raw.join_at_sizes`, `Raw.representationJoin_of_vcs`, `Paper1/ConcreteJoin.lean:212,376` | Strict event-set induction. No Join or canonical-merge preservation premise is supplied. Needs five equations plus uniqueness, initial representation, finite enumerability and replay supply. |
| Global guarded determinacy | `convergence_on_guarded`, `Paper1/GuardedConvergence.lean`; `ConcreteMRDT.replay_equal`, `canonical_unique`, `canonical_exists`, `Paper1/ConcreteReplay.lean:10,21,37` | Exact equality of folds for the chosen guarded semantic order on supported event sets; finite supported strict causal context for enumeration/existence. Guarded laws retain timestamp and replica restrictions. |
| Scoped determinacy | `InvariantReplay.convergence_on`, `canonical_unique`, `Paper1/InvariantReplay.lean:183,203` | Legal replay and invariant scope are part of the theorem. It cannot be applied to every raw permutation that happens to respect an invariant-derived order. |
| Merge-base bookkeeping | `gca_events_of_storeInv`, `Metatheory/StoreInvariant.lean`; `CertifiedClosedExecution.virtualMergeBaseState_canonical`, `Paper1/CertifiedClosedExecution.lean:187` | Store invariants justify event-set intersections; recursive antichain merging reconstructs a canonical state for the intersection of the two heads’ event sets. |
| All stored versions in ordinary/recursive execution | `CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV`, `canonicalConfig_of_execution`, `replayWitness_of_execution`, `Paper1/CertifiedClosedExecution.lean:205,258,265` | Contextual `ClosedJoinAt` plus explicit original-issuance/mint provenance. Ordinary executions embed into the widened virtual semantics. Store and representation invariants are maintained together. |
| Literal sequential lifting | `PaperPresentation.uniform_versionsRA_of_paperOrder_witness`, `Paper1/PaperPresentation.lean:18` | Given exact witnesses in public paper order plus global merge-free `FoldHistorySound`, one witness explains every query at every stored version. No repeated replay law is needed merely to reuse the exact word. |
| Independent simulation | `SequentialSimulation.fold_rel`, `sound`, `Paper1/SequentialSimulation.lean:20,28`; `EventSequentialSimulation.sound`, `EventBridge.lean:48` | Init/update/query relation yields admitted update-fold history in an independent deterministic total specification; event version retains complete inputs. This is a sufficient proof method, not a restriction on all history languages. |
| Specification-visibility compatibility | `CommutationCompatibility`, `projectedSpecVisibility_sub_paperOrder`, `specificationRA_of_fiveVCs_compatible`, `Paper1/CommutationBridge.lean:20,37,62` | Concrete commutation implies contextual specification commutation. Contraposition covers specification-conflicting visibility. Payload/full-event projections and raw/invariant commutation domains must match the theorem used. |
| Chosen history under certified execution | `ConcreteMRDT.versions_of_scoped_history`, `ScopedCertificate.convergence`, `executionsV`, `Paper1/ConcreteHistoryBridge.lean:30,86,111` | Execution-scoped history adequacy selects an admitted fold; exact canonical uniqueness identifies it with the separately represented stored state. Result covers every stored version and each visited configuration of a finite trace. |
| Representation-sensitive alternative | `CertifiedHistory.versions_of_representation`, `storedCanonical`, `Paper1/CertifiedHistoryBridge.lean:30,45` | Uniqueness only in certified contexts; independent represented history can be transported even without the global guarded-law contract. Does not discharge merge VCs. |
| Packaged generic sufficient conditions | `ConcreteMRDT.VCReplayConditions.join`, `ScopedVCConditions.executionsV`, `Paper1/ConcreteVCExecution.lean:38,91` | `VCReplayConditions` retains representation, laws, five VCs, uniqueness, initialization, finite replay, canonicality, support, replay supply, and `representedVersions`. The final certificate must establish these premises. |
| Issuance-sensitive and execution-sensitive soundness | `certifiedRA_of_fiveVCs_issued`, `Soundness.lean:111`; `event_certified_of_fiveVCs_issued`, `event_certified_of_fiveVCs_execution`, `EventBridge.lean:212,221` | Ordinary and recursive certified guarantees; event-sensitive version preserves complete timestamp/replica/operation inputs. Independent history premise remains additional to the merge equations. |
| Split self-commutation interfaces | `SplitPolicy.laws_iff_guarded`, `Certified.restricted_iff_existing`, `Invariant.restricted_iff_existing`, `Paper1/SplitPolicy.lean:76,155,237`; `SplitPolicy.Concrete.ScopedVCConditions.executionsV`, `SplitSoundness.lean:106` | Current split formulation separates operation-distinct noncommutation exactness and equal-operation self-commutation, with unchanged state/event domains. Conversion equivalence is checked; soundness is exposed through the split interface. |
| Declarative automation to the original five equations | `Automation.CommonVerification.verify`, `Paper1/Automation/CommonVerification.lean:96`; `GenericCertifiedRecords.five_vcs`, `Automation/GenericCertifiedRecords.lean:95` | Input constructors supply finite kits/evidence projections. Generic soundness returns exactly `Raw.MergeVCs`. No datatype VC theorem is an input to this common verifier. |

There is no declaration literally named `expandedVCs` in current `Sal` sources. If manuscript terminology refers to expanded local obligations, connect it to the generic expansion/assembly modules and `CommonVerification.verify`, and to the actual instance’s `mergeVCs` or `fiveVC` endpoint. Do not print an invented Lean declaration name in artifact citations.

Important dependency distinction: `ConcreteVCExecution.VCReplayConditions` receives `representedVersions` as a field; `ScopedVCConditions.executionsV` transports this supplied evidence and does not itself call `.join`. The datatype endpoint audits in `Paper1/Ledger.lean` traverse proofs and require both actual datatype VC obligations and `ConcreteJoin.join_at_sizes`, rejecting obsolete direct-Join/history-merge routes. These audits establish that the actual production representation proofs consume the new five-VC derivation. A generic certificate’s type alone is insufficient evidence of that dependence.

## Reproducible source measurement

Run:

```sh
python3 experiments/paper-implementation/measure_metatheory.py --repo . --out /tmp/sal-paper-metatheory --repo /Users/kc/repos/sal --out /private/tmp
```

Artifacts:

- `/private/tmp/sal-count-metatheory.py`: script and selected roots.
- `/private/tmp/sal-metatheory-count.lean`: generated Lean dependency traversal.
- `/private/tmp/sal-metatheory-count.log`: current source ranges, axiom closures, and completion records.
- `/private/tmp/sal-metatheory-count.json`: per-declaration and per-file results.

The script reuses `LEAN_AUDIT` from `scripts/verify-paper1-automation.py`, and `strip_comments` from `scripts/check-paper1-automation-contracts.py`. It invokes `lake env lean` on the generated audit, traverses each root’s used constants, obtains source ranges using `findDeclarationRanges?`, unions line indices within category, and counts nonblank lines after nested Lean block/line comments are removed. Theorem source includes the complete declaration (statement and proof). Generated declaration ranges are deduplicated; overlaps between theorem and definition ranges are assigned to theorem source, preventing double charging. Definitions include proposition/certificate/structure definitions and their generated projections/recursors; they are not a claim about executable implementation LOC. No ranges from Mathlib, Lean, Blaster, or other dependencies outside `Sal` are charged.

| Selected closure category | Complete theorem declarations | Theorem NBNC source lines | Definition NBNC source lines |
|---|---:|---:|---:|
| Generic Paper1 and MRDT metatheory | 191 | 3,261 | 486 |
| Framework and interface infrastructure | 63 | 759 | 431 |
| Shared automation | 172 | 1,688 | 258 |
| Datatype dependency (excluded from generic totals) | 0 | 0 | 11 |
| Generic metatheory + framework/interfaces | 254 | **4,020** | **917** |

The 11 excluded datatype lines are `Sal/MRDTs/Instances/FinsetStore.lean`’s generic MRDT carrier definition, reached through automation’s commuting transfer library.

Exactly ten roots were audited:

1. `Sal.MRDTs.Paper1.ConcreteMRDT.Raw.representationJoin_of_vcs`
2. `Sal.MRDTs.Paper1.ConcreteMRDT.ScopedVCConditions.executionsV`
3. `Sal.MRDTs.Paper1.ConcreteMRDT.VCConditions.executionsV`
4. `Sal.MRDTs.Paper1.ConcreteMRDT.replay_equal`
5. `Sal.MRDTs.Paper1.CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV`
6. `Sal.MRDTs.Paper1.PaperPresentation.uniform_versionsRA_of_paperOrder_witness`
7. `Sal.MRDTs.Paper1.InvariantReplay.convergence_on`
8. `Sal.MRDTs.Paper1.SplitPolicy.Concrete.ScopedVCConditions.executionsV`
9. `Sal.MRDTs.Paper1.Automation.CommonVerification.verify`
10. `Sal.MRDTs.Paper1.event_certified_of_fiveVCs_execution`

This selection covers a complete generic sufficient-condition chain, including guarded determinacy, five-VC Join induction, certified virtual/ordinary store representation, execution-sensitive sequential lifting, invariant convergence, the split contract adapter, and shared VC assembly. It excludes datatype-specific propagation/selected-history constructions, GC/safety metatheory, unrelated generic alternatives, and tests/controls. In particular `CertifiedHistory.versions_of_representation`, `SequentialSimulation.sound`, and all the separately useful lifted variants are not roots of this source count. Do not describe the selected closure as an exhaustive repository metatheory total.

## Trust evidence

The generated audit succeeded with all ten roots resolved and all completion records present. Nine roots have some subset of exactly `propext`, `Classical.choice`, `Quot.sound`; the direct `uniform_versionsRA_of_paperOrder_witness` lifting theorem has an empty axiom set. No audited root uses `sorryAx` or native-evaluation trust.

`Paper1/Ledger.lean:99` defines `assert_paper_axioms` with a whitelist of these three standard axioms. It checks load-bearing positive/negative endpoints and traverses selected dependencies to forbid old correctness shortcuts. `scripts/check-paper1.sh` builds that ledger and rejects textual `sorry`, `sorryAx`, and top-level `axiom` in Paper1 source. The source scan found none in Paper1/Framework/Metatheory. Lean is pinned to 4.28.0 (`lean-toolchain`), Mathlib to v4.28.0 (`lakefile.toml`). A full build was not rerun in this read-only subtask; current built imports resolved and the new kernel dependency/axiom audit passed.

A blanket claim that all validation examples avoid native computation is false: `Paper1/CertifiedRGAHistoryControls.lean:28` uses `native_decide`, and `Metatheory/Countermodels/TaggedORSet.lean:957–991` contains native-decided controls. These are not dependencies of the ten generic proof roots. Phrase trust as “the audited theorem endpoints depend only on Lean’s standard logical axioms.” Handwritten JavaScript correspondence remains executable evidence, not extraction/refinement of runtime bytes.

## Remaining manuscript-to-checked-statement differences

These are corrections for later theory-section editing, rather than reasons to weaken the accurate implementation paragraph.

1. **Five VCs alone do not discharge all representation machinery.** Current `proof_strategy.tex` Theorem `thm:adequacy` and Join lemma suppress replay existence, representation uniqueness, and represented peel/reconstruction prerequisites. `ConcreteJoin` checks a precise sufficient theorem with those prerequisites. State that the proof develops/discharges this machinery instead of claiming a direct transcription of the displayed five equations.
2. **Weak closure and full metadata closure are distinct.** The manuscript’s principal downset contains only noncommuting visibility ancestors. `ConcreteMetadata` allows commuting predecessors needed to reconstruct identifiers and anchors; the raw Join theorem requires simultaneous semantic and metadata maximality. The final representation-Join contract uses causally closed sets. Exact OR-set has a checked weak-closure specialization; efficient/general certified ports must retain their stronger closure hypotheses.
3. **Scopes of commutation laws differ.** Guarded replay exactness requires distinct event timestamps and replica IDs (`GuardedReplay.Laws:22`). Scoped replay retains causal readiness and invariants. Malformed raw states cannot be admitted silently to a certified/invariant theorem, and causal-ready convergence cannot be promoted to arbitrary public-order extensions.
4. **Sequential lift is currently checked under a sufficient stronger global premise.** The updated `seq_spec.tex` theorem assumes conformance of every linear extension of each stored set. `PaperPresentation.uniform_versionsRA_of_paperOrder_witness` uses `FoldHistorySound` on every raw word, a stronger sufficient premise. The chosen-history alternative is checked separately. If claiming exact displayed-statement mechanization, add/check the straightforward local-premise lifting theorem or map the manuscript to the already checked stronger route explicitly.
5. **Independent specifications need an explicit alphabet projection and query premise.** Updated `ralin.tex` presents operation-label projection; full-event RGA and several certified languages retain event inputs. General `HistoryMachine` has existential acceptance; the abstraction/simulation route assumes a total deterministic specification, with init/update/query clauses. Retain these method assumptions rather than claiming determinism of every language.
6. **Recursive bases are covered in a precise certified store model.** `virtualMergeBaseState_canonical` handles recursive antichain construction under store invariants and contextual closed Join, and the certified reachability induction keeps original issuance evidence. This supports the draft’s recursive-base statement, but not unrestricted network-runtime correctness.
