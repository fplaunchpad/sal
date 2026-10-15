# Paper claims and Lean entry points

This map explains which checked statement supports each part of the paper.
Paths are relative to the standalone artefact root. The Lean files, including
their hypotheses, are authoritative. The [datatype map](datatypes.md) identifies
the 24 measured paper rows and their individual endpoints.

The central argument has two parts. Merge obligations establish exact concrete
state reconstruction and convergence. An independent sequential history then
explains the query answer. The five merge equations alone do not establish
sequential conformance. Different datatypes establish the required premises in
different domains; the body theorem is not a uniform theorem for all table rows.

## Reading order

All declaration names below start with `Sal.MRDTs.` unless written otherwise.
Import paths replace `/` by `.` and omit `.lean`.

| Paper concept | Source and declarations | Scope to retain |
|---|---|---|
| Implementation signature and event inputs | [Framework/Signature.lean](../Sal/MRDTs/Framework/Signature.lean): `MRDTSig`; [Base/UpdateSignature.lean](../Sal/MRDTs/Framework/Base/UpdateSignature.lean): `Foundation.Op`, `Foundation.UpdateSig` | A concrete update receives timestamp, replica and operation. Implementation-state equality is Lean equality. |
| Operational semantics | [Framework/Execution.lean](../Sal/MRDTs/Framework/Execution.lean): `Configuration`, `Label`, `Step`, `labeledTS`, `StepV`, `labeledTSV` | Finite labelled executions maintain a version store, parent graph, replica heads and visibility. `Step` uses an ordinary greatest common ancestor; `StepV` additionally accepts a virtual merge-base resolver. |
| Recursive merge bases | [Metatheory/VirtualMergeBase.lean](../Sal/MRDTs/Metatheory/VirtualMergeBase.lean): `canonicalVirtualMergeBase`; [Paper1/CertifiedClosedExecution.lean](../Sal/MRDTs/Paper1/CertifiedClosedExecution.lean): `Paper1.CertifiedClosedExecution.virtualMergeBaseState_canonical` | Recursive antichain construction yields the canonical intersection state under the store invariants and contextual `ClosedJoinAt` premise. This is a theorem about the model's resolver. |
| Per-event-set order | [Paper1/RestrictedReplay.lean](../Sal/MRDTs/Paper1/RestrictedReplay.lean): `Paper1.paperOrder`; [Paper1/GuardedOrder.lean](../Sal/MRDTs/Paper1/GuardedOrder.lean): `Paper1.GuardedReplay.paperOrder_acyclic`, `exists_paperOrder_enumeration` | The absorber is searched for within the event set being ordered. Finite enumeration uses strict, transitive visibility and the relevant laws. |
| Canonical concrete state | [Paper1/ConcreteFormalism.lean](../Sal/MRDTs/Paper1/ConcreteFormalism.lean): `Paper1.ConcreteMRDT.Representation`, `RepresentationJoin`, `Canonical`, `VersionsWitness` | `Canonical` means exact equality with an update fold over a permutation respecting `paperOrder`. Representation relates event sets to implementation states; it is separate from a simulation to specification states. |
| One state per event set | [Paper1/GuardedConvergence.lean](../Sal/MRDTs/Paper1/GuardedConvergence.lean): `Paper1.convergence_on_guarded`; [Paper1/ConcreteReplay.lean](../Sal/MRDTs/Paper1/ConcreteReplay.lean): `Paper1.ConcreteMRDT.replay_equal`, `canonical_unique`, `canonical_exists` | Guarded laws retain their timestamp and replica restrictions. Existence also needs finite supported event sets and the causal-context hypotheses in the declaration. Invariant-scoped variants are described below. |
| Five equations | [Paper1/ConcreteJoin.lean](../Sal/MRDTs/Paper1/ConcreteJoin.lean): `Paper1.ConcreteMRDT.Raw.MergeVCs` | The fields are `merge_comm`, `init`, `causal_delta`, `local_redistribute`, and `shared`. They quantify over represented states and a metadata dependency scheme. Smaller-union reconstruction facts remain explicit. |
| Five equations imply Join | Same file: `Paper1.ConcreteMRDT.Raw.join_at_sizes`, `representationJoin_of_vcs` | Strict finite-event induction additionally needs representation uniqueness, initial representation, finite enumerability and `ReplaySupply`. No global Join or merge-preservation theorem is supplied as an input. |
| Stored versions retain canonical states | [Paper1/CertifiedClosedExecution.lean](../Sal/MRDTs/Paper1/CertifiedClosedExecution.lean): `Paper1.CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV`, `canonicalConfig_of_execution`, `replayWitness_of_execution` | Requires contextual closed Join and original mint/issuance provenance. Covers ordinary and recursive-base certified executions. |
| Sequential language | [Paper1/HistorySpec.lean](../Sal/MRDTs/Paper1/HistorySpec.lean): `Paper1.HistorySpec`, `HistoryMachine.toSpec`, `DeterministicSpec` | A `HistorySpec` is a prefix-closed language. General machines need neither determinism nor totality. `DeterministicSpec` is an optional total deterministic presentation used by a sufficient simulation method. |
| Literal RA criterion | [Paper1/RALinearizability.lean](../Sal/MRDTs/Paper1/RALinearizability.lean): `Paper1.RALinearizable`, `VersionsRALinearizable`, `UniformVersionsRALinearizable` | The first predicate covers active replica heads and permits a history per query; the second covers every allocated version; the third uses one history for every query at that version. The manuscript's current stored-version formulation corresponds to the second. Certification restricts guarantees, not these configuration predicates. |
| Specification-visible criterion | [Paper1/ProjectedCriterion.lean](../Sal/MRDTs/Paper1/ProjectedCriterion.lean): `Paper1.ProjectedSpecificationRALinearizable`; [Paper1/EventBridge.lean](../Sal/MRDTs/Paper1/EventBridge.lean): `Paper1.EventVersionsSpecificationRA` | One permutation must explain the actual query and respect both implementation order and visibility between specification-conflicting updates. Full-event specifications retain timestamp/replica inputs. |
| Sequential lifting | [Paper1/PaperPresentation.lean](../Sal/MRDTs/Paper1/PaperPresentation.lean): `Paper1.PaperPresentation.uniform_versionsRA_of_paperOrder_witness`, `projected_versions_of_exact_total` | An exact stored-state witness plus global merge-free fold soundness yields an admitted history. The global premise is stronger than requiring soundness only for stored-set linear extensions in the manuscript. No additional replay law is needed just to reuse the exact witness. |
| Simulation to an independent specification | [Paper1/SequentialSimulation.lean](../Sal/MRDTs/Paper1/SequentialSimulation.lean): `Paper1.SequentialSimulation.fold_rel`, `sound`; [Paper1/EventBridge.lean](../Sal/MRDTs/Paper1/EventBridge.lean): `Paper1.EventSequentialSimulation.sound` | Initial, update and query clauses relate implementation and independent specification states. These routes prove all-word fold soundness; history-scoped routes instead choose an admitted history using execution evidence. |
| Specification commutation | [Paper1/CommutationBridge.lean](../Sal/MRDTs/Paper1/CommutationBridge.lean): `Paper1.CommutationCompatibility`, `projectedSpecVisibility_sub_paperOrder`, `specificationRA_of_fiveVCs_compatible` | Concrete commutation implies contextual specification commutation. The contrapositive covers specification-conflicting visibility. The event projection and state domain must match the endpoint used. |
| Packaged sufficient conditions | [Paper1/ConcreteVCExecution.lean](../Sal/MRDTs/Paper1/ConcreteVCExecution.lean): `Paper1.ConcreteMRDT.VCReplayConditions.join`, `VCConditions.executionsV`, `ScopedVCConditions.executionsV` | Packages retain representation, laws, five VCs, uniqueness, replay supply, represented versions, and sequential evidence. `VCConditions` uses total fold soundness and compatibility; `ScopedVCConditions` uses execution-history adequacy. |
| Reusable VC reductions | [Paper1/Automation/CommonVerification.lean](../Sal/MRDTs/Paper1/Automation/CommonVerification.lean): `Paper1.Automation.CommonVerification.verify`; [GenericCertifiedRecords.lean](../Sal/MRDTs/Paper1/Automation/GenericCertifiedRecords.lean): `Paper1.Automation.GenericCertifiedRecords.five_vcs` | Sound generic reductions return `Raw.MergeVCs` from the selected finite/evidence inputs. Datatype inputs and supporting lemmas still require proofs. There is no declaration named `expandedVCs`. |

`VCReplayConditions` receives `representedVersions` as a field. Its `.join`
derives Join, but `.executionsV` transports the supplied representation evidence;
that theorem's type alone does not show how each datatype obtained it. Inspect
the datatype proof and the dependency logs produced by
[the counting script](../measurements/measure.py) for actual consumption of
the five-VC induction. [The artifact entry point](../Sal/Artifact/Paper.lean)
checks the selected declarations and their axiom dependencies.

## Certified and invariant-scoped extensions

[Framework/Certificates.lean](../Sal/MRDTs/Framework/Certificates.lean) defines
`Issuance`, `MintCertifiedReach`, and `MintCertifiedReachV`.
Mint provenance records the state in which an operation was originally
generated. It does not require that operation to be generated again at each
reordered intermediate state.

The following interfaces are related but are not interchangeable:

| Extension | Checked entry points | Limits of transport |
|---|---|---|
| Event guards | [GuardedReplay.lean](../Sal/MRDTs/Paper1/GuardedReplay.lean): `Paper1.GuardedReplay.Laws` | Noncommutation exactness is guarded by distinct timestamps and different replicas. Conditional commutation still tests actual event instances. |
| Chosen certified history | [ConcreteHistoryBridge.lean](../Sal/MRDTs/Paper1/ConcreteHistoryBridge.lean): `Paper1.ConcreteMRDT.versions_of_scoped_history`, `ScopedCertificate.convergence`, `ScopedCertificate.executionsV` | History adequacy selects a suitable fold. Canonical uniqueness identifies its state with the separately represented stored state. |
| Representation-sensitive history | [CertifiedHistoryBridge.lean](../Sal/MRDTs/Paper1/CertifiedHistoryBridge.lean): `Paper1.CertifiedHistory.versions_of_representation`, `storedCanonical` | Uniqueness is needed only in certified contexts. This bridge does not prove the five VCs or supply global guarded laws. |
| Invariant commutation | [InvariantOrder.lean](../Sal/MRDTs/Paper1/InvariantOrder.lean): `Paper1.InvariantOrder.Commutes`, `Closed`, `VersionsRA`, `versions_universal` | The state predicate is explicit and must be justified independently. The same domain is used in causal and absorber clauses. `Closed` includes initial, update and merge closure; it is stronger than closure along legal causal prefixes. |
| Legal invariant replay | [InvariantReplay.lean](../Sal/MRDTs/Paper1/InvariantReplay.lean): `Paper1.InvariantReplay.convergence_on`, `Canonical`, `canonical_unique` | Both replay words must be legal, respect visibility, and respect the invariant order. This does not establish equality of arbitrary permutations respecting only that order. |
| Split self-commutation contract | [SplitPolicy.lean](../Sal/MRDTs/Paper1/SplitPolicy.lean): `Paper1.SplitPolicy.laws_iff_guarded`, `Certified.restricted_iff_existing`, `Invariant.restricted_iff_existing`; [SplitSoundness.lean](../Sal/MRDTs/Paper1/SplitSoundness.lean): `Paper1.SplitPolicy.Concrete.ScopedVCConditions.executionsV` | Separates distinct-operation policy exactness from equal-operation self-commutation. The equivalences keep the state/event domains fixed; they do not erase invariant or readiness premises. |

Metadata closure can retain commuting causal predecessors needed for identifiers,
anchors or other representation data. In
[ConcreteJoin.lean](../Sal/MRDTs/Paper1/ConcreteJoin.lean), `Raw.PeelChoice`
must be maximal for both semantic order and metadata dependencies, and represent
the remainder and operation's past. The general theorem should not be read as
requiring only noncommuting visibility closure. A specialised weaker closure
result for one implementation does not automatically transfer to another.

## Pointwise operation labels

The paper writes `ops` as a pointwise projection of each event's operation
field. Some independent specifications also need identities, timestamps or
other prepared arguments. [OperationLabels.lean](../Sal/MRDTs/Paper1/OperationLabels.lean)
checks how to put those arguments into the operation field when issued:

- `Paper1.OperationLabels.Operation` pairs the original application payload
  with specification inputs; `issue` attaches inputs determined from the
  original event and `issuance` checks their consistency.
- `erase_issue`, `issue_injective`, `fold_issue`, `visibility_issue`,
  `order_issue`, and `query_same` preserve identity, effects, visibility,
  implementation order and query answers under this encoding.
- `ops`, `ops_issue`, and `projectedUpdates_eq_ops` give the literal pointwise
  projection. `specificationRA`, `ra`, and `eventVersionsRA` transport the
  corresponding existing history result to enriched operations.

This is an explicit encoding and configuration/history transport. It does not
prove that arbitrary independently supplied arguments are valid, or identify
the unextended payload-only criterion with every full-event specification.

## Notion: theory and external reproduction

The checked fragment is the typed create/insert/erase/split document core with
explicit bootstrap, fresh identities, injective sessions and its original
initialisation/receipt/request protocol. It is not the complete public demo or
the production Notion editor.

[Instances/NotionCoreMRDT.lean](../Sal/MRDTs/Instances/NotionCoreMRDT.lean)
contains the reference archive carrier, `D`, `spec`, and `fiveVCs` in namespace
`Instances.NotionCoreMRDT`. The structural carrier stores immutable facts and
derives its document query without replaying all transactions:
[NotionCoreStructuralMRDT.lean](../Sal/MRDTs/Instances/NotionCoreStructuralMRDT.lean)
contains `Instances.NotionCoreStructuralMRDT.fiveVCs`, `renderer`,
`versions_witness`, `specification_ra`, `operational_reach`, and `registered_query`.
Their scope retains `NotionCoreProtocol.Reach` and injective sessions; query
agreement transfers the independent history theorem to the structural carrier.

The distinguished checked packages live in
[Metatheory/NotionCoreLedger.lean](../Sal/MRDTs/Metatheory/NotionCoreLedger.lean),
`Research.NotionCoreLedger.entry`, and
[NotionCoreStructuralRuntimeLedger.lean](../Sal/MRDTs/Metatheory/NotionCoreStructuralRuntimeLedger.lean),
`Research.NotionCoreStructuralRuntimeLedger.entry`.
They are protocol-scoped research entries outside the uniform `VerifiedMRDT`
production registry. The latter also packages typed executable receipt/merge
refinement and registered-query/load results. It retains archive and allocation
metadata, including information that structural query facts alone do not determine.

Building these Lean sources checks their theorems without cloning the public
demo. Comparison with pinned external JavaScript, any preserved bug traces, and
JSON conversion are separate executable experiments. They are not consequences
of the typed refinement theorems. Formatting and the editor's merge-block
request are outside the verified fragment; merge-block is distinct from merging
replicated versions. The Lean development does not prove the external
JavaScript, number/string representation, JSON decoder, compiler or runtime correct.

## Measurements and trust

[current-counts.json](../measurements/current-counts.json) records 24 paper rows
and 26 selected configurations. Its `paper_rows` entries retain all declaration
roots and source ranges. The grow-only-set row combines three carriers; the
sided Peritext row combines its rendered endpoint with its internal core proof
layer. These are measured selections, not a count of every implementation or
every theorem in the repository. Some files with GC in their names are retained as transitive build dependencies
for timestamp, metadata or purge helpers. They do not add garbage-collection
claims or evaluation to this artefact.

[metatheory-counts.json](../measurements/metatheory-counts.json) lists ten generic
roots and their transitive kernel dependencies. The selected generic metatheory
and framework/interface theorem declarations occupy 4,020 nonblank,
noncomment source lines; shared automation adds 1,688. These include statements
and proofs, exclude definitions, and do not measure handwritten tactic bodies
or human effort. The two files are recorded measurement snapshots and retain
their own provenance; their totals should not be read as a fresh whole-source count.

For those ten roots the recorded axiom closures contain only some subset of
`propext`, `Classical.choice`, and `Quot.sound`; the direct uniform lifting
root has none. This is an endpoint dependency audit, not a statement that every
control/example avoids native evaluation. The standalone artefact's own check
commands establish what was rebuilt from the supplied source.
