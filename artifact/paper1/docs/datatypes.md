# Measured datatypes and proof routes

The measurement selects **26 implementations, displayed as 24 paper rows**.
Three grow-only-set carriers form one row. Sided Peritext's internal core is
charged to its public rich-text implementation rather than counted separately.
The measured declarations are listed in
[current-counts.json](../measurements/current-counts.json).

This catalogue is a reading map. It does not replace the hypotheses in the
linked declarations. `P.` abbreviates `Sal.MRDTs.Paper1.` and `I.` abbreviates
`Sal.MRDTs.Instances.`. Every root used for the implementation, independent
specification, VC and execution measurements is recorded under the row's
`roots` field in the JSON. The links below point to source modules, not external
reference implementations.

| Paper row | Implementation declaration(s) | Independent specification | VC and execution entry points |
|---|---|---|---|
| Counter | `I.FlatCounters.Counter` | `P.SimpleEventPorts.deltaMachine` | [SimpleConcretePorts](../Sal/MRDTs/Paper1/SimpleConcretePorts.lean): `P.ConcreteMRDT.SimplePorts.counterConditions`, `counterExecutionsV` |
| Grow-only set, three carriers | `I.AddStore.D`, `I.FinsetStore.D`, `I.FlatGrowOnly.GOSet` | `P.SimpleEventPorts.setMachine`, `finiteMachine`, `booleanMachine` | [SimpleConcretePorts](../Sal/MRDTs/Paper1/SimpleConcretePorts.lean): `P.ConcreteMRDT.SimplePorts.gsetConditions`, `finiteAddConditions`, `booleanSetConditions`, and their `*ExecutionsV` endpoints |
| Flat grow-only map | `I.FlatGrowOnly.GOMap` | `P.SimpleEventPorts.booleanMachine` | [SimpleConcretePorts](../Sal/MRDTs/Paper1/SimpleConcretePorts.lean): `P.ConcreteMRDT.SimplePorts.booleanMapConditions`, `booleanMapExecutionsV` |
| Last-writer-wins register | `I.LWWRegister.D` | `P.LWW.GuardedPort.language` | [GuardedLWWPort](../Sal/MRDTs/Paper1/GuardedLWWPort.lean): `P.LWW.GuardedPort.certificate`, `history`, `executionsV` |
| Multi-value register | `I.MVRLive.D` | `P.CertifiedMVRHistory.language` | [CertifiedMVRVC](../Sal/MRDTs/Paper1/CertifiedMVRVC.lean): `P.CertifiedQueueMVR.MVR.RawVC.mergeVCs`; [CertifiedMVRCertificate](../Sal/MRDTs/Paper1/CertifiedMVRCertificate.lean): `P.CertifiedQueueMVR.MVR.Certificate.executionsV` |
| Optional register | `I.OptionalRegister.D` | `P.OptionalRegister.spec` | [OptionalRegisterVC](../Sal/MRDTs/Paper1/OptionalRegisterVC.lean): `P.OptionalRegister.fiveVC`; [OptionalRegisterCertificate](../Sal/MRDTs/Paper1/OptionalRegisterCertificate.lean): `P.OptionalRegister.executionsV`, `sourceWellFormed` |
| Enable-wins flag | `I.EnableWinsFlag.D` | `P.EnableWinsFlagEvent.spec` | [NeemFlagVC](../Sal/MRDTs/Paper1/EnableWinsFlagVC.lean): `P.NeemFlagVC.certifiedFiveVCFor`; [EnableWinsFlagCertificate](../Sal/MRDTs/Paper1/EnableWinsFlagCertificate.lean): `P.EnableWinsFlagEvent.certifiedV` |
| Disable-wins flag | `I.DisableWinsFlag.D` | `P.DisableWinsFlagEvent.spec` | [NeemFlagVC](../Sal/MRDTs/Paper1/EnableWinsFlagVC.lean): `P.NeemFlagVC.certifiedFiveVCFor`; [DisableWinsFlagCertificate](../Sal/MRDTs/Paper1/DisableWinsFlagCertificate.lean): `P.DisableWinsFlagEvent.certifiedV` |
| Ordinary OR-set, paper example | `P.ORSet.D` | `P.ORSet.EventSpec.spec` | [GuardedRawORSetJoin](../Sal/MRDTs/Paper1/GuardedRawORSetJoin.lean): `P.ORSet.GuardedRawVC.mergeVCs`; [GuardedRawExactExecution](../Sal/MRDTs/Paper1/GuardedRawExactExecution.lean): `P.ORSet.RawExecution.executionsV` |
| Efficient OR-set | `I.EfficientORSet.D` | `P.EfficientORSet.EventSpec.spec` | [GuardedRawORSetVC](../Sal/MRDTs/Paper1/GuardedRawORSetVC.lean): `P.EfficientORSet.GuardedRawVC.mergeVCs`; [GuardedRawEfficientCertificate](../Sal/MRDTs/Paper1/GuardedRawEfficientCertificate.lean): `P.EfficientORSet.RawCertificate.executionsV` |
| Remove-wins set | `I.RemoveWinsSet.D` | `P.RemoveWinsSet.spec` | [RemoveWinsSetVC](../Sal/MRDTs/Paper1/RemoveWinsSetVC.lean): `P.RemoveWinsSet.fiveVC`; [RemoveWinsSetCertificate](../Sal/MRDTs/Paper1/RemoveWinsSetCertificate.lean): `P.RemoveWinsSet.executionsV` |
| Set-wins multimap | `I.SetWinsMap.D` | `P.SetWinsMap.spec` | [SetWinsMapVC](../Sal/MRDTs/Paper1/SetWinsMapVC.lean): `P.SetWinsMap.fiveVC`; [SetWinsMapCertificate](../Sal/MRDTs/Paper1/SetWinsMapCertificate.lean): `P.SetWinsMap.executionsV` |
| Priority queue, same-record variant | `I.PriorityQueueSameRecord.D`, `rmvMax` | `P.PriorityQueueSameRecord.spec`, `seqRmvMax` | [PriorityQueueSameRecordVC](../Sal/MRDTs/Paper1/PriorityQueueSameRecordVC.lean): `P.PriorityQueueSameRecord.fiveVC`; [PriorityQueueSameRecordCertificate](../Sal/MRDTs/Paper1/PriorityQueueSameRecordCertificate.lean): `P.PriorityQueueSameRecord.executionsV` |
| Bounded counter with rights transfer | `I.BalegasBoundedCounter.D` | `P.BalegasBoundedCounterEvent.spec` | [BalegasBoundedCounterVC](../Sal/MRDTs/Paper1/BalegasBoundedCounterVC.lean): `P.BalegasBoundedCounterVC.fiveVC`; [BalegasBoundedCounterCertificate](../Sal/MRDTs/Paper1/BalegasBoundedCounterCertificate.lean): `P.BalegasBoundedCounterEvent.certifiedV` |
| Anchored FIFO queue, paper variant | `P.AnchoredQueue.publicQueue` | `P.AnchoredQueue.Public.language` | [AnchoredQueue](../Sal/MRDTs/Paper1/AnchoredQueue.lean): `P.AnchoredQueue.mergeVCs`; [AnchoredQueueCertificate](../Sal/MRDTs/Paper1/AnchoredQueueCertificate.lean): `P.AnchoredQueue.History.schedule_publicWitness`, `executionsV` |
| RGA | `I.RGA.RGAM` | `P.RGA.EventSpec.spec` | [RGAConcretePort](../Sal/MRDTs/Paper1/RGAConcretePort.lean): `P.RGA.ConcretePort.conditions`, `history`, `executionsV` |
| Embedded RGA | `I.EmbedRGA.E` | `I.ProductionRGA.embedClientSpec` | [CertifiedRGAVC](../Sal/MRDTs/Paper1/CertifiedRGAVC.lean): `P.CertifiedRGAVC.Embedded.mergeVCs`; [CertifiedRGAInvariantCertificate](../Sal/MRDTs/Paper1/CertifiedRGAInvariantCertificate.lean): `P.CertifiedRGAInvariantCertificate.executionsV` |
| Sided Embedded RGA | `I.SidedEmbedRGA.S` | `I.ProductionRGA.sidedClientSpec` | [CertifiedRGASidedVC](../Sal/MRDTs/Paper1/CertifiedRGASidedVC.lean): `P.CertifiedRGAVC.Sided.mergeVCs`; [CertifiedSidedInvariantCertificate](../Sal/MRDTs/Paper1/CertifiedSidedInvariantCertificate.lean): `P.CertifiedSidedInvariantCertificate.executionsV` |
| FugueMax, immutable birth records | `I.SidedEmbedRGA.FugueMax.datatype` | `P.FugueMaxNaturalCertificate.eventSpec` | [CertifiedFugueVC](../Sal/MRDTs/Paper1/CertifiedFugueVC.lean): `P.CertifiedFugueVC.mergeVCs`; [FugueMaxNaturalCertificate](../Sal/MRDTs/Paper1/FugueMaxNaturalCertificate.lean): `P.FugueMaxNaturalCertificate.executionsV` |
| Tree move, incremental carrier | `I.TreeMove.Incremental.D` | `I.TreeMove.Incremental.language` | [TreeMoveIncrementalMRDT](../Sal/MRDTs/Instances/TreeMoveIncrementalMRDT.lean): `I.TreeMove.Incremental.fiveVC`; [TreeMoveIncrementalCertificate](../Sal/MRDTs/Instances/TreeMoveIncrementalCertificate.lean): `I.TreeMove.Incremental.history`, `executionsV` |
| Embedded Peritext | `I.Peritext.D` | `P.CertifiedPeritextInvariantCertificate.language` | [CertifiedPeritextVC](../Sal/MRDTs/Paper1/CertifiedPeritextVC.lean): `P.CertifiedPeritextVC.mergeVCs`; [CertifiedPeritextInvariantCertificate](../Sal/MRDTs/Paper1/CertifiedPeritextInvariantCertificate.lean): `P.CertifiedPeritextInvariantCertificate.executionsV` |
| Sided Peritext, rich endpoint and internal core | `I.SidedPeritext.RichCore`, `Core` | `P.CertifiedRGARichCertificate.language`, `P.CertifiedRGACoreCertificate.language` | [CertifiedRGARichVC](../Sal/MRDTs/Paper1/CertifiedRGARichVC.lean): `P.CertifiedRGARichVC.mergeVCs`; [CertifiedRGARichCertificate](../Sal/MRDTs/Paper1/CertifiedRGARichCertificate.lean): `P.CertifiedRGARichCertificate.executionsV`; internal core uses `P.CertifiedRGACoreMergeVC.mergeVCs` and `P.CertifiedRGACoreCertificate.executionsV` |
| AegisSheet | `I.AegisSheet.D` | `P.AegisSheetEvent.spec` | [IssuedConcretePorts](../Sal/MRDTs/Paper1/IssuedConcretePorts.lean): `P.ConcreteMRDT.GuardedPorts.Sheet.conditions`, `history`, `executionsV` |
| Notion typed core | `I.NotionCoreMRDT.D`, `I.NotionCoreStructuralMRDT.D`, indexed typed runtime | `I.NotionCoreMRDT.spec` | [NotionCoreStructuralMRDT](../Sal/MRDTs/Instances/NotionCoreStructuralMRDT.lean): `I.NotionCoreStructuralMRDT.fiveVCs`, `versions_witness`, `operational_reach`; [NotionCoreStructuralRuntimeLedger](../Sal/MRDTs/Metatheory/NotionCoreStructuralRuntimeLedger.lean): `Sal.MRDTs.Research.NotionCoreStructuralRuntimeLedger.entry`; reference protocol with block merge: [NotionCoreProtocol](../Sal/MRDTs/Instances/NotionCoreProtocol.lean): `I.NotionCoreProtocol.versions_witness`, `specification_ra`; [NotionCoreMRDTClient](../Sal/MRDTs/Instances/NotionCoreMRDTClient.lean): `I.NotionCoreMRDTClient.merge_effect` |

`executionsV` denotes the named finite-trace theorem, not an assumption-free
guarantee. Where the table uses `certifiedV`, its conclusion covers the
canonical recursive-base certified reachability predicate; ordinary certified
reachability embeds into it. Consult the theorem's actual signature for the
issuer, parameter and protocol premises.

## Conditions that matter when reading the table

The simple counter/set/map ports use independent deterministic specifications
and local simulations. Both OR-set implementations have the ordinary-set
sequential behaviour. The efficient carrier changes the representation rather
than the specification. The set-wins map is a multimap: its query returns a set
of values at a key, rather than selecting a single register value.

The optional register and remove-wins set retain positive timestamp conditions
to distinguish updates from initial data. The register, queue and bounded
counter ports retain their own issuance evidence. In particular, the bounded
counter includes rights transfer and legality conditions; its theorem is not a
claim about arbitrary unguarded decrements. The priority-queue measurement uses
the same-record variant and includes derived maximum-removal evidence, not a
silent substitution of another priority-queue carrier.

The sequence and rich-text specifications retain the identities needed for
anchors and deletion targets. Several embedded sequence/rich-text ports use
explicit representation invariants and legal replay prefixes. Their convergence
statements must not be strengthened to all permutations respecting only an
invariant-derived public order. Plain RGA and tree move can have unrestricted
update/merge algebra yet still need issuance evidence to obtain an admitted
independent history. FugueMax's measured endpoint uses its natural sequence
language and immutable birth records.

Notion has a separate protocol-scoped research package. Its reference carrier,
structural renderer and typed indexed implementation share an independent
document specification and original honest protocol. The reference carrier's
theorems cover create, insert, erase, split and a corrected block merge whose
removal of the source is the move itself. The structural and executable
carriers cover merge-free networks (`I.NotionCoreMergeFree.MergeFree`), since
the facts they retain record no merge
(`I.NotionCoreStructuralRender.SPOT.merge_outside_scope`). They are included in one
measurement row without promoting that row to the uniform production registry.
The [claim map](claims-and-theorems.md#notion-theory-and-external-reproduction)
states the verified fragment and the boundary of external demo comparisons.

These examples exercise a family of sufficient conditions: raw/guarded laws,
certified histories, representation invariants and protocol-specific transport.
A table entry is not evidence that the manuscript's unextended body theorem
applies verbatim to that datatype. Each named endpoint retains the additional
premises used by its proof.

## Reading the size columns

[table.md](../measurements/table.md) gives the recorded sizes. Definition,
specification, VC support and bridge/execution support columns count dependency
footprints using Lean declaration source ranges. Complete declarations include
their statements and proofs. Shared libraries are excluded from per-row values;
overlap across different rows is not subtracted. The Notion row includes its
reference/protocol proof, structural implementation and typed executable
refinement. These are not measurements of handwritten proof bodies or elapsed
proof-development effort.
