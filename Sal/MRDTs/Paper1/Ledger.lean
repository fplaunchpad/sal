import Sal.MRDTs.Paper1.PaperPresentation
import Sal.MRDTs.Paper1.AnchoredQueueCertificate
import Sal.MRDTs.Paper1.AnchoredQueuePublicControls
import Sal.MRDTs.Paper1.AnchoredQueueHistoryControls
import Sal.MRDTs.Paper1.CertifiedSidedInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedSidedInvariantControls
import Sal.MRDTs.Paper1.CertifiedPeritextInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedPeritextInvariantControls
import Sal.MRDTs.Paper1.CertifiedFugueInvariantObstruction
import Sal.MRDTs.Paper1.CertifiedRGAInvariantCertificate
import Sal.MRDTs.Paper1.CertifiedRGAInvariantControls
import Sal.MRDTs.Paper1.CertifiedRGAOrderComparison
import Sal.MRDTs.Paper1.CertifiedFugueRawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedSidedRawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedPeritextRawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedRGACoreCertificate
import Sal.MRDTs.Paper1.CertifiedRGARichCertificate
import Sal.MRDTs.Paper1.CertifiedFugueVCExecution
import Sal.MRDTs.Paper1.CertifiedRGACoreExecution
import Sal.MRDTs.Paper1.CertifiedRGARawOrderObstruction
import Sal.MRDTs.Paper1.CertifiedRGACertificate
import Sal.MRDTs.Paper1.CertifiedRGAHistoryCommutation
import Sal.MRDTs.Paper1.CertifiedRGACoreMergeVC
import Sal.MRDTs.Paper1.CertifiedRGARichVC
import Sal.MRDTs.Paper1.CertifiedCoverage
import Sal.MRDTs.Paper1.CertifiedScopeRestriction
import Sal.MRDTs.Paper1.CertifiedMVRCertificate
import Sal.MRDTs.Paper1.CertifiedMVRControls
import Sal.MRDTs.Paper1.CertifiedRGAIssuance
import Sal.MRDTs.Paper1.CertifiedQueueMVRQueue
import Sal.MRDTs.Paper1.CertifiedReplay
import Sal.MRDTs.Paper1.CertifiedHistoryBridge
import Sal.MRDTs.Paper1.CertifiedMVRHistory
import Sal.MRDTs.Paper1.CertifiedMVRReplay
import Sal.MRDTs.Paper1.CertifiedRGAReplay
import Sal.MRDTs.Paper1.CertifiedRGAScope

import Sal.MRDTs.Paper1.Soundness
import Sal.MRDTs.Paper1.Capstone
import Sal.MRDTs.Paper1.ORSetSPOT
import Sal.MRDTs.Paper1.ORSetSpecification
import Sal.MRDTs.Paper1.ORSetExecution
import Sal.MRDTs.Paper1.CriterionCounterexample
import Sal.MRDTs.Paper1.RGAActive
import Sal.MRDTs.Paper1.RGAStrict
import Sal.MRDTs.Paper1.RGAConflict
import Sal.MRDTs.Paper1.RGAComparison
import Sal.MRDTs.Paper1.RGAEventSpec
import Sal.MRDTs.Paper1.CommutationBridge
import Sal.MRDTs.Paper1.MigrationCoverage
import Sal.MRDTs.Paper1.ORSetBridgeControls
import Sal.MRDTs.Paper1.QueryORSet
import Sal.MRDTs.Paper1.QueryExactORSet
import Sal.MRDTs.Paper1.AbstractControls
import Sal.MRDTs.Paper1.NeemScope
import Sal.MRDTs.Paper1.MetadataORSet
import Sal.MRDTs.Paper1.MetadataPeelControl
import Sal.MRDTs.Paper1.MetadataRewrite
import Sal.MRDTs.Paper1.EfficientMetadataCausal
import Sal.MRDTs.Paper1.MetadataDecomposition
import Sal.MRDTs.Paper1.ORSetRedistribution
import Sal.MRDTs.Paper1.ORSetVCJoin
import Sal.MRDTs.Paper1.EfficientORSetVCJoin
import Sal.MRDTs.Paper1.EfficientVCExecution
import Sal.MRDTs.Paper1.AbstractCoverage
import Sal.MRDTs.Paper1.GuardedOrder
import Sal.MRDTs.Paper1.GuardedAbstraction
import Sal.MRDTs.Paper1.GuardedPolicyControls
import Sal.MRDTs.Paper1.GuardedRawExactExecution
import Sal.MRDTs.Paper1.GuardedRawEfficientCertificate
import Sal.MRDTs.Paper1.GuardedCoverage
import Mathlib.Util.AssertNoSorry

/-!
# Paper1 theorem and trust ledger

The active manuscript criterion and the stronger specification-visible candidate remain
distinct. Both operation-only RGA languages have full honestly certified
counterexamples from the initial store, excluding all witness orders and
allocation choices. Explicit insertion-ID labels give general positive
guarantees for the same concrete datatype and issuer. These names are the
stable evidence boundary for the canonical task list's research results.
The agreed full-input RGA language retains timestamp, replica, and operation;
its literal and stronger guarantees are recorded under `RGA.EventSpec`.
-/

namespace Sal.MRDTs.Paper1

#check HistorySpec
#check HistoryMachine.toSpec
#check OperationPolicy
#check RestrictedLaws
#check paperOrder
#check RALinearizable
#check RAExecution
#check RAImplementation
#check UniformVersionsRALinearizable
#check CertifiedRA
#check CertifiedRAV
#check PaperMergeVCs
#check SequentialSimulation
#check IssuedHistoryAdequacy
#check SpecificationRALinearizable
#check QueryReplay.Equivalent
#check QueryReplay.Abstraction
#check QueryReplay.Laws
#check QueryReplay.VersionsRALinearizable
#check AbstractMRDT.Model
#check AbstractMRDT.MergeVCs
#check AbstractMRDT.Certificate
#check AbstractMRDT.VCConditions

-- Audit all load-bearing bridges and the positive/negative research results.
-- Only Lean's standard classical/extensional axioms are permitted.
open Lean Elab Command in
elab "assert_paper_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "{n} depends on unexpected axiom {axiomName}"

assert_paper_axioms HistoryMachine.toSpec
assert_paper_axioms convergence_on_guarded
assert_paper_axioms GuardedReplay.paperOrder_acyclic
assert_paper_axioms GuardedReplay.exists_paperOrder_enumeration
assert_paper_axioms AbstractMRDT.Guarded.Laws.toReplay
assert_paper_axioms AbstractMRDT.Guarded.canonical_equivalent
assert_paper_axioms AbstractMRDT.Guarded.canonical_query_unique
assert_paper_axioms AbstractMRDT.Guarded.canonical_exists
assert_paper_axioms EfficientORSet.GuardedPolicyControls.guarded_exactness_control
assert_paper_axioms EfficientORSet.GuardedPolicyControls.tag_control
assert_paper_axioms EfficientORSet.GuardedPolicyControls.paperOrder_control

-- Guarded convergence must not silently reuse the uniform-order transport.
open Lean Elab Command in
elab "assert_guarded_dependencies " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  let forbidden := [``RestrictedLaws.replayLaws, ``paperOrder_iff_loOn,
    ``AbstractMRDT.Laws.toRestricted, ``AbstractMRDT.canonical_query_unique]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if forbidden.contains current then
        throwError "{n} uses uniform-law transport {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending
  unless seen.contains ``convergence_on_guarded do
    throwError "{n} does not use direct guarded convergence"

assert_guarded_dependencies AbstractMRDT.Guarded.canonical_equivalent
assert_guarded_dependencies AbstractMRDT.Guarded.canonical_query_unique

assert_paper_axioms ORSet.Guarded.laws
assert_paper_axioms EfficientORSet.Guarded.laws
assert_paper_axioms AbstractMRDT.Raw.join_at_sizes
assert_paper_axioms ORSet.GuardedRawVC.mergeVCs
assert_paper_axioms EfficientORSet.GuardedRawVC.mergeVCs
assert_paper_axioms ORSet.RawExecution.certificate
assert_paper_axioms EfficientORSet.RawCertificate.certificate
assert_paper_axioms ORSet.RawExecution.executions
assert_paper_axioms ORSet.RawExecution.executionsV
assert_paper_axioms EfficientORSet.RawCertificate.executions
assert_paper_axioms EfficientORSet.RawCertificate.executionsV
assert_paper_axioms ORSet.RawExecution.convergence
assert_paper_axioms EfficientORSet.RawCertificate.convergence
assert_paper_axioms ORSet.RawExecution.storedCanonical
assert_paper_axioms EfficientORSet.RawCertificate.storedCanonical

-- Final raw certificates must reach the new equality induction and actual
-- datatype equations, without relying on any previous merge correctness route.
open Lean Elab Command in
elab "assert_raw_vc_dependencies " n:ident " using " vc:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let obligation ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo vc
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  let forbidden := [``ORSet.join, ``ORSet.AbstractSpec.representationJoin,
    ``ORSet.AbstractSpec.vcRepresentationJoin, ``ORSet.AbstractSpec.vcJoinAt,
    ``ORSet.AbstractSpec.vcRepresentedVersions,
    ``AbstractMRDT.join_at_sizes, ``AbstractMRDT.representationJoin_of_vcs,
    ``Sal.MRDTs.Instances.EfficientORSet.represents_merge,
    ``Sal.MRDTs.Instances.EfficientORSet.represented_of_mintCertifiedV,
    ``Sal.MRDTs.Instances.EfficientORSet.virtualMergeBaseState_represents,
    ``EfficientORSet.AbstractSpec.representationJoin,
    ``EfficientORSet.AbstractSpec.vcRepresentationJoin,
    ``EfficientORSet.AbstractSpec.vcRepresentedConfig,
    ``EfficientORSet.AbstractSpec.vcRepresentedVersions,
    ``EfficientORSet.AbstractSpec.vcVirtualMergeBaseStateRepresents]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if forbidden.contains current then
        throwError "{n} uses earlier merge correctness route {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending
  for required in [``AbstractMRDT.Raw.join_at_sizes, obligation] do
    unless seen.contains required do
      throwError "{n} omits raw VC dependency {required}"

assert_raw_vc_dependencies ORSet.RawExecution.executions using ORSet.GuardedRawVC.mergeVCs
assert_raw_vc_dependencies ORSet.RawExecution.executionsV using ORSet.GuardedRawVC.mergeVCs
assert_raw_vc_dependencies EfficientORSet.RawCertificate.executions using EfficientORSet.GuardedRawVC.mergeVCs
assert_raw_vc_dependencies EfficientORSet.RawCertificate.executionsV using EfficientORSet.GuardedRawVC.mergeVCs
assert_paper_axioms DeterministicSpec.updates_query_iff
assert_paper_axioms RestrictedLaws.replayLaws
assert_paper_axioms QueryReplay.Abstraction.equivalent_iff
assert_paper_axioms AbstractMRDT.equivalent_iff_future
assert_paper_axioms AbstractMRDT.causalPast_subset
assert_paper_axioms AbstractMRDT.metadataSubstitution_of_unique
assert_paper_axioms AbstractMRDT.join_empty_left
assert_paper_axioms AbstractMRDT.MetadataDependencies.observable_past_subset
assert_paper_axioms AbstractMRDT.MetadataDependencies.closed_diff_of_max
assert_paper_axioms AbstractMRDT.joint_maximal_of_enumeration
assert_paper_axioms ORSet.AbstractSpec.joint_maximal
assert_paper_axioms EfficientORSet.AbstractSpec.joint_maximal
assert_paper_axioms AbstractMRDT.canonical_snoc
assert_paper_axioms AbstractMRDT.MetadataDependencies.past_closed
assert_paper_axioms AbstractMRDT.MetadataDependencies.past_semantic_maximal
assert_paper_axioms ORSet.AbstractSpec.peel_choice
assert_paper_axioms AbstractMRDT.causal_reconstruction
assert_paper_axioms EfficientORSet.AbstractSpec.kills_noncomm
assert_paper_axioms EfficientORSet.AbstractSpec.represents_snoc_maximal
assert_paper_axioms EfficientORSet.AbstractSpec.representation_exists
assert_paper_axioms EfficientORSet.AbstractSpec.peel_choice
assert_paper_axioms EfficientORSet.AbstractSpec.merge_update_eq
assert_paper_axioms EfficientORSet.AbstractSpec.causal_replay_eq
assert_paper_axioms EfficientORSet.AbstractSpec.causalMetadata
assert_paper_axioms AbstractMRDT.causal_frame
assert_paper_axioms AbstractMRDT.local_step
assert_paper_axioms AbstractMRDT.shared_step
assert_paper_axioms AbstractMRDT.swap_step
assert_paper_axioms AbstractMRDT.side_decomposition
assert_paper_axioms ORSet.AbstractSpec.mergeCommMetadata
assert_paper_axioms EfficientORSet.AbstractSpec.mergeCommMetadata
assert_paper_axioms AbstractMRDT.join_at_sizes
assert_paper_axioms AbstractMRDT.representationJoin_of_vcs
assert_paper_axioms ORSet.AbstractSpec.replaySupply
assert_paper_axioms EfficientORSet.AbstractSpec.replaySupply
assert_paper_axioms ORSet.AbstractSpec.shared_replay_eq
assert_paper_axioms ORSet.AbstractSpec.sharedMetadata
assert_paper_axioms EfficientORSet.AbstractSpec.shared_replay_eq
assert_paper_axioms EfficientORSet.AbstractSpec.sharedMetadata
assert_paper_axioms ORSet.AbstractSpec.local_replay_eq
assert_paper_axioms ORSet.AbstractSpec.localMetadata
assert_paper_axioms EfficientORSet.AbstractSpec.local_replay_eq
assert_paper_axioms EfficientORSet.AbstractSpec.localMetadata
assert_paper_axioms ORSet.AbstractSpec.causal_replay_eq
assert_paper_axioms ORSet.AbstractSpec.causalMetadata
assert_paper_axioms ORSet.AbstractSpec.mergeVCs
assert_paper_axioms ORSet.AbstractSpec.vcRepresentationJoin
assert_paper_axioms ORSet.AbstractSpec.vcJoinAt
assert_paper_axioms ORSet.AbstractSpec.vcRepresentedVersions
assert_paper_axioms ORSet.AbstractSpec.vcCertificate
assert_paper_axioms ORSet.AbstractSpec.vcCertifiedVersionsRAV
assert_paper_axioms ORSet.AbstractSpec.vcCertifiedExecutionsV
assert_paper_axioms ORSet.AbstractSpec.vcCertifiedExecutions
assert_paper_axioms EfficientORSet.AbstractSpec.causal_add_observation
assert_paper_axioms EfficientORSet.AbstractSpec.local_add_observation
assert_paper_axioms EfficientORSet.AbstractSpec.remove_past_subset
assert_paper_axioms EfficientORSet.AbstractSpec.local_remove_eq
assert_paper_axioms EfficientORSet.AbstractSpec.causal_remove_eq
assert_paper_axioms EfficientORSet.AbstractSpec.mergeVCs
assert_paper_axioms EfficientORSet.AbstractSpec.vcRepresentationJoin
assert_paper_axioms EfficientORSet.AbstractSpec.vcHistoryMerge
assert_paper_axioms EfficientORSet.AbstractSpec.vcVirtualMergeBaseStateRepresents
assert_paper_axioms EfficientORSet.AbstractSpec.vcRepresentedConfig
assert_paper_axioms EfficientORSet.AbstractSpec.vcRepresentedVersions
assert_paper_axioms EfficientORSet.AbstractSpec.vcCertificate
assert_paper_axioms EfficientORSet.AbstractSpec.vcCertifiedVersionsRAV
assert_paper_axioms EfficientORSet.AbstractSpec.vcCertifiedExecutionsV
assert_paper_axioms EfficientORSet.AbstractSpec.vcCertifiedExecutions
assert_paper_axioms AbstractMRDT.VCConditions.toCertificate
assert_paper_axioms AbstractMRDT.VCConditions.executions
assert_paper_axioms AbstractMRDT.VCConditions.executionsV
assert_paper_axioms ORSet.AbstractSpec.vcConditions
assert_paper_axioms EfficientORSet.AbstractSpec.vcConditions

-- Check the proof route, not merely its axioms: the new execution proofs
-- must reach the metadata induction and avoid the earlier direct Join proofs.
open Lean Elab Command in
elab "assert_vc_dependencies " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  let forbidden := [``ORSet.join, ``ORSet.AbstractSpec.representationJoin,
    ``ORSet.AbstractSpec.representedVersions,
    ``Sal.MRDTs.Instances.EfficientORSet.represents_merge,
    ``Sal.MRDTs.Instances.EfficientORSet.represented_of_mintCertifiedV,
    ``Sal.MRDTs.Instances.EfficientORSet.virtualMergeBaseState_represents,
    ``EfficientORSet.AbstractSpec.representationJoin,
    ``EfficientORSet.AbstractSpec.representedVersions]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if forbidden.contains current then
        throwError "{n} uses earlier direct Join route {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending
  unless seen.contains ``AbstractMRDT.join_at_sizes do
    throwError "{n} does not depend on the new metadata Join induction"
  for leaf in ["mergeVCs", "causalMetadata", "localMetadata", "sharedMetadata"] do
    let required := Name.str root.getPrefix leaf
    unless seen.contains required do
      throwError "{n} does not depend on datatype obligation {required}"

assert_vc_dependencies ORSet.AbstractSpec.vcRepresentationJoin
assert_vc_dependencies EfficientORSet.AbstractSpec.vcRepresentationJoin
assert_vc_dependencies ORSet.AbstractSpec.vcCertifiedExecutions
assert_vc_dependencies ORSet.AbstractSpec.vcCertifiedExecutionsV
assert_vc_dependencies EfficientORSet.AbstractSpec.vcCertifiedExecutions
assert_vc_dependencies EfficientORSet.AbstractSpec.vcCertifiedExecutionsV

-- Commuting ports reuse concrete equations, but their execution proofs must
-- still derive Join through the primary abstraction/metadata VC induction.
open Lean Elab Command in
elab "assert_commuting_vc_dependencies " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  let forbidden := [``Sal.MRDTs.Instances.AddStore.join,
    ``Sal.MRDTs.Instances.LWWRegister.join,
    ``Sal.MRDTs.Instances.LWWRegister.sequentialCorrectness,
    ``Sal.MRDTs.Instances.FinsetStore.join, ``Sal.MRDTs.Instances.FlatCounters.join,
    ``Sal.MRDTs.Instances.FlatGrowOnly.join, ``Sal.MRDTs.Instances.RGA.join,
    ``Sal.MRDTs.Instances.RGA.versionWellFormed_of_execution,
    ``Sal.MRDTs.Instances.RGA.canonical_respects_rc,
    ``RGA.Identified.canonical_respects_specVisibility,
    ``Sal.MRDTs.Instances.BoundedCounter.sequentialCorrectness,
    ``Sal.MRDTs.Instances.TreeMove.join, ``Sal.MRDTs.Instances.TreeMove.sequentialCorrectness,
    ``Sal.MRDTs.Instances.AegisSheet.join,
    ``Sal.MRDTs.Instances.AegisSheet.Sequential.canonical_causalOriginLegal,
    ``Sal.MRDTs.Instances.AegisSheet.Sequential.sequentialCorrectness]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if forbidden.contains current || current.toString.endsWith ".BoundedCounter.bcJoin" then
        throwError "{n} uses earlier concrete proof route {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending
  for required in [``AbstractMRDT.join_at_sizes, ``AbstractMRDT.CommutingPort.mergeVCs,
      ``AbstractMRDT.CommutingPort.causalMetadata, ``AbstractMRDT.CommutingPort.localMetadata,
      ``AbstractMRDT.CommutingPort.sharedMetadata] do
    unless seen.contains required do
      throwError "{n} lacks required abstraction VC obligation {required}"

assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.gsetExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.gsetExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.addStoreExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.addStoreExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.finiteAddExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.finiteAddExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.counterExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.counterExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.iocExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.iocExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.pnExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.pnExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.booleanSetExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.booleanSetExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.booleanMapExecutions
assert_commuting_vc_dependencies AbstractMRDT.SimplePorts.booleanMapExecutionsV
assert_commuting_vc_dependencies RGA.AbstractPort.executions
assert_commuting_vc_dependencies RGA.AbstractPort.executionsV
assert_commuting_vc_dependencies AbstractMRDT.GuardedPorts.Bounded.executions
assert_commuting_vc_dependencies AbstractMRDT.GuardedPorts.Bounded.executionsV
assert_commuting_vc_dependencies AbstractMRDT.GuardedPorts.Tree.executions
assert_commuting_vc_dependencies AbstractMRDT.GuardedPorts.Tree.executionsV
assert_commuting_vc_dependencies AbstractMRDT.GuardedPorts.Sheet.executions
assert_commuting_vc_dependencies AbstractMRDT.GuardedPorts.Sheet.executionsV

assert_paper_axioms AbstractMRDT.future_complete
assert_paper_axioms AbstractMRDT.VCReplayConditions.join
assert_paper_axioms AbstractMRDT.ScopedVCConditions.versionsV
assert_paper_axioms AbstractMRDT.ScopedVCConditions.executions
assert_paper_axioms AbstractMRDT.ScopedVCConditions.executionsV
assert_paper_axioms RGA.AbstractPort.conditions
assert_paper_axioms RGA.AbstractPort.executions
assert_paper_axioms RGA.AbstractPort.executionsV
assert_paper_axioms RGA.AbstractPort.globalCompatibility_impossible
assert_paper_axioms RGA.AbstractPort.crossed_control
assert_paper_axioms AbstractMRDT.SimplePorts.gsetConditions
assert_paper_axioms AbstractMRDT.SimplePorts.addStoreConditions
assert_paper_axioms AbstractMRDT.SimplePorts.finiteAddConditions
assert_paper_axioms AbstractMRDT.SimplePorts.counterConditions
assert_paper_axioms AbstractMRDT.SimplePorts.iocConditions
assert_paper_axioms AbstractMRDT.SimplePorts.pnConditions
assert_paper_axioms AbstractMRDT.SimplePorts.booleanSetConditions
assert_paper_axioms AbstractMRDT.SimplePorts.booleanMapConditions
assert_paper_axioms AbstractMRDT.GuardedPorts.Bounded.conditions
assert_paper_axioms AbstractMRDT.GuardedPorts.Tree.conditions
assert_paper_axioms AbstractMRDT.GuardedPorts.Sheet.conditions
assert_paper_axioms ObservationalObstructions.Queue.no_laws
assert_paper_axioms ObservationalObstructions.MVR.no_laws
assert_paper_axioms ObservationalObstructions.Embedded.no_laws
assert_paper_axioms ObservationalObstructions.Sided.no_laws
assert_paper_axioms ObservationalObstructions.peritext_no_laws
assert_paper_axioms ObservationalObstructions.SidedPeritext.core_no_laws
assert_paper_axioms ObservationalObstructions.SidedPeritext.rich_no_laws
assert_paper_axioms ObservationalObstructions.RegisteredFugueMax.no_laws
assert_paper_axioms ObservationalObstructions.Queue.query_control
assert_paper_axioms ObservationalObstructions.MVR.query_control
assert_paper_axioms ObservationalObstructions.Embedded.query_control
assert_paper_axioms ObservationalObstructions.Sided.query_control
assert_paper_axioms ObservationalObstructions.peritext_query_control
assert_paper_axioms ObservationalObstructions.SidedPeritext.core_query_control
assert_paper_axioms ObservationalObstructions.SidedPeritext.rich_query_control
assert_paper_axioms ObservationalObstructions.RegisteredFugueMax.query_control
assert_paper_axioms AbstractMRDT.SimplePorts.add_control
assert_paper_axioms AbstractMRDT.SimplePorts.finite_add_control
assert_paper_axioms AbstractMRDT.SimplePorts.increment_control
assert_paper_axioms AbstractMRDT.SimplePorts.pn_control
assert_paper_axioms AbstractMRDT.SimplePorts.boolean_control
assert_paper_axioms AbstractMRDT.SimplePorts.immutable_map_control
assert_paper_axioms AbstractCoverage.packages_eq_production
assert_paper_axioms AbstractCoverage.counts
assert_paper_axioms AbstractCoverage.ProvedResult.executions
assert_paper_axioms AbstractCoverage.ProvedResult.executionsV
assert_paper_axioms ORSet.AbstractSpec.metadataSubstitution
assert_paper_axioms EfficientORSet.AbstractSpec.metadataSubstitution
assert_paper_axioms ORSet.AbstractSpec.initialMetadata
assert_paper_axioms ORSet.AbstractSpec.initMetadata
assert_paper_axioms EfficientORSet.AbstractSpec.initialMetadata
assert_paper_axioms EfficientORSet.AbstractSpec.initMetadata
assert_paper_axioms EfficientORSet.MetadataPeelControl.control
assert_paper_axioms EfficientORSet.MetadataPeelControl.observable_dependency_missing
assert_paper_axioms EfficientORSet.MetadataPeelControl.observable_past_empty
assert_paper_axioms EfficientORSet.MetadataPeelControl.metadata_past_retains_older
assert_paper_axioms EfficientORSet.MetadataPeelControl.causal_reconstruction_invalid
assert_paper_axioms EfficientORSet.MetadataPeelControl.causal_reconstruction_observable
assert_paper_axioms AbstractMRDT.Laws.toRestricted
assert_paper_axioms AbstractMRDT.canonical_equivalent
assert_paper_axioms AbstractMRDT.canonical_iff
assert_paper_axioms AbstractMRDT.Model.historySound
assert_paper_axioms AbstractMRDT.of_representation
assert_paper_axioms AbstractMRDT.merge_canonical_of_representation
assert_paper_axioms AbstractMRDT.merge_equivalent_of_representation
assert_paper_axioms AbstractMRDT.Certificate.versionsV
assert_paper_axioms AbstractMRDT.Certificate.convergence
assert_paper_axioms AbstractMRDT.Certificate.executions
assert_paper_axioms AbstractMRDT.Certificate.executionsV
assert_paper_axioms ORSet.AbstractSpec.certificate
assert_paper_axioms EfficientORSet.AbstractSpec.certificate
assert_paper_axioms EfficientORSet.AbstractControls.merge_control
assert_paper_axioms EfficientORSet.AbstractControls.canonical_only_join_fails
assert_paper_axioms EfficientORSet.NeemScope.guarded_vs_unqualified
assert_paper_axioms QueryReplay.commutes_iff
assert_paper_axioms QueryReplay.Laws.toRestricted
assert_paper_axioms QueryReplay.canonical_query_unique
assert_paper_axioms QueryReplay.of_canonical
assert_paper_axioms ORSet.QuerySpec.certifiedVersionsRA
assert_paper_axioms ORSet.QuerySpec.certifiedVersionsRAV
assert_paper_axioms EfficientORSet.QuerySpec.laws
assert_paper_axioms EfficientORSet.QuerySpec.certifiedVersionsRA
assert_paper_axioms EfficientORSet.QuerySpec.certifiedVersionsRAV
assert_paper_axioms EfficientORSet.QuerySpec.same_replica_add_control
assert_paper_axioms EfficientORSet.QuerySpec.ordering_control
assert_paper_axioms EfficientORSet.QuerySpec.merge_congruence_fails
assert_paper_axioms paperOrder_iff_loOn
assert_paper_axioms SequentialSimulation.sound
assert_paper_axioms ra_of_replay_total
assert_paper_axioms uniform_ra_of_replay_total
assert_paper_axioms ra_of_canonical_history
assert_paper_axioms certifiedRA_of_fiveVCs
assert_paper_axioms certifiedRA_of_fiveVCs_issued
assert_paper_axioms certified_convergence_of_join
assert_paper_axioms CertifiedRA.executions
assert_paper_axioms CertifiedRAV.executions
assert_paper_axioms rawRA_of_join_total
assert_paper_axioms specificationRA_of_canonical_total
assert_paper_axioms specificationCertifiedRA_of_join_issued
assert_paper_axioms ORSet.join
assert_paper_axioms ORSet.certifiedRA
assert_paper_axioms ORSet.certifiedRAV
assert_paper_axioms ORSet.specificationCertifiedRA
assert_paper_axioms ORSet.specificationCertifiedRAV
assert_paper_axioms ORSet.rawRA
assert_paper_axioms ORSet.rawUniformRA
assert_paper_axioms ORSet.rawSpecificationRA
assert_paper_axioms ORSet.SPOT.defeater_union
assert_paper_axioms ORSet.Execution.defeater_execution
assert_paper_axioms ORSet.Execution.defeater_ra_execution
assert_paper_axioms ORSet.Execution.defeater_final_ra
assert_paper_axioms ORSet.Execution.figure_states
assert_paper_axioms ORSet.Execution.figure_observations
assert_paper_axioms CriterionCounterexample.bad_execution
assert_paper_axioms CriterionCounterexample.bad_mintCertified
assert_paper_axioms CriterionCounterexample.bad_ra_execution
assert_paper_axioms CriterionCounterexample.criteria_differ_on_reachable_mutation
assert_paper_axioms CriterionCounterexample.mutant_join
assert_paper_axioms CriterionCounterexample.mutant_rawRA
assert_paper_axioms CriterionCounterexample.raw_replay_witness
assert_paper_axioms CriterionCounterexample.raw_store_convergence
assert_paper_axioms CriterionCounterexample.raw_cross_store_convergence
assert_paper_axioms CriterionCounterexample.canonical_reachableV
assert_paper_axioms CriterionCounterexample.virtual_store_convergence
assert_paper_axioms RGA.certifiedRA
assert_paper_axioms RGA.certifiedRAV
assert_paper_axioms RGA.old_list_run_does_not_factor
assert_paper_axioms RGA.Strict.crossed_orders_stuck
assert_paper_axioms RGA.Strict.crossed_no_continuation
assert_paper_axioms RGA.Strict.Trace.local_issuance
assert_paper_axioms RGA.Strict.Trace.merged_effects
assert_paper_axioms RGA.root_insert_remove_not_commute
assert_paper_axioms RGA.anchor_two_insert_remove_one_not_commute
assert_paper_axioms RGA.anchor_one_insert_remove_two_not_commute
assert_paper_axioms RGA.specification_conflicts_not_covered
assert_paper_axioms projected_original_iff
assert_paper_axioms projected_certified_executions
assert_paper_axioms projected_certified_executionsV
assert_paper_axioms RGA.Strict.Investigation.crossed_no_history
assert_paper_axioms RGA.Strict.Investigation.crossed_not_specificationRA
assert_paper_axioms RGA.Strict.Investigation.six_event_no_history
assert_paper_axioms RGA.Strict.Investigation.six_event_primary_escape
assert_paper_axioms RGA.CrossedExecution.execution
assert_paper_axioms RGA.CrossedExecution.Evidence.mint_honest
assert_paper_axioms RGA.CrossedExecution.Evidence.mint_certified
assert_paper_axioms RGA.CrossedExecution.Evidence.observed_execution
assert_paper_axioms RGA.CrossedExecution.Evidence.final_read
assert_paper_axioms RGA.CrossedExecution.Evidence.strict_failure
assert_paper_axioms RGA.CrossedExecution.Evidence.not_every_certified_strict
assert_paper_axioms RGA.Identified.canonical_respects_specVisibility
assert_paper_axioms RGA.Identified.versions_of_execution
assert_paper_axioms RGA.Identified.projection_does_not_factor
assert_paper_axioms RGA.Identified.certifiedStrictRA
assert_paper_axioms RGA.Identified.certifiedStrictRAV
assert_paper_axioms RGA.Identified.certifiedMissingNoopRA
assert_paper_axioms RGA.Identified.certifiedMissingNoopRAV
assert_paper_axioms RGA.Identified.certifiedStrictExecutions
assert_paper_axioms RGA.Identified.certifiedStrictExecutionsV
assert_paper_axioms RGA.Comparison.strict_alphabet_comparison
assert_paper_axioms RGA.Comparison.identified_missing_noop
assert_paper_axioms RGA.AllocatingInvestigation.transition_projects
assert_paper_axioms RGA.AllocatingInvestigation.runs_project
assert_paper_axioms RGA.AllocatingInvestigation.projected_crossed_exclusion
assert_paper_axioms RGA.AllocatingInvestigation.crossed_no_history
assert_paper_axioms RGA.AllocatingCounterexample.not_specificationRA
assert_paper_axioms RGA.AllocatingCounterexample.certified_counterexample
assert_paper_axioms RGA.Comparison.allocating_alphabet_comparison
assert_paper_axioms RGA.Comparison.not_every_certified_allocating
assert_paper_axioms RGA.Comparison.same_execution_comparison
assert_paper_axioms HistorySpec.withInputs_commutes_iff
assert_paper_axioms HistoryMachine.toSpec_withInputs
assert_paper_axioms projected_withInputs
assert_paper_axioms EventSpecificationRALinearizable.active
assert_paper_axioms RGA.EventSpec.insertion_uses_timestamp
assert_paper_axioms RGA.EventSpec.deletion_uses_target
assert_paper_axioms RGA.EventSpec.replica_independent
assert_paper_axioms RGA.EventSpec.commutes_iff
assert_paper_axioms RGA.EventSpec.versions_of_execution
assert_paper_axioms RGA.EventSpec.certifiedRA
assert_paper_axioms RGA.EventSpec.certifiedRAV
assert_paper_axioms RGA.EventSpec.certifiedLiteralRA
assert_paper_axioms RGA.EventSpec.certifiedLiteralRAV
assert_paper_axioms RGA.EventSpec.certifiedMissingRA
assert_paper_axioms RGA.EventSpec.certifiedMissingRAV
assert_paper_axioms RGA.EventSpec.certifiedExecutions
assert_paper_axioms RGA.EventSpec.certifiedExecutionsV
assert_paper_axioms RGA.EventSpec.crossed_accepted
assert_paper_axioms RGA.EventSpec.supplied_inputs_control
assert_paper_axioms commutationCompatibility_iff_conflictsCovered
assert_paper_axioms projectedSpecVisibility_sub_paperOrder
assert_paper_axioms eventSpecificationRA_of_compatibility
assert_paper_axioms specificationRA_of_fiveVCs_compatible
assert_paper_axioms ORSet.commutationCompatibility
assert_paper_axioms ORSet.eventCommutationCompatibility
assert_paper_axioms CriterionCounterexample.commutationCompatibility_fails

-- Full-input bridge: total simulation and both mint/trace-sensitive routes.
assert_paper_axioms restricted_of_all_commute
assert_paper_axioms EventSequentialSimulation.fold_rel
assert_paper_axioms EventSequentialSimulation.sound
assert_paper_axioms EventVersionsSpecificationRA.heads
assert_paper_axioms event_versions_of_canonical_total
assert_paper_axioms event_versions_of_canonical_issued
assert_paper_axioms event_versions_of_canonical_execution
assert_paper_axioms EventCertifiedSpecificationRAV.ordinary
assert_paper_axioms event_certified_of_join_total
assert_paper_axioms event_certified_of_join_issued
assert_paper_axioms event_certified_of_join_execution
assert_paper_axioms event_certified_of_fiveVCs_total
assert_paper_axioms event_certified_of_fiveVCs_issued
assert_paper_axioms event_certified_of_fiveVCs_execution
assert_paper_axioms EventCertifiedSpecificationRA.executions
assert_paper_axioms EventCertifiedSpecificationRAV.executions
assert_paper_axioms GuardedHistory.updates_run
assert_paper_axioms GuardedHistory.admits_updates_query
assert_paper_axioms GuardedHistory.recorded_prefix
assert_paper_axioms GuardedHistory.rejects_first_update
assert_paper_axioms event_versions_of_guarded_certificate

-- Independent specifications and positive/negative controls.
assert_paper_axioms ORSet.EventSpec.certifiedVersionsRAV
assert_paper_axioms ORSet.EventSpec.certifiedExecutionsV
assert_paper_axioms ORSet.EventSpec.rawRA
assert_paper_axioms RGA.EventMigration.history
assert_paper_axioms RGA.EventMigration.certifiedV
assert_paper_axioms RGA.EventMigration.executionsV
assert_paper_axioms RGA.EventMigration.crossed_control
assert_paper_axioms SimpleEventPorts.Add.certifiedV
assert_paper_axioms SimpleEventPorts.Finite.certifiedV
assert_paper_axioms SimpleEventPorts.Boolean.certifiedV
assert_paper_axioms SimpleEventPorts.Delta.certifiedV
assert_paper_axioms SimpleEventPorts.add_control
assert_paper_axioms SimpleEventPorts.finite_add_control
assert_paper_axioms SimpleEventPorts.boolean_control
assert_paper_axioms SimpleEventPorts.immutable_map_control
assert_paper_axioms SimpleEventPorts.increment_control
assert_paper_axioms SimpleEventPorts.pn_control
assert_paper_axioms BoundedCounterEvent.certifiedV
assert_paper_axioms BoundedCounterEvent.account_control
assert_paper_axioms BoundedCounterEvent.initial_decrement_rejected
assert_paper_axioms BoundedCounterEvent.commutationCompatibility_fails
assert_paper_axioms TreeMoveEvent.certifiedV
assert_paper_axioms TreeMoveEvent.origin_control
assert_paper_axioms AegisSheetEvent.certifiedV
assert_paper_axioms AegisSheetEvent.origin_control
assert_paper_axioms EfficientORSet.EventSpec.certifiedVersionsRAV
assert_paper_axioms EfficientORSet.EventSpec.certifiedExecutionsV
assert_paper_axioms EfficientORSet.EventSpec.noncommutation_does_not_factor
assert_paper_axioms EfficientORSet.EventSpec.restrictedLaws_impossible
assert_paper_axioms ORSetBridgeControls.exact_remove_control
assert_paper_axioms ORSetBridgeControls.efficient_remove_control
assert_paper_axioms ORSetBridgeControls.mutant_causal_control
assert_paper_axioms ORSetBridgeControls.mutant_compatibility_fails
assert_paper_axioms ORSetBridgeControls.compatibility_controls

-- Exact production scope, including independently checked incompatibilities.
assert_paper_axioms PolicyObstructions.Queue.no_restricted_policy
assert_paper_axioms PolicyObstructions.MVR.no_restricted_policy
assert_paper_axioms RGA.EmbeddingObstructions.Embedded.no_restricted_policy
assert_paper_axioms RGA.EmbeddingObstructions.Sided.no_restricted_policy
assert_paper_axioms RGA.EmbeddingObstructions.peritext_no_restricted_policy
assert_paper_axioms RGA.EmbeddingObstructions.SidedPeritext.core_no_restricted_policy
assert_paper_axioms RGA.EmbeddingObstructions.SidedPeritext.rich_no_restricted_policy
assert_paper_axioms RGA.EmbeddingObstructions.RegisteredFugueMax.no_restricted_policy
assert_paper_axioms MigrationCoverage.packages_eq_production
assert_paper_axioms MigrationCoverage.names_eq_production
assert_paper_axioms MigrationCoverage.every_production_entry
assert_paper_axioms MigrationCoverage.counts
assert_paper_axioms MigrationCoverage.exactORSet
assert_paper_axioms MigrationCoverage.efficient_direct

-- Corrected guarded registry campaign: positive VC routes and guarded exclusions.
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.gsetExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.gsetExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.gsetExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.gsetExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.addStoreExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.addStoreExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.addStoreExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.addStoreExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.finiteAddExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.finiteAddExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.finiteAddExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.finiteAddExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.counterExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.counterExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.counterExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.counterExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.iocExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.iocExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.iocExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.iocExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.pnExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.pnExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.pnExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.pnExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.booleanSetExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.booleanSetExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.booleanSetExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.booleanSetExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.booleanMapExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.booleanMapExecutions
assert_paper_axioms AbstractMRDT.Guarded.SimplePorts.booleanMapExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.SimplePorts.booleanMapExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.boundedExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.boundedExecutions
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.boundedExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.boundedExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.treeExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.treeExecutions
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.treeExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.treeExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.sheetExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.sheetExecutions
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.sheetExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.sheetExecutionsV
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.rgaExecutions
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.rgaExecutions
assert_paper_axioms AbstractMRDT.Guarded.ScopedPorts.rgaExecutionsV
assert_commuting_vc_dependencies AbstractMRDT.Guarded.ScopedPorts.rgaExecutionsV
assert_paper_axioms GuardedQueueMVR.Queue.no_laws
assert_paper_axioms GuardedQueueMVR.MVR.no_laws
assert_paper_axioms GuardedQueueMVR.Queue.control
assert_paper_axioms GuardedQueueMVR.MVR.origin_control
assert_paper_axioms GuardedQueueMVR.MVR.control
assert_paper_axioms GuardedRGAObstructions.embedded_no_laws
assert_paper_axioms GuardedRGAObstructions.Sided.no_laws
assert_paper_axioms GuardedRGAObstructions.peritext_no_laws
assert_paper_axioms GuardedRGAObstructions.SidedPeritext.core_no_laws
assert_paper_axioms GuardedRGAObstructions.SidedPeritext.rich_no_laws
assert_paper_axioms GuardedRGAObstructions.RegisteredFugueMax.no_laws
assert_paper_axioms GuardedLWWExclusion.source_policy_excluded
assert_paper_axioms GuardedLWWExclusion.empty_policy_possible
assert_paper_axioms GuardedCoverage.packages_eq_production
assert_paper_axioms GuardedCoverage.every_production_entry
assert_paper_axioms GuardedCoverage.counts
assert_paper_axioms GuardedCoverage.ProvedResult.storedCanonical
assert_paper_axioms GuardedCoverage.inventory_length
assert_paper_axioms GuardedRGAObstructions.embedded_guarded_control
assert_paper_axioms GuardedRGAObstructions.sided_guarded_control
assert_paper_axioms GuardedRGAObstructions.peritext_issuer_control
assert_paper_axioms GuardedRGAObstructions.core_issuer_control
assert_paper_axioms GuardedRGAObstructions.rich_issuer_control
assert_paper_axioms GuardedRGAObstructions.RegisteredFugueMax.never_issuable
assert_paper_axioms LWW.GuardedPort.certificate
assert_paper_axioms LWW.GuardedPort.executions
assert_paper_axioms LWW.GuardedPort.executionsV
assert_paper_axioms LWW.GuardedPort.convergence
assert_paper_axioms LWW.GuardedPort.control
assert_commuting_vc_dependencies LWW.GuardedPort.executions
assert_commuting_vc_dependencies LWW.GuardedPort.executionsV

-- Certified-scope increments are audited separately from complete ports.
assert_paper_axioms CertifiedReplay.legal_swap
assert_paper_axioms CertifiedReplay.represented_fold
assert_paper_axioms CertifiedReplay.convergence_on
assert_paper_axioms CertifiedReplay.canonical_unique
assert_paper_axioms CertifiedHistory.versions_of_representation
assert_paper_axioms CertifiedHistory.storedCanonical
assert_paper_axioms CertifiedQueueMVR.MVR.concurrent_commutes
assert_paper_axioms CertifiedQueueMVR.MVR.scope_laws
assert_paper_axioms CertifiedMVRHistory.replay_history
assert_paper_axioms CertifiedRGAReplay.Embedded.eligible_inserts_commute
assert_paper_axioms CertifiedRGAReplay.Sided.eligible_inserts_commute
assert_paper_axioms CertifiedRGAScope.Embedded.laws
assert_paper_axioms CertifiedRGAScope.Sided.laws

-- Replay/history increments must not inherit correctness through an existing
-- datatype Join or a stored-state certificate that already assumes that Join.
open Lean Elab Command in
elab "assert_certified_replay_dependencies " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  let forbidden := [
    "Sal.MRDTs.Instances.MVRLive.represents_merge",
    "Sal.MRDTs.Instances.MVRLive.represented_of_mintCertifiedV",
    "Sal.MRDTs.Instances.MVRLive.represented_of_execution",
    "Sal.MRDTs.Instances.MVRLive.sequentialCorrectness",
    "Sal.MRDTs.Instances.EmbedRGA.e_join_at",
    "Sal.MRDTs.Instances.SidedEmbedRGA.s_join_at"].map String.toName
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if forbidden.contains current then
        throwError "{n} uses prior datatype correctness {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending

assert_certified_replay_dependencies CertifiedQueueMVR.MVR.scope_laws
assert_certified_replay_dependencies CertifiedMVRHistory.replay_history
assert_certified_replay_dependencies CertifiedRGAScope.Embedded.laws
assert_certified_replay_dependencies CertifiedRGAScope.Sided.laws

assert_paper_axioms CertifiedQueueMVR.Queue.certified_control
assert_paper_axioms CertifiedQueueMVR.Queue.no_local_payload_policy
assert_paper_axioms CertifiedQueueMVR.Queue.no_scoped_policy

assert_paper_axioms CertifiedReplay.emptyPolicyLaws_of_diamonds
assert_paper_axioms CertifiedQueueMVR.MVR.Controls.mint_not_reissuance
assert_paper_axioms CertifiedQueueMVR.MVR.RawVC.mergeVCs
assert_paper_axioms CertifiedQueueMVR.MVR.RawVC.representationJoin
assert_paper_axioms CertifiedQueueMVR.MVR.Certificate.executions
assert_paper_axioms CertifiedQueueMVR.MVR.Certificate.executionsV
assert_paper_axioms CertifiedQueueMVR.MVR.Certificate.convergence
assert_paper_axioms CertifiedRGAIssuance.Embedded.laws
assert_paper_axioms CertifiedRGAIssuance.Sided.laws
assert_paper_axioms CertifiedRGAIssuance.Peritext.laws
assert_paper_axioms CertifiedRGAIssuance.SidedPeritext.laws
assert_paper_axioms CertifiedRGAIssuance.SidedPeritext.rich_laws
assert_paper_axioms CertifiedRGAIssuance.FugueMax.laws

open Lean Elab Command in
elab "assert_certified_mvr_dependencies " n:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  let forbidden := [
    "Sal.MRDTs.Instances.MVRLive.represents_merge",
    "Sal.MRDTs.Instances.MVRLive.represented_of_mintCertifiedV",
    "Sal.MRDTs.Instances.MVRLive.represented_of_execution",
    "Sal.MRDTs.Instances.MVRLive.virtualMergeBaseState_represents",
    "Sal.MRDTs.Instances.MVRLive.sequentialCorrectness",
    "Sal.MRDTs.Instances.MVRLive.replayAdequacy"].map String.toName
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if forbidden.contains current then
        throwError "{n} uses legacy MVR correctness {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending
  for required in [``AbstractMRDT.Raw.join_at_sizes,
      ``CertifiedQueueMVR.MVR.RawVC.mergeVCs,
      ``CertifiedQueueMVR.MVR.Execution.vcVirtualMergeBaseStateRepresents,
      ``CertifiedMVRHistory.replay_history,
      ``CertifiedReplay.restrictedEmpty] do
    unless seen.contains required do
      throwError "{n} omits certified VC/history dependency {required}"

assert_certified_mvr_dependencies CertifiedQueueMVR.MVR.Certificate.versions
assert_certified_mvr_dependencies CertifiedQueueMVR.MVR.Certificate.executions
assert_certified_mvr_dependencies CertifiedQueueMVR.MVR.Certificate.executionsV

assert_paper_axioms CertifiedCoverage.packages_eq_production
assert_paper_axioms CertifiedCoverage.counts
assert_paper_axioms CertifiedCoverage.mvrResult
assert_paper_axioms CertifiedReplay.restrict_laws

assert_paper_axioms GuardedHistory.language_commutes_of_legal_swap
assert_paper_axioms CertifiedClosedExecution.canonicalConfig_of_execution
assert_paper_axioms CertifiedRGACertificate.Embedded.storedCanonical
assert_paper_axioms CertifiedRGACertificate.Sided.storedCanonical
assert_paper_axioms CertifiedRGAHistory.embed_canonical_specVisibility
assert_paper_axioms CertifiedRGAHistory.sided_canonical_specVisibility
assert_paper_axioms CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGACoreMergeVC.representationJoin
assert_paper_axioms CertifiedRGARichVC.mergeVCs
assert_paper_axioms CertifiedRGARichVC.representationJoin

open Lean Elab Command in
elab "assert_certified_rga_dependencies " n:ident " using " vc:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let equations ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo vc
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  let forbidden := [
    "Sal.MRDTs.Instances.EmbedRGA.e_join_at",
    "Sal.MRDTs.Instances.SidedEmbedRGA.s_join_at",
    "Sal.MRDTs.Instances.SidedPeritext.core_join_at",
    "Sal.MRDTs.Instances.SidedPeritext.rich_join_at",
    "Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.f_join_at",
    "Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.join_of_mint",
    "Sal.MRDTs.Instances.ProductionRGA.embedSequentialCorrectness",
    "Sal.MRDTs.Instances.ProductionRGA.sidedSequentialCorrectness"].map String.toName
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if forbidden.contains current then
        throwError "{n} uses legacy RGA correctness {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending
  for required in [``AbstractMRDT.Raw.join_at_sizes, equations,
      ``CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV] do
    unless seen.contains required do
      throwError "{n} omits certified VC/execution dependency {required}"

assert_certified_rga_dependencies CertifiedRGACertificate.Embedded.storedCanonical using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies CertifiedRGACertificate.Sided.storedCanonical using CertifiedRGAVC.Sided.mergeVCs

assert_paper_axioms CertifiedRGACoreExecution.representedVersions
assert_paper_axioms CertifiedRGACoreExecution.Rich.representedVersions
assert_paper_axioms CertifiedFugueVCExecution.representedVersions
assert_certified_rga_dependencies CertifiedRGACoreExecution.representedVersions using CertifiedRGACoreMergeVC.mergeVCs
assert_certified_rga_dependencies CertifiedRGACoreExecution.Rich.representedVersions using CertifiedRGACoreMergeVC.mergeVCs
assert_certified_rga_dependencies CertifiedFugueVCExecution.representedVersions using CertifiedFugueVC.mergeVCs
assert_paper_axioms CertifiedRGARawOrderObstruction.certified_raw_criterion_failure
assert_paper_axioms CertifiedRGARawOrderObstruction.admitted_history_control

-- Rich changes the public query, reusing the new Core operational VC proof.
assert_paper_axioms CertifiedRGACoreCertificate.correct
assert_certified_rga_dependencies CertifiedRGACoreCertificate.correct using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGACoreCertificate.correctV
assert_certified_rga_dependencies CertifiedRGACoreCertificate.correctV using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGACoreCertificate.executions
assert_certified_rga_dependencies CertifiedRGACoreCertificate.executions using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGACoreCertificate.executionsV
assert_certified_rga_dependencies CertifiedRGACoreCertificate.executionsV using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGARichCertificate.correct
assert_certified_rga_dependencies CertifiedRGARichCertificate.correct using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGARichCertificate.correctV
assert_certified_rga_dependencies CertifiedRGARichCertificate.correctV using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGARichCertificate.executions
assert_certified_rga_dependencies CertifiedRGARichCertificate.executions using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedRGARichCertificate.executionsV
assert_certified_rga_dependencies CertifiedRGARichCertificate.executionsV using CertifiedRGACoreMergeVC.mergeVCs
assert_paper_axioms CertifiedSidedRawOrderObstruction.certified_raw_criterion_failure
assert_paper_axioms CertifiedSidedRawOrderObstruction.admitted_history_control
assert_paper_axioms CertifiedSidedRawOrderObstruction.no_raw_order_history
assert_paper_axioms CertifiedPeritextRawOrderObstruction.certified_raw_criterion_failure
assert_paper_axioms CertifiedPeritextRawOrderObstruction.admitted_history_control
assert_paper_axioms CertifiedPeritextRawOrderObstruction.no_raw_order_history

assert_paper_axioms CertifiedFugueRawOrderObstruction.certified_raw_criterion_failure
assert_paper_axioms CertifiedFugueRawOrderObstruction.no_raw_order_history
assert_paper_axioms CertifiedFugueRawOrderObstruction.admitted_history_control
assert_paper_axioms CertifiedFugueRawOrderObstruction.original_preparation
assert_paper_axioms CertifiedFugueRawOrderObstruction.original_guards
assert_paper_axioms CertifiedFugueRawOrderObstruction.final_read

assert_paper_axioms CertifiedRGAOrderComparison.contracts_differ
assert_paper_axioms CertifiedRGAOrderComparison.main_pair_independent
assert_paper_axioms CertifiedRGAOrderComparison.main_has_no_extra_edge
assert_paper_axioms CertifiedRGAOrderComparison.goodHistory_respects_main
assert_paper_axioms CertifiedRGAOrderComparison.paper_has_extra_edge

assert_paper_axioms CertifiedRGAOrderComparison.earlier_internal_replay_control
assert_paper_axioms CertifiedRGAOrderComparison.earlier_public_history_control

-- Invariant-scoped concrete commutation is a separate, explicit criterion.
assert_paper_axioms InvariantOrder.order_universal
assert_paper_axioms InvariantOrder.versions_universal
assert_paper_axioms InvariantOrder.Closed.applySeq
assert_paper_axioms InvariantReplay.convergence_on
assert_paper_axioms InvariantReplay.restrict_restrictedLaws
assert_paper_axioms CertifiedRGAInvariant.closed
assert_paper_axioms CertifiedRGAInvariant.invariant_commutes_iff
assert_paper_axioms CertifiedRGAInvariant.birth_delete_noncommutes
assert_paper_axioms CertifiedRGAInvariantHistory.canonical_valid_history
assert_paper_axioms CertifiedRGAInvariantReplay.laws
assert_paper_axioms CertifiedRGAInvariantReplay.storedCanonical
assert_paper_axioms CertifiedRGAInvariantCertificate.correct
assert_paper_axioms CertifiedRGAInvariantCertificate.correctV
assert_paper_axioms CertifiedRGAInvariantCertificate.executions
assert_paper_axioms CertifiedRGAInvariantCertificate.executionsV
assert_paper_axioms CertifiedRGAInvariantCertificate.virtual_base_valid
assert_paper_axioms CertifiedRGAInvariantCertificate.implementation_replay_equal
assert_certified_rga_dependencies CertifiedRGAInvariantCertificate.correct using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies CertifiedRGAInvariantCertificate.correctV using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies CertifiedRGAInvariantCertificate.executions using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies CertifiedRGAInvariantCertificate.executionsV using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies CertifiedRGAInvariantCertificate.virtual_base_valid using CertifiedRGAVC.Embedded.mergeVCs
assert_paper_axioms CertifiedRGAInvariantControls.explanation_control
assert_paper_axioms CertifiedRGAInvariantControls.extra_edge_control
assert_paper_axioms CertifiedRGAInvariantControls.own_birth_control
assert_paper_axioms CertifiedRGAInvariantControls.scratch_excluded
assert_paper_axioms CertifiedRGAInvariantControls.certified_execution_comparison

open Lean Elab Command in
elab "assert_invariant_dependency " n:ident " uses " dependency:ident : command => do
  let root ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let required ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo dependency
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [root]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending
  unless seen.contains required do
    throwError "{n} omits invariant proof dependency {required}"

assert_invariant_dependency CertifiedRGAInvariantCertificate.correct uses CertifiedRGAInvariantHistory.canonical_valid_history
assert_invariant_dependency CertifiedRGAInvariantCertificate.correct uses CertifiedRGAInvariant.semantic_commutes
assert_invariant_dependency CertifiedRGAInvariantCertificate.correct uses InvariantReplay.restrict_restrictedLaws
assert_invariant_dependency CertifiedRGAInvariantCertificate.virtual_base_valid uses CertifiedClosedExecution.virtualMergeBaseState_canonical
assert_invariant_dependency CertifiedRGAInvariantCertificate.implementation_replay_equal uses InvariantReplay.convergence_on


-- Remaining invariant-scoped ports and the specification-only Fugue obstruction.
assert_paper_axioms CertifiedSidedInvariantCertificate.correct
assert_certified_rga_dependencies CertifiedSidedInvariantCertificate.correct using CertifiedRGAVC.Sided.mergeVCs
assert_paper_axioms CertifiedSidedInvariantCertificate.correctV
assert_certified_rga_dependencies CertifiedSidedInvariantCertificate.correctV using CertifiedRGAVC.Sided.mergeVCs
assert_paper_axioms CertifiedSidedInvariantCertificate.executions
assert_certified_rga_dependencies CertifiedSidedInvariantCertificate.executions using CertifiedRGAVC.Sided.mergeVCs
assert_paper_axioms CertifiedSidedInvariantCertificate.executionsV
assert_certified_rga_dependencies CertifiedSidedInvariantCertificate.executionsV using CertifiedRGAVC.Sided.mergeVCs
assert_paper_axioms CertifiedSidedInvariantCertificate.virtual_base_valid
assert_certified_rga_dependencies CertifiedSidedInvariantCertificate.virtual_base_valid using CertifiedRGAVC.Sided.mergeVCs
assert_paper_axioms CertifiedSidedInvariantCertificate.implementation_replay_equal
assert_invariant_dependency CertifiedSidedInvariantCertificate.implementation_replay_equal uses InvariantReplay.convergence_on
assert_paper_axioms CertifiedPeritextInvariantCertificate.correct
assert_certified_rga_dependencies CertifiedPeritextInvariantCertificate.correct using CertifiedRGAVC.Embedded.mergeVCs
assert_paper_axioms CertifiedPeritextInvariantCertificate.correctV
assert_certified_rga_dependencies CertifiedPeritextInvariantCertificate.correctV using CertifiedRGAVC.Embedded.mergeVCs
assert_paper_axioms CertifiedPeritextInvariantCertificate.executions
assert_certified_rga_dependencies CertifiedPeritextInvariantCertificate.executions using CertifiedRGAVC.Embedded.mergeVCs
assert_paper_axioms CertifiedPeritextInvariantCertificate.executionsV
assert_certified_rga_dependencies CertifiedPeritextInvariantCertificate.executionsV using CertifiedRGAVC.Embedded.mergeVCs
assert_paper_axioms CertifiedPeritextInvariantCertificate.virtual_base_valid
assert_certified_rga_dependencies CertifiedPeritextInvariantCertificate.virtual_base_valid using CertifiedRGAVC.Embedded.mergeVCs
assert_paper_axioms CertifiedPeritextInvariantCertificate.implementation_replay_equal
assert_invariant_dependency CertifiedPeritextInvariantCertificate.implementation_replay_equal uses InvariantReplay.convergence_on
assert_paper_axioms CertifiedSidedInvariant.closed
assert_paper_axioms CertifiedSidedInvariant.invariant_commutes_iff
assert_paper_axioms CertifiedSidedInvariantReplay.laws
assert_paper_axioms CertifiedSidedInvariantReplay.canonical_unique
assert_paper_axioms CertifiedSidedInvariantHistory.canonical_valid_history
assert_paper_axioms CertifiedSidedInvariantControls.certified_execution_comparison
assert_paper_axioms CertifiedSidedInvariantControls.final_query_control
assert_paper_axioms CertifiedSidedInvariantControls.commutation_control
assert_paper_axioms CertifiedPeritextInvariantCertificate.mergeVCs
assert_paper_axioms CertifiedPeritextInvariantCertificate.representationJoin
assert_paper_axioms CertifiedPeritextInvariantControls.certified_execution_comparison
assert_paper_axioms CertifiedPeritextInvariantControls.explanation_control
assert_paper_axioms CertifiedPeritextInvariantControls.extra_edge_control
assert_paper_axioms CertifiedPeritextInvariantControls.own_birth_control
assert_paper_axioms CertifiedPeritextInvariantControls.rendered_control
assert_paper_axioms CertifiedFugueInvariant.closed
assert_paper_axioms CertifiedFugueInvariant.invariant_commutes_iff
assert_paper_axioms CertifiedFugueInvariant.stored_valid
assert_paper_axioms CertifiedFugueInvariant.virtual_base_valid
assert_paper_axioms CertifiedFugueInvariantReplay.laws
assert_paper_axioms CertifiedFugueInvariantReplay.storedCanonical
assert_paper_axioms CertifiedFugueInvariantReplay.canonical_unique
assert_paper_axioms CertifiedFugueInvariantObstruction.deletion_replacement_spec_conflict
assert_paper_axioms CertifiedFugueInvariantObstruction.no_spec_visible_history
assert_paper_axioms CertifiedFugueInvariantObstruction.certified_failure
assert_paper_axioms CertifiedFugueInvariantObstruction.trace_states_valid
assert_paper_axioms CertifiedFugueInvariantObstruction.domain_closed
assert_paper_axioms CertifiedFugueInvariantObstruction.implementation_spec_separation
assert_paper_axioms CertifiedFugueInvariantObstruction.valid_execution_counterexample
assert_invariant_dependency CertifiedSidedInvariantCertificate.correct uses CertifiedSidedInvariantHistory.canonical_valid_history
assert_invariant_dependency CertifiedSidedInvariantCertificate.correct uses CertifiedSidedInvariant.semantic_commutes
assert_invariant_dependency CertifiedPeritextInvariantCertificate.correct uses CertifiedRGAInvariantHistory.canonical_valid_history
assert_certified_rga_dependencies CertifiedFugueInvariant.stored_valid using CertifiedFugueVC.mergeVCs
assert_certified_rga_dependencies CertifiedFugueInvariant.virtual_base_valid using CertifiedFugueVC.mergeVCs
assert_certified_rga_dependencies CertifiedFugueInvariantReplay.storedCanonical using CertifiedFugueVC.mergeVCs
assert_invariant_dependency CertifiedFugueInvariantReplay.canonical_unique uses InvariantReplay.convergence_on
assert_invariant_dependency CertifiedFugueInvariantObstruction.certified_failure uses CertifiedFugueRawOrderObstruction.mint_certified
assert_invariant_dependency CertifiedFugueInvariantObstruction.certified_failure uses CertifiedFugueInvariantObstruction.deletion_replacement_spec_conflict

open Lean Elab Command in
elab "assert_fugue_spec_only" : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut pending := [``CertifiedFugueInvariantObstruction.certified_failure]
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    unless seen.contains current do
      seen := seen.insert current
      for forbidden in ["deletion_insertion_raw_conflict", "required_paperOrder",
          "no_raw_order_history", "certified_raw_criterion_failure", "scratch"] do
        if current.toString.endsWith forbidden then
          throwError "Fugue specification obstruction uses raw-order evidence {current}"
      if let some info := env.find? current then
        pending := info.getUsedConstantsAsSet.toList ++ pending

assert_fugue_spec_only

-- Separate anchored-enqueue Queue: actual FIFO scheduling, exact tagged head,
-- new merge VCs, and ordinary/recursive-virtual certified executions.
assert_paper_axioms AnchoredQueue.History.correct
assert_paper_axioms AnchoredQueue.History.certificate
assert_certified_rga_dependencies AnchoredQueue.History.certificate using CertifiedRGAVC.Embedded.mergeVCs
assert_paper_axioms AnchoredQueue.History.correctV
assert_paper_axioms AnchoredQueue.History.executions
assert_paper_axioms AnchoredQueue.History.executionsV
assert_certified_rga_dependencies AnchoredQueue.History.correct using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies AnchoredQueue.History.correctV using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies AnchoredQueue.History.executions using CertifiedRGAVC.Embedded.mergeVCs
assert_certified_rga_dependencies AnchoredQueue.History.executionsV using CertifiedRGAVC.Embedded.mergeVCs
assert_invariant_dependency AnchoredQueue.History.correct uses AnchoredQueue.History.schedule_publicWitness
assert_invariant_dependency AnchoredQueue.History.correct uses AnchoredQueue.causal_birth_delete_predecessor
assert_invariant_dependency AnchoredQueue.History.correct uses AnchoredQueue.liveEndpoint
assert_invariant_dependency AnchoredQueue.History.correct uses AnchoredQueue.History.unrelated_public_language
assert_invariant_dependency AnchoredQueue.History.correctV uses AnchoredQueue.Public.virtual_base
assert_paper_axioms AnchoredQueue.mergeVCs
assert_paper_axioms AnchoredQueue.representationJoin
assert_paper_axioms AnchoredQueue.scoped_laws
assert_paper_axioms AnchoredQueue.concurrent_commutes
assert_paper_axioms AnchoredQueue.closed
assert_paper_axioms AnchoredQueue.stored_valid
assert_paper_axioms AnchoredQueue.virtual_base_valid
assert_paper_axioms AnchoredQueue.storedCanonical
assert_paper_axioms AnchoredQueue.storedCanonicalV
assert_paper_axioms AnchoredQueue.History.stored_publicWitness
assert_paper_axioms AnchoredQueue.History.public_versions
assert_paper_axioms AnchoredQueue.Controls.concurrent_same_tail
assert_paper_axioms AnchoredQueue.Controls.singleton_dequeue_enqueue
assert_paper_axioms AnchoredQueue.Controls.duplicate_dequeues
assert_paper_axioms AnchoredQueue.Controls.postmerge_continuation
assert_paper_axioms AnchoredQueue.Controls.independent_fifo_controls
assert_paper_axioms AnchoredQueue.Controls.public_head_controls
assert_paper_axioms AnchoredQueue.PublicControls.certified
assert_paper_axioms AnchoredQueue.PublicControls.certifiedV
assert_paper_axioms AnchoredQueue.PublicControls.public_certified_control
assert_paper_axioms AnchoredQueue.PublicControls.public_ra_control
assert_paper_axioms AnchoredQueue.HistoryControls.duplicate_removal
assert_paper_axioms AnchoredQueue.HistoryControls.fresh_births
assert_paper_axioms AnchoredQueue.HistoryControls.named_head
assert_paper_axioms AnchoredQueue.HistoryControls.removed_anchor_ignored

assert_paper_axioms PaperPresentation.uniform_versionsRA_of_paperOrder_witness

end Sal.MRDTs.Paper1
