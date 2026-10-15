import Sal.Artifact.Paper

/-!
# Reading the mechanisation alongside the paper

Open this file in a Lean editor and inspect each checked declaration's type.
The comments follow the paper's compiled statement numbering. Definitions and
sufficient theorems are distinguished below; extra hypotheses are part of the
checked result. The accompanying `docs/paper-index.md` gives source line links
and records the places where a shorter paper display is not the exact type of
an existing endpoint. This navigation file adds no mathematical assumptions.
-/

/- Definition 2.1: the policy is packaged separately from the implementation. -/
#check Sal.MRDTs.MRDTSig
#check Sal.MRDTs.Paper1.OperationPolicy

/- Section 3 and Lemma 3.1: explicit version storage and ancestor bookkeeping.
`IsGCA` means greatest common ancestor; arbitrary maximal common ancestors do
not have the same intersection contract. Virtual bases are handled below. -/
#check Sal.MRDTs.Configuration
#check Sal.MRDTs.Step
#check Sal.MRDTs.StepV
#check Sal.MRDTs.IsGCA
#check Sal.MRDTs.gca_events_of_storeInv
#check Sal.MRDTs.storeInv_reachable

/- Definitions 4.1 and 4.3: per-event-set order and exact finite enumeration.
For Lemma 4.2, the selected API exposes the relation and policy no-chain fact,
not a separately named cross-event-set non-reversal theorem. Single-set
acyclicity should not be mistaken for that exact statement. -/
#check Sal.MRDTs.Paper1.paperOrder
#check Sal.MRDTs.Paper1.GuardedReplay.Laws.payload_no_chain
#check Sal.MRDTs.Paper1.GuardedReplay.paperOrder_acyclic
#check Sal.MRDTs.Foundation.listPermOf
#check Sal.MRDTs.Foundation.respects

/- Definition 4.4: general finite-run languages; deterministic machines are
an optional sufficient presentation used by the later simulation method. -/
#check Sal.MRDTs.Paper1.HistorySpec
#check Sal.MRDTs.Paper1.HistoryMachine
#check Sal.MRDTs.Paper1.HistoryMachine.toSpec
#check Sal.MRDTs.Paper1.DeterministicSpec

/- Definition 4.5: all stored versions, active heads, and the stronger uniform
quantifier order. The event/specification-visible criterion keeps full inputs
and requires one witness to respect both relevant relations. -/
#check Sal.MRDTs.Paper1.VersionsRALinearizable
#check Sal.MRDTs.Paper1.RALinearizable
#check Sal.MRDTs.Paper1.UniformVersionsRALinearizable
#check Sal.MRDTs.Paper1.EventVersionsSpecificationRA

/- Theorem 4.6 and Definitions 4.7–4.8: existence and equality are separate.
The guarded theorem retains its event/context assumptions. Canonicality is
exact concrete equality with a replay, not equality only of query answers. -/
#check Sal.MRDTs.Paper1.GuardedReplay.exists_paperOrder_enumeration
#check Sal.MRDTs.Paper1.ConcreteMRDT.replay_equal
#check Sal.MRDTs.Paper1.ConcreteMRDT.canonical_exists
#check Sal.MRDTs.Paper1.ConcreteMRDT.Canonical
#check Sal.MRDTs.CanonicalConfig

/- Theorem 5.1 and Lemma 5.2: five equations derive Join through finite-event
induction with representation uniqueness, initiality, enumerability and peel
supply. Stored-state preservation also retains original mint provenance.
The field order is VC1, VC2, VC4, VC3, VC5, so use the field names when reading. -/
#check Sal.MRDTs.Paper1.ConcreteMRDT.Raw.MergeVCs
#check Sal.MRDTs.Paper1.ConcreteMRDT.Raw.PeelChoice
#check Sal.MRDTs.Paper1.ConcreteMRDT.Raw.ReplaySupply
#check Sal.MRDTs.Paper1.ConcreteMRDT.Raw.representationJoin_of_vcs
#check Sal.MRDTs.Paper1.CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
#check Sal.MRDTs.Paper1.CertifiedClosedExecution.virtualMergeBaseState_canonical

/- Theorem 6.1: this route uses global merge-free fold soundness, a sufficient
stronger premise than soundness only on stored-set linear extensions. The
simulation method establishes that global premise independently of merge. -/
#check Sal.MRDTs.Paper1.PaperPresentation.uniform_versionsRA_of_paperOrder_witness
#check Sal.MRDTs.Paper1.PaperPresentation.projected_versions_of_exact_total
#check Sal.MRDTs.Paper1.SequentialSimulation.sound
#check Sal.MRDTs.Paper1.EventSequentialSimulation.sound

/- Definitions 7.1–7.2 and Theorem 7.3: guard original generation, then select
an admitted independent history using certified execution evidence. This does
not require operations to be issued again at reordered intermediate states.
The five equations alone do not establish the specification's query meaning. -/
#check Sal.MRDTs.Issuance
#check Sal.MRDTs.MintHonest
#check Sal.MRDTs.MintCertifiedReach
#check Sal.MRDTs.MintCertifiedReachV
#check Sal.MRDTs.Paper1.IssuedHistoryAdequacy
#check Sal.MRDTs.Paper1.EventExecutionHistoryAdequacy
#check Sal.MRDTs.Paper1.certifiedRA_of_fiveVCs_issued
#check Sal.MRDTs.Paper1.event_certified_of_fiveVCs_execution
#check Sal.MRDTs.Paper1.ConcreteMRDT.ScopedVCConditions.executionsV

/- Section 8 extensions: invariant convergence retains legal and causal replay
premises. Pointwise operation labels transport an already justified history;
they do not turn arbitrary extra arguments into honestly issued operations. -/
#check Sal.MRDTs.Paper1.InvariantReplay.convergence_on
#check Sal.MRDTs.Paper1.OperationLabels.ops
#check Sal.MRDTs.Paper1.OperationLabels.specificationRA
#check Sal.MRDTs.Paper1.OperationLabelsInvariant.projectedVersionsRA
#check Sal.MRDTs.Paper1.Automation.CommonVerification.verify

/- Notion: typed create/insert/erase/split under its original protocol. The
structural and typed runtime entry retains that scope and is separate from
the uniform production registry. External demo executions and JSON conversion
remain executable evidence, documented in the reproduction guide. -/
#check Sal.MRDTs.Instances.NotionCoreStructuralMRDT.versions_witness
#check Sal.MRDTs.Research.NotionCoreStructuralRuntimeLedger.entry
