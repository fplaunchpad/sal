# Stable theorem manifest

The production build gate is `Sal.MRDTs.Metatheory.RefactorLedger`. The names
below are the stable paper-facing API; internal helper names are not part of
the compatibility contract.

## Framework

- `Sal.MRDTs.Issuance`
- `Sal.MRDTs.InteractionSpec`
- `Sal.MRDTs.interactionLoOn`
- `Sal.MRDTs.SequentialSpec`
- `Sal.MRDTs.SequentialCorrectnessCertificate`
- `Sal.MRDTs.IsSpecRALinearizable`
- `Sal.MRDTs.VerifiedMRDT`
- `Sal.MRDTs.PackagedMRDT`
- `Sal.MRDTs.Production.registry`
- `Sal.MRDTs.StateGCCertificate.exactState`
- `Sal.MRDTs.StateGCCoverage`
- `Sal.MRDTs.PackagedStateGC`
- `Sal.MRDTs.Production.StateGC.registry`
- `Sal.MRDTs.ConvergenceCertificate.sound`
- `Sal.MRDTs.MintCertifiedReach.toV`
- `Sal.MRDTs.Instances.InteractionSPOT.LWW.old_no_chain_refuted`

### Optional and migration certificates

- `Sal.MRDTs.SafetyCertificate`
- `Sal.MRDTs.SafetyCertificate.preservation`
- `Sal.MRDTs.SequentialRefinement`
- `Sal.MRDTs.ReplayAdequateMRDT`
- `Sal.MRDTs.StateGCProtocol.refines`
- `Sal.MRDTs.GC.execution_refines_noGC`
- `Sal.MRDTs.GC.runtime_refines_core`
- `Sal.MRDTs.GC.runtime_refines_coreV`
- `Sal.MRDTs.GC.CombinedSteps.refinesV`

## RGA and Peritext

- `Sal.MRDTs.Instances.RGA.verified`
- `Sal.MRDTs.Instances.RGA.rga_spec_linearizable`
- `Sal.MRDTs.Instances.RGA.rga_spec_linearizableV`
- `Sal.MRDTs.Instances.EmbedRGA.convergence`
- `Sal.MRDTs.Instances.SidedEmbedRGA.convergence`
- `Sal.MRDTs.Instances.ProductionRGA.embed`
- `Sal.MRDTs.Instances.ProductionRGA.sided`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fuguemax_maximally_noninterleaving`
- `Sal.MRDTs.Instances.Peritext.verified`
- `Sal.MRDTs.Instances.Peritext.render_sequentially_correct`
- `Sal.MRDTs.Instances.SidedPeritext.verified`
- `Sal.MRDTs.Instances.SidedPeritext.richVerified`
- `Sal.MRDTs.Instances.SidedPeritext.rich_sequentially_correct`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.Protocol.protocol`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.Protocol.refines`

## Peritext state collection

- `Sal.MRDTs.Instances.SidedPeritext.StateGC.collectText_query_preserved`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.collectedText_continuation_query`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.trimDeleted_query_preserved`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.dropMarkPair_query_preserved`
- `Sal.MRDTs.Instances.SidedPeritext.StateGC.Interaction.merge_text_after_epoch_translation`

## Other production instances

- `Sal.MRDTs.Instances.LWWRegister.verified`
- `Sal.MRDTs.Instances.LWWRegister.replay_lo_false`
- `Sal.MRDTs.Instances.LWWRegister.canonical_respects`
- `Sal.MRDTs.Instances.LWWRegister.timestamp_chain`
- `Sal.MRDTs.Instances.LWWRegister.chronological_winner`
- `Sal.MRDTs.Instances.LWWRegister.lower_timestamp_does_not_win`
- `Sal.MRDTs.Instances.TreeMove.verified`
- `Sal.MRDTs.Instances.TreeMove.render_safe`
- `Sal.MRDTs.Instances.TreeMove.sequentialSound`
- `Sal.MRDTs.Instances.TreeMove.selfMove_rejected`
- `Sal.MRDTs.Instances.TreeMove.GC.undoRedo_algorithm_refines`
- `Sal.MRDTs.Instances.TreeMove.GC.collectPrefix_exact`
- `Sal.MRDTs.Instances.TreeMove.GC.appendFresh_exact`
- `Sal.MRDTs.Instances.TreeMove.GC.fullyStable_collectTrash_query`
- `Sal.MRDTs.Instances.TreeMove.GC.refines`
- `Sal.MRDTs.Instances.AegisSheet.verified`
- `Sal.MRDTs.Instances.AegisSheet.spec_linearizable`
- `Sal.MRDTs.Instances.AegisSheet.spec_linearizableV`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.canonical_causalOriginLegal`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.concurrent_origins_causal_legal`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.unavailable_origin_not_causal_legal`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.no_view_only_step`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.row_tokens_distinguish_future`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.cell_versions_distinguish_future`
- `Sal.MRDTs.Instances.AegisSheet.Sequential.Abstraction.range_versions_distinguish_future`
- `Sal.MRDTs.Instances.AegisSheet.replayVerified` (internal compatibility
  package; its old whole-prefix legality is refuted by
  `Sequential.concurrent_origins_not_guarded_chronological`)
- `Sal.MRDTs.Instances.AegisSheet.sequentially_correct`
- `Sal.MRDTs.Instances.AegisSheet.observationally_correct`
- `Sal.MRDTs.Instances.AegisSheet.GC.certificate`
- `Sal.MRDTs.Instances.BoundedCounter.verified`
- `Sal.MRDTs.Instances.ORSet.verified`
- `Sal.MRDTs.Instances.ORSet.omitted_observed_tag_rejected`
- `Sal.MRDTs.Instances.ORSet.fabricated_tag_rejected`
- `Sal.MRDTs.Instances.ORSet.concurrent_remove_add_wins`
- `Sal.MRDTs.Instances.FlatCounters.counterVerified`
- `Sal.MRDTs.Instances.FlatCounters.iocVerified`
- `Sal.MRDTs.Instances.FlatCounters.pnVerified`
- `Sal.MRDTs.Instances.FlatGrowOnly.gosetVerified`
- `Sal.MRDTs.Instances.FlatGrowOnly.gomapVerified`
- `Sal.MRDTs.Instances.GSet.verified`

## Negative and internal evidence

These declarations are checked by `Sal.MRDTs.Metatheory.NegativeLedger` and
cannot enter `Production.registry` without a complete `VerifiedMRDT` for the
same signature.

- `Sal.MRDTs.Instances.MVR.replayVerified`
- `Sal.MRDTs.Instances.MVR.concurrentState_no_sequential_register`
- `Sal.MRDTs.Instances.Queue.replayVerified`
- `Sal.MRDTs.Instances.Queue.ConditioningSPOT.duplicate_dequeue_not_fifo`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fmGeneration`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fmConvergence`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fuguemax_ra_linearizable`

Run `./scripts/check-mrdt-refactor.sh` to check the manifest’s imported ledger,
forbidden-import and proof-hole scans, and all runtime conformance tests.
