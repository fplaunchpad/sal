# Stable theorem manifest

The production build gate is `Sal.MRDTs.Metatheory.RefactorLedger`. The names
below are the stable paper-facing API; internal helper names are not part of
the compatibility contract.

## Framework

- `Sal.MRDTs.GenerationContract`
- `Sal.MRDTs.SafetyCertificate`
- `Sal.MRDTs.SequentialRefinement`
- `Sal.MRDTs.VerifiedMRDT`
- `Sal.MRDTs.StateGCProtocol.refines`
- `Sal.MRDTs.GC.execution_refines_noGC`
- `Sal.MRDTs.GC.runtime_refines_core`
- `Sal.MRDTs.GC.runtime_refines_coreV`
- `Sal.MRDTs.GC.CombinedSteps.refinesV`

## RGA and Peritext

- `Sal.MRDTs.Instances.RGA.verified`
- `Sal.MRDTs.Instances.EmbedRGA.convergence`
- `Sal.MRDTs.Instances.SidedEmbedRGA.convergence`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fuguemax_maximally_noninterleaving`
- `Sal.MRDTs.Instances.SidedEmbedRGA.fuguemax_ra_linearizable`
- `Sal.MRDTs.Instances.Peritext.verified`
- `Sal.MRDTs.Instances.Peritext.render_sequentially_correct`
- `Sal.MRDTs.Instances.SidedPeritext.verified`
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

- `Sal.MRDTs.Instances.TreeMove.verified`
- `Sal.MRDTs.Instances.TreeMove.render_safe`
- `Sal.MRDTs.Instances.TreeMove.sequentialSound`
- `Sal.MRDTs.Instances.TreeMove.selfMove_rejected`
- `Sal.MRDTs.Instances.TreeMove.GC.undoRedo_algorithm_refines`
- `Sal.MRDTs.Instances.TreeMove.GC.collectPrefix_exact`
- `Sal.MRDTs.Instances.TreeMove.GC.appendFresh_exact`
- `Sal.MRDTs.Instances.TreeMove.GC.fullyStable_collectTrash_query`
- `Sal.MRDTs.Instances.TreeMove.GC.refines`
- `Sal.MRDTs.Instances.BoundedCounter.verified`
- `Sal.MRDTs.Instances.MVR.verified`
- `Sal.MRDTs.Instances.Queue.verified`
- `Sal.MRDTs.Instances.FlatCounters.counterVerified`
- `Sal.MRDTs.Instances.FlatCounters.iocVerified`
- `Sal.MRDTs.Instances.FlatCounters.pnVerified`
- `Sal.MRDTs.Instances.FlatGrowOnly.gosetVerified`
- `Sal.MRDTs.Instances.FlatGrowOnly.gomapVerified`

Run `./scripts/check-mrdt-refactor.sh` to check the manifest’s imported ledger,
forbidden-import and proof-hole scans, and all runtime conformance tests.
