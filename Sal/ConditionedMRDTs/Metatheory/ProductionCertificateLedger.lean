import Sal.ConditionedMRDTs.MRDT_Instances.VerifiedCertificates
import Sal.ConditionedMRDTs.Metatheory.RefactorLedger

/-! Mechanically checked ledger for production `VerifiedMRDT` packages.

It also imports `RefactorLedger`; Shesha's formerly colliding update callback
is now named `sheshaUpdate`, so the production and refactor surfaces coexist in
one Lean environment.
-/

open Sal.ConditionedMRDTs

#check SequentialSpec.run_prod
#check SequentialRefinement.toHistory
#check HistorySequentialRefinement.prod
#check embedVerified
#check embedVerifiedRuntime
#check embedVerifiedRuntime_multiEpoch
#check sidedVerified
#check queueVerified
#check embedQueueVerified
#check VerifiedMRDT.ra_linearizable
#check VerifiedMRDT.sequential
#check VerifiedMRDT.prod
#check VerifiedRuntimeMRDT.compact_continuation
