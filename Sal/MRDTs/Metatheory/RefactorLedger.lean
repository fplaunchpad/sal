import Sal.MRDTs.Framework.StateGC
import Sal.MRDTs.Instances.GSet
import Sal.MRDTs.Instances.MigratedCanaries
import Sal.MRDTs.GC.Refinement
import Sal.MRDTs.Instances.PeritextSidedStateGC
import Sal.MRDTs.Metatheory.LegacyBridge

/-! Build gate for the plain-signature reconstruction. -/

namespace Sal.MRDTs

#check MRDTSig
#check Configuration
#check initConfig
#check Step
#check VirtualLCAResolver
#check canonicalVirtualLCA
#check StoreInv
#check lca_events_of_storeInv
#check storeInv_reachable
#check storeInv_reachableV
#check mca_events_cover
#check ra_linearizable3_of_join
#check ra_linearizable3V_of_join
#check StepV
#check GenerationContract
#check MintCertifiedReach
#check MintCertifiedReachV
#check SafetyCertificate
#check SequentialRefinement
#check ConvergenceCertificate
#check VerifiedMRDT
#check StateGCCertificate
#check StateGCProtocol
#check StateGCProtocol.refines
#check HeadOnlyMergeCapability
#check GC.Certificate
#check GC.Certificate.ofMCAClosed
#check GC.root_absent_when_dropped
#check GC.execution_refines_noGC
#check GC.runtime_refines_core
#check GC.runtime_refines_coreV

#check Instances.GSet.generation
#check Instances.GSet.sequential
#check Instances.GSet.safety
#check LegacyBridge.erase_step
#check LegacyBridge.lift_step
#check LegacyBridge.lift_stepV
#check Instances.Migrated.boundedCounter
#check Instances.Migrated.queue
#check Instances.Migrated.embedRGA
#check Instances.Migrated.sidedEmbedRGA
#check Instances.Migrated.peritextEmbedRGA
#check Instances.PeritextSided.stateGC
#check Instances.PeritextSided.verified
#check Instances.PeritextSided.production

example (D : MRDTSig) : Configuration D := initConfig D

end Sal.MRDTs
