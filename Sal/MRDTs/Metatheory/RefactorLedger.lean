import Sal.MRDTs.Framework.StateGC
import Sal.MRDTs.Instances.GSet
import Sal.MRDTs.Instances.BoundedCounter
import Sal.MRDTs.Instances.ProductionRGA
import Sal.MRDTs.GC.Refinement

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
#check Instances.BoundedCounter.BC
#check Instances.BoundedCounter.BC_coreVCs3
#check Instances.BoundedCounter.ra_linearizable
#check Instances.EmbedRGA.generation
#check Instances.EmbedRGA.convergence
#check Instances.SidedEmbedRGA.generation
#check Instances.SidedEmbedRGA.convergence
#check Instances.ProductionRGA.embed
#check Instances.ProductionRGA.sided
#check VerifiedMRDT.converges
#check VerifiedMRDT.convergesV
#check VerifiedMRDT.sequentially_correct

example (D : MRDTSig) : Configuration D := initConfig D

end Sal.MRDTs
