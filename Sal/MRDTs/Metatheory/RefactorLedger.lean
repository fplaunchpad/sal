import Sal.MRDTs.Framework.StateGC
import Sal.MRDTs.Instances.GSet
import Sal.MRDTs.Metatheory.LegacyBridge

/-! Build gate for the plain-signature reconstruction. -/

namespace Sal.MRDTs

#check MRDTSig
#check Configuration
#check initConfig
#check Step
#check GenerationContract
#check MintCertifiedReach
#check SafetyCertificate
#check SequentialRefinement
#check ConvergenceCertificate
#check VerifiedMRDT
#check StateGCCertificate
#check HeadOnlyMergeCapability

#check Instances.GSet.generation
#check Instances.GSet.sequential
#check Instances.GSet.safety
#check LegacyBridge.erase_step
#check LegacyBridge.lift_step

example (D : MRDTSig) : Configuration D := initConfig D

end Sal.MRDTs
