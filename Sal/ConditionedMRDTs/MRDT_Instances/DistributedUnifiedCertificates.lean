import Sal.ConditionedMRDTs.Metatheory.Distributed_GC_Refinement
import Sal.ConditionedMRDTs.MRDT_Instances.ProductionGenerationContracts
import Sal.ConditionedMRDTs.MRDT_Instances.FlatUnifiedCertificates
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_WithTombstones.RGA_Intent
import Sal.ConditionedMRDTs.MRDT_Instances.MVR.MVR_Unified
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_WithTombstones.Peritext_Intent

/-!
# Distributed correctness certificates for production RDTs

Each theorem below is an instantiation of one generic result. No datatype proof
is repeated here. Peritext has both current positive kernels until the paper
selects one authoritative presentation.
-/

namespace Sal.ConditionedMRDTs

theorem boundedCounterDistributed :
    DistributedCorrectness boundedCounterUnified :=
  boundedCounterUnified.distributedCorrectness

theorem queueDistributed : DistributedCorrectness queueUnified :=
  queueUnified.distributedCorrectness

theorem tombstoneRGADistributed : DistributedCorrectness rgaUnified :=
  rgaUnified.distributedCorrectness

theorem mvrDistributed : DistributedCorrectness mvrUnified :=
  mvrUnified.distributedCorrectness

theorem orsetDistributed : DistributedCorrectness orsetUnified :=
  orsetUnified.distributedCorrectness

theorem peritextTombstoneDistributed : DistributedCorrectness ptUnified :=
  ptUnified.distributedCorrectness

theorem peritextEmbedDistributed
    (Γ : Sal.EmbedRGA.OrderedPrefixCode) :
    DistributedCorrectness (peritextEmbedUnified Γ) :=
  (peritextEmbedUnified Γ).distributedCorrectness

end Sal.ConditionedMRDTs

#print axioms Sal.ConditionedMRDTs.peritextTombstoneDistributed
#print axioms Sal.ConditionedMRDTs.peritextEmbedDistributed
