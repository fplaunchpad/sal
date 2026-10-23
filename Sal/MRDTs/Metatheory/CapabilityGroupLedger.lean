import Sal.MRDTs.Instances.CapabilityGroupCertificateSPOT
import Sal.MRDTs.Instances.CapabilityGroupSourceExecution
import Sal.MRDTs.Paper1.CapabilityGroupBridge

/-! Checked owner-ordered capability protocol. This research entry is separate
from the uniform runtime package registry. It retains the five VCs, actual
issuance-certified histories, independent ACL bridge and nonempty execution.
The concurrent-owner counterexample remains a separately checked boundary.
-/
namespace Sal.MRDTs.Research.CapabilityGroupLedger
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Instances.CapabilityGroup

structure CheckedProtocolEntry where
  conditions : ∀ (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica),
    ScopedVCConditions (commutingPolicy Event) (Certificate.eventSpec owner)
      (Protocol.issuance owner principal ownerReplica)
  source : ∀ (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica)
    (C : Configuration (Protocol.D owner)),
    MintCertifiedReachV (Protocol.D owner) (canonicalVirtualMergeBase (Protocol.D owner))
      (Protocol.issuance owner principal ownerReplica) C →
    ∀ v state E, C.ver v = some (state,E) → SourceReach owner state
  nonempty : MintCertifiedReachV (Protocol.D 0) (canonicalVirtualMergeBase (Protocol.D 0))
    (Protocol.issuance 0 id 0) ProtocolNonempty.config
  observation : (Protocol.D 0).query ProtocolNonempty.log () = {10} ∧
    (Protocol.D 0).query ProtocolNonempty.log () ≠ ∅

noncomputable def entry : CheckedProtocolEntry where
  conditions := Certificate.conditions
  source := fun _ _ _ C reach v state E registered =>
    Protocol.registered_source_reachable C reach v state E registered
  nonempty := ProtocolNonempty.reachV
  observation := ProtocolNonempty.query_control

#check Protocol.fiveVCs
#check Protocol.registered_source
#check Certificate.projectedRAV
#check Certificate.executionsV
#check CertificateSPOT.actual_nonempty_public_control
#check CapabilityGroupBridge.criterion_boundary
#print axioms entry
#print axioms Certificate.projectedRAV
#print axioms Certificate.executionsV
end Sal.MRDTs.Research.CapabilityGroupLedger
