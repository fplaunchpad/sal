import Sal.MRDTs.Instances.CapabilityGroupCertificate
import Sal.MRDTs.Instances.CapabilityGroupProtocolNonempty

/-! Nonempty issuance controls for the actual framework issuance predicate.
The expectations distinguish authenticated subjects, framework replica IDs,
named-grant revocation and the designated single owner issuer. -/
namespace Sal.MRDTs.Instances.CapabilityGroup.CertificateSPOT
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1

private def principal (replica : Replica) : Actor := if replica = 0 then 0 else 1
private def twoOwnerPrincipal (replica : Replica) : Actor := if replica = 7 then 0 else principal replica
private abbrev grant : Event := ⟨1,0,∅,.grant 1⟩
private abbrev use : Event := ⟨2,1,{1},.assign 1 10⟩
private abbrev revoke : Event := ⟨3,0,{1},.revoke 1⟩
private abbrev freshGrant : Event := ⟨4,0,{1,3},.grant 1⟩
private abbrev freshUse : Event := ⟨5,1,{1,3,4},.assign 4 20⟩
private abbrev staleUse : Event := ⟨4,1,{1,3},.assign 1 20⟩

/-- Grant/use/revoke are issuable with real nonempty causal contexts. A subject
cannot claim the owner's authenticated identity on the recipient replica. -/
theorem grant_use_controls :
    (Protocol.issuance 0 principal 0).CanIssue (1,0,grant) ∅ ∧
    (Protocol.issuance 0 principal 0).CanIssue (2,1,use) {grant} ∧
    (Protocol.issuance 0 principal 0).CanIssue (3,0,revoke) {grant} ∧
    ¬ (Protocol.issuance 0 principal 0).CanIssue (1,1,grant) ∅ := by
  unfold Protocol.issuance
  decide

/-- Revoking one grant blocks its later use; a fresh named grant permits a
new use. Recipient identity may be authenticated on several replica IDs. -/
theorem regrant_and_recipient_devices_controls :
    (Protocol.issuance 0 principal 0).CanIssue (4,0,freshGrant) {grant,revoke} ∧
    (Protocol.issuance 0 principal 0).CanIssue (5,1,freshUse) {grant,revoke,freshGrant} ∧
    (Protocol.issuance 0 principal 0).CanIssue (5,2,freshUse) {grant,revoke,freshGrant} ∧
    ¬ (Protocol.issuance 0 principal 0).CanIssue (4,1,staleUse) {grant,revoke} ∧
    ¬ (Protocol.issuance 0 principal 0).CanIssue (6,1,freshUse) {grant,revoke,freshGrant} := by
  unfold Protocol.issuance
  decide

/-- Authenticating the owner at another replica does not authorize that device
to issue owner operations; the principal map alone cannot bypass the owner chain. -/
theorem wrong_owner_device_controls :
    (Protocol.issuance 0 twoOwnerPrincipal 0).CanIssue (1,0,grant) ∅ ∧
    ¬ (Protocol.issuance 0 twoOwnerPrincipal 0).CanIssue (2,7,⟨2,0,∅,.grant 1⟩) ∅ ∧
    ¬ (Protocol.issuance 0 twoOwnerPrincipal 0).CanIssue (3,7,revoke) {grant} := by
  unfold Protocol.issuance
  decide

/-- Apply both public criterion interfaces to an actual nonempty ordinary
execution and its certified virtual-semantics embedding. The query excludes
an empty-only or universally rejecting interpretation of the certificate. -/
theorem actual_nonempty_public_control :
    ProjectedSpecificationRALinearizable (Protocol.D 0) (commutingPolicy Event)
      Certificate.project (CapabilityGroupSpec.spec 0) ProtocolNonempty.config ∧
    EventSpecificationRALinearizable (Protocol.D 0) (commutingPolicy Event)
      (Certificate.eventSpec 0) ProtocolNonempty.config ∧
    (Protocol.D 0).query ProtocolNonempty.log () = {10} ∧
    (Protocol.D 0).query ProtocolNonempty.log () ≠ ∅ := by
  exact ⟨Certificate.projectedRA ProtocolNonempty.reach,
    Certificate.eventRAV ProtocolNonempty.reachV,ProtocolNonempty.query_control⟩

#print axioms actual_nonempty_public_control

end Sal.MRDTs.Instances.CapabilityGroup.CertificateSPOT
