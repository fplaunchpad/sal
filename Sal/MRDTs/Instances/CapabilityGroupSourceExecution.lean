import Sal.MRDTs.Instances.CapabilityGroupSourceProtocol
import Sal.MRDTs.Instances.CapabilityGroupProtocol

/-! Actual certified version-DAG executions generate source-protocol logs.
The theorem covers every allocated version, including ordinary and virtual
merges. Source-protocol completeness reconstructs a finite issuance/reconcile
derivation from the source invariants derived by the actual framework proof.
No supplied source run or final-state invariant appears as a hypothesis.
-/
namespace Sal.MRDTs.Instances.CapabilityGroup.Protocol
open Sal.MRDTs Sal.MRDTs.Foundation

/-- Every registered state of an actual honestly certified virtual-merge
execution is reachable in the source issue/reconcile protocol. -/
theorem registered_source_reachable {owner : Actor} {principal : Replica → Actor}
    {ownerReplica : Replica} (C : Configuration (D owner))
    (reach : MintCertifiedReachV (D owner) (canonicalVirtualMergeBase (D owner))
      (issuance owner principal ownerReplica) C)
    (v : Version) (state : State) (E : Set (Op Event))
    (registered : C.ver v = some (state, E)) : SourceReach owner state := by
  have source := registered_source C reach v state E registered
  exact SourceReach.of_valid source.1 source.2.1

/-- Ordinary certified executions inherit the correspondence through the
framework's ordinary-to-virtual embedding. -/
theorem registered_source_reachable_ordinary {owner : Actor} {principal : Replica → Actor}
    {ownerReplica : Replica} (C : Configuration (D owner))
    (reach : MintCertifiedReach (D owner) (issuance owner principal ownerReplica) C)
    (v : Version) (state : State) (E : Set (Op Event))
    (registered : C.ver v = some (state, E)) : SourceReach owner state :=
  registered_source_reachable C reach.toV v state E registered

/-- In particular, every active replica's actual state has a source-protocol
derivation. Replica allocation and lookup remain concrete framework facts. -/
theorem head_source_reachable {owner : Actor} {principal : Replica → Actor}
    {ownerReplica : Replica} (C : Configuration (D owner))
    (reach : MintCertifiedReachV (D owner) (canonicalVirtualMergeBase (D owner))
      (issuance owner principal ownerReplica) C)
    (r : Replica) (state : State) (head : C.headState r = some state) :
    SourceReach owner state := by
  unfold Configuration.headState headStateFrom at head
  cases hr : C.head r with
  | none => simp [hr] at head
  | some v =>
    cases hv : C.ver v with
    | none => simp [hr, hv] at head
    | some pair =>
      obtain ⟨stored, E⟩ := pair
      have same : stored = state := by simpa [hr, hv] using head
      subst state
      exact registered_source_reachable C reach v stored E hv

#print axioms registered_source_reachable
#print axioms registered_source_reachable_ordinary
#print axioms head_source_reachable

end Sal.MRDTs.Instances.CapabilityGroup.Protocol
