import Sal.MRDTs.Instances.NotionCoreMachineNetwork
import Sal.MRDTs.Instances.NotionCoreMachineClientShape
import Sal.MRDTs.Instances.NotionCoreMachineShape
import Sal.MRDTs.Instances.NotionCoreRootCreators
import Sal.MRDTs.Instances.NotionCoreMachineRootReplay

/-! Honest positional preparation supplies root-instance provenance. The
archive property records actual creator kinds and received transactions,
not desired replay results or selected output intervals. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineHonestReplay
open NotionCorePayload (BlockKey Payload Transaction reservation)
open NotionCoreMachine
open NotionCoreMachineShape
open NotionCoreMachineNetwork (Request prepareRequest)
open NotionCoreMachineClient
open NotionCoreRootCreators

private theorem active_known_root (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (state : State)
    (roots : ∀ name, ActiveInstance state name →
      ∃ tx ∈ NotionCoreReconstruction.transactions network session,
        ∃ key ∈ rootCreatedBlocks tx, blockName key = name)
    (inst : BlockKey) (active : ActiveInstance state (blockName inst)) : KnownRoot network session inst := by
  obtain ⟨tx,member,key,born,equal⟩ := roots (blockName inst) active
  have same : key = inst := blockName_injective equal
  obtain ⟨entry,published,transactionEq,received⟩ :=
    NotionCoreReconstruction.transactions_received network session tx member
  exact ⟨entry,published,transactionEq ▸ received,transactionEq ▸ (same ▸ born)⟩

/-- Root knowledge is derived from actual local materialization and the root
classification of that reconstructed version. No selection certificate is
supplied by the client or placed in the executable issue function. -/
theorem prepared_root_knowledge (network : NotionCorePayloadNetwork.State)
    (session : NotionRunAllocation.Session) (state : State)
    (accepted : NotionCoreReconstruction.reconstruct network session = some state)
    (shape : ShapeInvariant state)
    (roots : ∀ name, ActiveInstance state name →
      ∃ tx ∈ NotionCoreReconstruction.transactions network session,
        ∃ key ∈ rootCreatedBlocks tx, blockName key = name)
    (request : Request) (payload : Payload)
    (prepared : prepareRequest state request = some payload) :
    ∀ inst ∈ selectedInstances payload, KnownRoot network session inst := by
  cases request with
  | create afterBlock =>
    cases afterBlock with
    | none =>
      have equal : payload = .create none := by simpa [prepareRequest,prepareCreate] using prepared.symm
      simp [equal,selectedInstances]
    | some block =>
      simp only [prepareRequest,prepareCreate] at prepared
      split at prepared
      · have equal : payload = .create (some block) := Option.some.inj prepared.symm
        simp [equal,selectedInstances]
      · contradiction
  | erase block start stop =>
    obtain ⟨inst,ids,rfl⟩ := NotionCoreMachineDelete.selectErase_kind state block start stop payload prepared
    simp [selectedInstances]
  | split block index =>
    cases selected : locateAddress state block index with
    | none => simp [prepareRequest,prepareSplit,selected] at prepared
    | some address =>
      cases decoded : decodeAddress address with
      | none => simp [prepareRequest,prepareSplit,selected,decoded] at prepared
      | some pair =>
        obtain ⟨inst,origin⟩ := pair
        have equal : Payload.split block inst origin = payload := by
          simpa [prepareRequest,prepareSplit,selected,decoded] using prepared
        subst payload
        have active := NotionCoreMachineClientShape.prepared_split_active _ state accepted
          shape.1 shape.2.2 block inst index origin prepared
        intro key member
        have same : key = inst := by simpa [selectedInstances] using member
        exact same ▸ active_known_root network session state roots inst active
  | insert block index atoms =>
    cases skipped : atoms.isEmpty with
    | true => simp [prepareRequest,prepareInsert,skipped] at prepared
    | false =>
      cases selected : locateAddress state block index with
      | none => simp [prepareRequest,prepareInsert,skipped,selected] at prepared
      | some address =>
        cases decoded : decodeAddress address with
        | none => simp [prepareRequest,prepareInsert,skipped,selected,decoded] at prepared
        | some pair =>
          obtain ⟨inst,origin⟩ := pair
          have equal : Payload.insert block inst origin atoms = payload := by
            simpa [prepareRequest,prepareInsert,skipped,selected,decoded] using prepared
          subst payload
          have active := NotionCoreMachineClientShape.prepared_insert_active _ state accepted
            shape.1 shape.2.2 block inst index atoms origin prepared
          intro key member
          have same : key = inst := by simpa [selectedInstances] using member
          exact same ▸ active_known_root network session state roots inst active

/-- The real request transition preserves root provenance. Its reconstruction
invariant follows from the old archive property; local preparation supplies
the new entry's root-provider knowledge. -/
theorem issue_root_provenance (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (session : NotionRunAllocation.Session) (request : Request)
    (next : NotionCorePayloadNetwork.State)
    (issued : NotionCoreMachineNetwork.issue network session request = some next) : RootProvenance next := by
  have noSkip : request.earlyNoop = false := by
    cases skipped : request.earlyNoop <;> simp_all [NotionCoreMachineNetwork.issue]
  cases current : NotionCoreReconstruction.reconstruct network session with
  | none => simp [NotionCoreMachineNetwork.issue,noSkip,current] at issued
  | some document =>
    cases selected : prepareRequest document request with
    | none => simp [NotionCoreMachineNetwork.issue,noSkip,current,selected] at issued
    | some payload =>
      cases reserved : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) session payload with
      | none => simp [NotionCoreMachineNetwork.issue,noSkip,current,selected,reserved] at issued
      | some tx =>
        have equal : NotionCorePayloadNetwork.emit network session payload tx = next := by
          simpa [NotionCoreMachineNetwork.issue,noSkip,current,selected,reserved] using issued
        rw [← equal]
        obtain ⟨checked,accepted,_,shape,rootActive⟩ :=
          NotionCoreMachineRootReplay.reconstruct_invariant network reachable roots session
        have same : checked = document := Option.some.inj (accepted.symm.trans current)
        subst checked
        apply emit_roots network session payload tx roots (NotionCorePayloadNetwork.prepared_payload reserved)
        exact prepared_root_knowledge network session document current shape
          (fun name active => (rootActive name).mp active) request payload selected

/-- Root provenance is a theorem of actual positional-request history, not an
extra admission guard. Exchange and clock gaps preserve the archive property. -/
theorem honest_root_provenance (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) : RootProvenance network := by
  induction reachable with
  | init => exact initial_roots
  | bootstrap atoms => exact bootstrap_roots atoms
  | exchange target source prior ih => exact exchange_roots _ target source ih
  | gap session ticks prior ih => exact gap_roots _ session ticks ih
  | request session request prior issued ih =>
      exact issue_root_provenance _ (NotionCoreMachineNetwork.creator_reachable prior) ih
        session request _ issued

/-- Honest positional-request archives execute every closed version and
canonical prefix, including versions not registered as any peer's receipt. -/
theorem honest_prefix_reconstruct_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix) :
    ∃ state, replay {} pre = some state ∧ NotionCoreMachinePartition.Partitioned state ∧
      ShapeInvariant state ∧ NotionCoreMachineRootReplay.RootActive pre state :=
  NotionCoreMachineRootReplay.canonical_prefix_reconstruct_version network
    (NotionCoreMachineNetwork.creator_reachable reachable) (honest_root_provenance network reachable)
    version closed pre suffix position

/-- Complete explicit-version replay follows from the same archive's honest
issuance and closure, without a caller's replay-acceptance premise. -/
theorem honest_reconstruct_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) :
    ∃ state, replay {} (NotionCoreReconstruction.transactionsFor network version) = some state ∧
      NotionCoreMachinePartition.Partitioned state ∧ ShapeInvariant state ∧
      NotionCoreMachineRootReplay.RootActive (NotionCoreReconstruction.transactionsFor network version) state :=
  honest_prefix_reconstruct_version network reachable version closed _ [] (by simp)

#print axioms honest_prefix_reconstruct_version
#print axioms honest_reconstruct_version
/-- Existing peer-prefix API specializes the archive-wide theorem. -/
theorem honest_prefix_reconstruct (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ suffix) :
    ∃ state, replay {} pre = some state ∧ NotionCoreMachinePartition.Partitioned state ∧
      ShapeInvariant state ∧ NotionCoreMachineRootReplay.RootActive pre state :=
  honest_prefix_reconstruct_version network reachable _
    (NotionCoreIssuance.peers_closed
      (NotionCorePayloadNetwork.forget_reachable
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))) peer)
    pre suffix position

/-- Complete peer reconstruction follows from the shared closed-version
induction. This remains execution/structure, not an RA theorem. -/
theorem honest_reconstruct (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session) :
    ∃ state, NotionCoreReconstruction.reconstruct network peer = some state ∧
      NotionCoreMachinePartition.Partitioned state ∧ ShapeInvariant state ∧
      NotionCoreMachineRootReplay.RootActive (NotionCoreReconstruction.transactions network peer) state :=
  honest_prefix_reconstruct network reachable peer _ [] (by simp)

#print axioms honest_root_provenance
#print axioms honest_prefix_reconstruct
#print axioms honest_reconstruct
#print axioms prepared_root_knowledge
end Sal.MRDTs.Instances.NotionCoreMachineHonestReplay
