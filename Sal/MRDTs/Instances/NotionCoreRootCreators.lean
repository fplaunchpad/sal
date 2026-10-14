import Sal.MRDTs.Instances.NotionCoreArchiveOrder
import Sal.MRDTs.Instances.NotionCoreCreatorNetwork

/-! Root-instance provenance distinguishes standalone create from the empty
own-title instance allocated by split. It is an archive property, not a state
or rendering assertion; honest client history must establish it separately. -/
namespace Sal.MRDTs.Instances.NotionCoreRootCreators
open NotionRunAllocation (Id Run Session)
open NotionCorePayload (BlockKey Payload Transaction reservation)
open NotionCorePayloadNetwork (State Entry)

/-- Split creates a block title, but never a new active root text instance. -/
def rootCreatedBlocks (tx : Transaction) : List BlockKey := match tx.payload with
  | .bootstrap _ => [.initial]
  | .create _ => [.issued tx.id]
  | _ => []

def selectedInstances : Payload → List BlockKey
  | .insert _ inst _ _ | .split _ inst _ => [inst]
  | _ => []

def RootProvenance (network : State) : Prop :=
  ∀ entry ∈ network.entries, ∀ inst ∈ selectedInstances entry.tx.payload,
    ∃ provider ∈ network.entries, reservation provider.tx ∈ entry.past ∧
      inst ∈ rootCreatedBlocks provider.tx

def KnownRoot (network : State) (session : Session) (inst : BlockKey) : Prop :=
  ∃ provider ∈ network.entries,
    reservation provider.tx ∈ (network.allocation.peers session).received ∧
      inst ∈ rootCreatedBlocks provider.tx

theorem initial_roots : RootProvenance NotionCorePayloadNetwork.initial := by
  simp [RootProvenance,NotionCorePayloadNetwork.initial]
theorem bootstrap_roots (atoms : List Nat) : RootProvenance (NotionCorePayloadNetwork.seeded atoms) := by
  simp [RootProvenance,NotionCorePayloadNetwork.seeded,NotionCorePayload.bootstrap,selectedInstances]
theorem exchange_roots (network : State) (target source : Session) (roots : RootProvenance network) :
    RootProvenance (NotionCorePayloadNetwork.exchange network target source) := roots
theorem gap_roots (network : State) (session : Session) (ticks : Nat) (roots : RootProvenance network) :
    RootProvenance (NotionCorePayloadNetwork.gap network session ticks) := roots

/-- Emit captures the actual issuer's whole received version as the new
entry's past. Knowledge is needed only for selected insert/split instances. -/
theorem emit_roots (network : State) (session : Session) (payload : Payload) (tx : Transaction)
    (roots : RootProvenance network) (samePayload : tx.payload = payload)
    (known : ∀ inst ∈ selectedInstances payload, KnownRoot network session inst) :
    RootProvenance (NotionCorePayloadNetwork.emit network session payload tx) := by
  intro entry member inst selected
  rcases List.mem_cons.mp member with rfl | old
  · obtain ⟨provider,present,received,created⟩ := known inst (samePayload ▸ selected)
    exact ⟨provider,List.mem_cons_of_mem _ present,received,created⟩
  · obtain ⟨provider,present,past,created⟩ := roots entry old inst selected
    exact ⟨provider,List.mem_cons_of_mem _ present,past,created⟩

theorem root_created_is_created (tx : Transaction) (inst : BlockKey)
    (root : inst ∈ rootCreatedBlocks tx) : inst ∈ NotionCoreCreatorNetwork.createdBlocks tx := by
  cases tx with
  | mk id payload => cases payload <;>
      simp_all [rootCreatedBlocks,NotionCoreCreatorNetwork.createdBlocks]

/-- Root knowledge in an archived version does not require a live peer
currently holding that version. Receipt order and duplicates are irrelevant. -/
def KnownRootVersion (network : State) (version : List Run) (inst : BlockKey) : Prop :=
  ∃ provider ∈ network.entries, reservation provider.tx ∈ version ∧
    inst ∈ rootCreatedBlocks provider.tx

/-- Closure of one common archive retains every selected active instance's
root creator, including versions synthesized by union or intersection. -/
theorem selected_root_known_version (network : State) (roots : RootProvenance network)
    (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (entry : Entry) (member : entry ∈ network.entries)
    (present : reservation entry.tx ∈ version)
    (inst : BlockKey) (selected : inst ∈ selectedInstances entry.tx.payload) :
    KnownRootVersion network version inst := by
  obtain ⟨provider,published,past,created⟩ := roots entry member inst selected
  have recordMember : entry.record ∈ (NotionCorePayloadNetwork.forget network).records :=
    List.mem_map.mpr ⟨entry,member,rfl⟩
  exact ⟨provider,published,closed entry.record recordMember present (reservation provider.tx) past,created⟩

/-- Canonical closure places the whole root-creator provider before use. -/
theorem replay_selected_root_provider_version (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (entry : Entry) (member : entry ∈ network.entries)
    (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      version = pre ++ reservation entry.tx :: suffix)
    (inst : BlockKey) (selected : inst ∈ selectedInstances entry.tx.payload) :
    ∃ provider ∈ network.entries, reservation provider.tx ∈ pre ∧
      inst ∈ rootCreatedBlocks provider.tx ∧
      (reservation provider.tx).last < entry.tx.id.counter := by
  obtain ⟨provider,present,past,created⟩ := roots entry member inst selected
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  have recordMember : entry.record ∈ (NotionCorePayloadNetwork.forget network).records :=
    List.mem_map.mpr ⟨entry,member,rfl⟩
  have earlier := NotionCoreIssuance.past_in_prefix issued recordMember pre suffix
    (position ▸ NotionCoreIssuance.replay_closed issued _ closed)
    (position ▸ NotionCoreIssuance.replay_ordered issued _) (reservation provider.tx) past
  exact ⟨provider,present,earlier,created,
    (NotionCoreIssuance.record_provenance issued entry.record recordMember).2.1 _ past⟩

/-- Canonical closure places the whole root-creator provider before use. -/
theorem replay_selected_root_provider (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (peer : Session) (entry : Entry) (member : entry ∈ network.entries)
    (pre suffix : List Run)
    (position : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      (network.allocation.peers peer).received = pre ++ reservation entry.tx :: suffix)
    (inst : BlockKey) (selected : inst ∈ selectedInstances entry.tx.payload) :
    ∃ provider ∈ network.entries, reservation provider.tx ∈ pre ∧
      inst ∈ rootCreatedBlocks provider.tx ∧
      (reservation provider.tx).last < entry.tx.id.counter := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact replay_selected_root_provider_version network reachable roots
    (network.allocation.peers peer).received (NotionCoreIssuance.peers_closed issued peer)
    entry member pre suffix position inst selected

/-- Actual transaction membership, not merely reservation containment, names
an earlier root creator in the canonical chronological prefix. -/
theorem canonical_selected_root_provider_version (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (inst : BlockKey) (selected : inst ∈ selectedInstances tx.payload) :
    ∃ provider ∈ pre, inst ∈ rootCreatedBlocks provider ∧
      (reservation provider).last < tx.id.counter := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_right pre (by simp))
  have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
      version =
      pre.map reservation ++ reservation entry.tx :: suffix.map reservation := by
    rw [← NotionCoreReconstruction.transactionsFor_runs,position,List.map_append,List.map_cons,same]
  obtain ⟨provider,published,earlier,created,clock⟩ := replay_selected_root_provider_version network reachable roots
    version closed entry member (pre.map reservation) (suffix.map reservation) runPosition inst (same ▸ selected)
  obtain ⟨previous,inPre,runEq⟩ := List.mem_map.mp earlier
  obtain ⟨archived,archiveMember,previousEq,_⟩ := NotionCoreReconstruction.transactionsFor_received network version previous
    (position ▸ List.mem_append_left _ inPre)
  have keys := NotionCoreArchiveOrder.archive_keys_unique network
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  have providerMember : provider.tx ∈ network.entries.map Entry.tx :=
    List.mem_map.mpr ⟨provider,published,rfl⟩
  have previousMember : previous ∈ network.entries.map Entry.tx :=
    List.mem_map.mpr ⟨archived,archiveMember,previousEq⟩
  have txEq : previous = provider.tx := List.inj_on_of_nodup_map keys previousMember providerMember
    (congrArg Run.first runEq)
  exact ⟨previous,inPre,txEq ▸ created,by simpa only [txEq,same] using clock⟩

/-- Actual transaction membership, not merely reservation containment, names
an earlier root creator in the canonical chronological prefix. -/
theorem canonical_selected_root_provider (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (roots : RootProvenance network)
    (peer : Session) (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (inst : BlockKey) (selected : inst ∈ selectedInstances tx.payload) :
    ∃ provider ∈ pre, inst ∈ rootCreatedBlocks provider ∧
      (reservation provider).last < tx.id.counter := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_selected_root_provider_version network reachable roots
    (network.allocation.peers peer).received (NotionCoreIssuance.peers_closed issued peer)
    pre suffix tx position inst selected

/-- The source's sole bootstrap is supplied at fixed A@1; ordinary prepare
cannot emit another bootstrap. It need not be first in canonical replay. -/
theorem archived_bootstrap (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (entry : Entry) (member : entry ∈ network.entries) (atoms : List Nat)
    (payload : entry.tx.payload = .bootstrap atoms) : entry.tx = NotionCorePayload.bootstrap atoms := by
  induction reachable generalizing entry atoms with
  | init => simp [NotionCorePayloadNetwork.initial] at member
  | bootstrap initialAtoms =>
    simp only [NotionCorePayloadNetwork.seeded,List.mem_singleton] at member
    subst entry
    simp only [NotionCorePayload.bootstrap] at payload
    have same : initialAtoms = atoms := Payload.bootstrap.inj payload
    simp [NotionCorePayload.bootstrap,same]
  | exchange target source _ ih => exact ih entry member atoms payload
  | gap session ticks _ ih => exact ih entry member atoms payload
  | @emit old session request tx prior prepared known ih =>
    rcases List.mem_cons.mp member with rfl | older
    · have same := NotionCorePayloadNetwork.prepared_payload prepared
      have impossible : request = .bootstrap atoms := same.symm.trans payload
      rw [impossible] at prepared
      simp [NotionCorePayload.prepare] at prepared
    · exact ih entry older atoms payload

private theorem initial_creator_bootstrap (tx : Transaction)
    (created : BlockKey.initial ∈ NotionCoreCreatorNetwork.createdBlocks tx) :
    ∃ atoms, tx.payload = .bootstrap atoms := by
  cases tx with
  | mk id payload =>
      cases payload <;> simp [NotionCoreCreatorNetwork.createdBlocks] at created
      exact ⟨_,rfl⟩

/-- An earlier ordinary create may precede bootstrap. What is excluded is an
earlier creator of the initial instance, not a nonempty chronological prefix. -/
theorem canonical_no_initial_creator_version (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    ∀ provider ∈ network.entries, reservation provider.tx ∈ pre.map reservation →
      BlockKey.initial ∉ NotionCoreCreatorNetwork.createdBlocks provider.tx := by
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version tx
    (position ▸ List.mem_append_right pre (by simp))
  have archiveReach := NotionCoreCreatorNetwork.payload_reachable reachable
  have bootstrapEq := archived_bootstrap network archiveReach entry member atoms (same ▸ payload)
  have txEq : tx = NotionCorePayload.bootstrap atoms := same.symm.trans bootstrapEq
  have ordered := position ▸ NotionCoreReconstruction.transactionsFor_ordered network archiveReach version
  intro provider published earlier created
  obtain ⟨oldAtoms,oldPayload⟩ := initial_creator_bootstrap provider.tx created
  have providerEq := archived_bootstrap network archiveReach provider published oldAtoms oldPayload
  obtain ⟨previous,inPre,runEq⟩ := List.mem_map.mp earlier
  have previousId : previous.id = tx.id := by
    have firstEq := congrArg Run.first runEq
    simpa [reservation,providerEq,txEq,NotionCorePayload.bootstrap] using firstEq
  have before := (List.pairwise_append.mp ordered).2.2 previous inPre tx (by simp)
  rw [previousId] at before
  exact NotionCoreSourceInvariant.before_irrefl tx.id before

/-- An earlier ordinary create may precede bootstrap. What is excluded is an
earlier creator of the initial instance, not a nonempty chronological prefix. -/
theorem canonical_no_initial_creator (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    ∀ provider ∈ network.entries, reservation provider.tx ∈ pre.map reservation →
      BlockKey.initial ∉ NotionCoreCreatorNetwork.createdBlocks provider.tx := by
  exact canonical_no_initial_creator_version network reachable (network.allocation.peers peer).received
    pre suffix tx position atoms payload

/-- Creator provenance excludes even a required use of the initial instance
before bootstrap; a standalone lower-key create can still occur there. -/
theorem canonical_no_initial_use_version (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    ∀ previous ∈ pre, BlockKey.initial ∉ NotionCoreMachineCreators.usedBlocks previous := by
  have excluded := canonical_no_initial_creator_version network reachable version pre suffix tx position atoms payload
  intro previous present used
  obtain ⟨entry,member,same,_⟩ := NotionCoreReconstruction.transactionsFor_received network version previous
    (position ▸ List.mem_append_left _ present)
  rcases List.mem_append.mp used with created | required
  · exact excluded entry member (List.mem_map.mpr ⟨previous,present,by rw [same]⟩) (same ▸ created)
  · obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp present
    have runPosition : NotionCoreIssuance.replay (NotionCorePayloadNetwork.forget network)
        version =
        before.map reservation ++ reservation entry.tx :: (after ++ tx :: suffix).map reservation := by
      rw [← NotionCoreReconstruction.transactionsFor_runs,position,shape,List.append_assoc,
        List.cons_append,List.map_append,List.map_cons,same]
    obtain ⟨provider,published,earlier,born,_⟩ :=
      NotionCoreCreatorNetwork.replay_creator_provider_version reachable version closed member
        (before.map reservation) ((after ++ tx :: suffix).map reservation) runPosition (same ▸ required)
    have inPre : reservation provider.tx ∈ pre.map reservation := by
      rw [shape,List.map_append,List.map_cons]
      exact List.mem_append_left _ earlier
    exact excluded provider published inPre born

/-- Creator provenance excludes even a required use of the initial instance
before bootstrap; a standalone lower-key create can still occur there. -/
theorem canonical_no_initial_use (network : State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (peer : Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (atoms : List Nat) (payload : tx.payload = .bootstrap atoms) :
    ∀ previous ∈ pre, BlockKey.initial ∉ NotionCoreMachineCreators.usedBlocks previous := by
  have issued := NotionCorePayloadNetwork.forget_reachable
    (NotionCoreCreatorNetwork.payload_reachable reachable)
  exact canonical_no_initial_use_version network reachable (network.allocation.peers peer).received
    (NotionCoreIssuance.peers_closed issued peer) pre suffix tx position atoms payload

#print axioms canonical_no_initial_creator_version
#print axioms canonical_no_initial_use_version
#print axioms canonical_selected_root_provider_version
#print axioms selected_root_known_version
#print axioms replay_selected_root_provider_version
#print axioms replay_selected_root_provider

#print axioms canonical_no_initial_use
#print axioms archived_bootstrap
#print axioms canonical_no_initial_creator
/-- PASS+FAIL: standalone creation is a root provider, split creation is not. -/
theorem root_kind_control :
    rootCreatedBlocks ⟨⟨3,[65]⟩,.create (some .initial)⟩ = [.issued ⟨3,[65]⟩] ∧
    rootCreatedBlocks ⟨⟨3,[65]⟩,.split .initial .initial .start⟩ ≠ [.issued ⟨3,[65]⟩] ∧
    selectedInstances (.erase .initial .initial [⟨1,[65]⟩]) = [] := by decide +kernel

/-- PASS+FAIL: an archive entry alone does not put its root into an empty
version; a complete bootstrap reservation does, independently of a live peer. -/
theorem root_version_control :
    KnownRootVersion (NotionCorePayloadNetwork.seeded [97])
      [reservation (NotionCorePayload.bootstrap [97])] .initial ∧
    ¬ KnownRootVersion (NotionCorePayloadNetwork.seeded [97]) [] .initial := by
  simp [KnownRootVersion,NotionCorePayloadNetwork.seeded,rootCreatedBlocks,NotionCorePayload.bootstrap]

#print axioms emit_roots
#print axioms canonical_selected_root_provider
end Sal.MRDTs.Instances.NotionCoreRootCreators
