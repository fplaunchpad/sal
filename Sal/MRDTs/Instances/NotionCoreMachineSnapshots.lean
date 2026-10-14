import Sal.MRDTs.Instances.NotionCoreMachineNetwork

/-! Immutable saved versions can be represented by receipt-only peers. Copying
into an empty peer uses the existing honest exchange operation, preserves the
archive and other peers, and produces the identical canonical replay. This is
a building block for the Sal simulation, not that simulation itself. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineSnapshots
open NotionRunAllocation (Session Run)
open NotionCorePayloadNetwork (State exchange)
open NotionCoreReconstruction

theorem exchange_received (network : State) (target source peer : Session) (run : Run) :
    run ∈ ((exchange network target source).allocation.peers peer).received ↔
      run ∈ (network.allocation.peers peer).received ∨
        peer = target ∧ run ∈ (network.allocation.peers source).received :=
  NotionCoreIssuance.import_received network.allocation target _ peer run

theorem exchange_other_peer (network : State) (target source peer : Session)
    (different : peer ≠ target) :
    (exchange network target source).allocation.peers peer = network.allocation.peers peer := by
  have untouched : ∀ runs : List Run,
      (NotionCoreIssuance.importRuns network.allocation target runs).peers peer =
        network.allocation.peers peer := by
    intro runs
    generalize network.allocation = allocation
    induction runs generalizing allocation with
    | nil => rfl
    | cons run rest ih =>
      rw [NotionCoreIssuance.importRuns, ih]
      simp [NotionRunAllocation.deliver, different]
  exact untouched _

theorem exchange_archive (network : State) (target source : Session) :
    (exchange network target source).entries = network.entries := rfl

theorem exchange_transactions (network : State) (target source peer : Session) :
    transactions (exchange network target source) peer =
      transactionsFor network ((exchange network target source).allocation.peers peer).received := rfl

theorem snapshot_transactions (network : State) (target source : Session)
    (empty : (network.allocation.peers target).received = []) :
    transactions (exchange network target source) target = transactions network source := by
  rw [exchange_transactions, transactions_eq_for]
  apply transactionsFor_ext
  intro run
  simp [exchange_received, empty]

theorem snapshot_reconstruct (network : State) (target source : Session)
    (empty : (network.allocation.peers target).received = []) :
    reconstruct (exchange network target source) target = reconstruct network source := by
  simp only [reconstruct, snapshot_transactions network target source empty]

theorem restore_transactions (network : State) (target snapshot : Session) :
    transactions (exchange network target snapshot) target =
      transactionsFor network ((network.allocation.peers target).received ++
        (network.allocation.peers snapshot).received) := by
  rw [exchange_transactions]
  apply transactionsFor_ext
  intro run
  simp [exchange_received]

theorem exchange_reachable {network : State}
    (honest : NotionCoreMachineNetwork.Reach network) (target source : Session) :
    NotionCoreMachineNetwork.Reach (exchange network target source) :=
  .exchange target source honest

/-- A finite execution touches only finitely many peer identities. This makes
fresh receipt-only storage available without resetting an existing allocator. -/
theorem finite_peer_support {network : NotionRunAllocation.Network}
    (reachable : NotionRunAllocation.Reach network) :
    ∃ touched : List Session, ∀ peer, peer ∉ touched →
      network.peers peer = NotionRunAllocation.emptyPeer := by
  induction reachable with
  | init => exact ⟨[], fun _ _ => rfl⟩
  | delivery run target _ _ ih =>
    obtain ⟨touched, untouched⟩ := ih
    refine ⟨target :: touched, ?_⟩
    intro peer outside
    have different : peer ≠ target := fun same => outside (by simp [same])
    have old : peer ∉ touched := fun member => outside (by simp [member])
    simpa [NotionRunAllocation.deliver, different] using untouched peer old
  | gap ticks target _ ih =>
    obtain ⟨touched, untouched⟩ := ih
    refine ⟨target :: touched, ?_⟩
    intro peer outside
    have different : peer ≠ target := fun same => outside (by simp [same])
    have old : peer ∉ touched := fun member => outside (by simp [member])
    simpa [NotionRunAllocation.skip, different] using untouched peer old
  | issuance width target _ _ ih =>
    obtain ⟨touched, untouched⟩ := ih
    refine ⟨target :: touched, ?_⟩
    intro peer outside
    have different : peer ≠ target := fun same => outside (by simp [same])
    have old : peer ∉ touched := fun member => outside (by simp [member])
    simpa [NotionRunAllocation.issue, different] using untouched peer old

/-- An infinite namespace of code-unit-valid receipt-only peers. A caller can
reserve the leading tag separately from the namespace used for real issuers. -/
def ghostSession (tag index : Nat) : Session := tag :: List.replicate index 0

theorem fresh_ghost {network : NotionRunAllocation.Network}
    (reachable : NotionRunAllocation.Reach network) (tag : Nat)
    (avoid : List Session) :
    ∃ index, ghostSession tag index ∉ avoid ∧
      network.peers (ghostSession tag index) = NotionRunAllocation.emptyPeer := by
  classical
  obtain ⟨touched, untouched⟩ := finite_peer_support reachable
  obtain ⟨index, absent⟩ := Infinite.exists_notMem_finset
    (((touched ++ avoid).map (fun peer => peer.length - 1)).toFinset)
  have fresh : ghostSession tag index ∉ touched ++ avoid := by
    intro member
    apply absent
    simp only [List.mem_toFinset]
    apply List.mem_map.mpr
    refine ⟨ghostSession tag index, member, ?_⟩
    simp [ghostSession]
  refine ⟨index, ?_, untouched _ ?_⟩
  · intro member
    exact fresh (List.mem_append_right _ member)
  · intro member
    exact fresh (List.mem_append_left _ member)

/-- Publishing an immutable snapshot needs neither a new allocator nor an
assumed replay result: a fresh ghost receives the existing peer's whole version. -/
theorem publish_snapshot {network : State}
    (honest : NotionCoreMachineNetwork.Reach network) (source : Session)
    (tag : Nat) (avoid : List Session) :
    ∃ index, ghostSession tag index ∉ avoid ∧
      NotionCoreMachineNetwork.Reach (exchange network (ghostSession tag index) source) ∧
      reconstruct (exchange network (ghostSession tag index) source) (ghostSession tag index) =
        reconstruct network source := by
  have allocation := NotionCoreIssuance.allocation_reachable
    (NotionCoreMachineNetwork.issuance_reachable honest)
  obtain ⟨index, fresh, empty⟩ := fresh_ghost allocation tag avoid
  refine ⟨index, fresh, exchange_reachable honest _ source, ?_⟩
  apply snapshot_reconstruct
  exact congrArg NotionRunAllocation.Peer.received empty

#print axioms snapshot_reconstruct
#print axioms restore_transactions
#print axioms exchange_reachable
#print axioms publish_snapshot
end Sal.MRDTs.Instances.NotionCoreMachineSnapshots
