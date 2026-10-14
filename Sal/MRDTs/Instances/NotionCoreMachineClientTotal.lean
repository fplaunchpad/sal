import Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal

/-! Valid gaps in an existing core block admit actual insert/split preparation.
Selection, endpoint scans and internal decoding all succeed; no next-state or
visible-effect equation is assumed. Empty inserts remain source early no-ops. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineClientTotal
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreMachineDeleteTotal (visibleLength)
open NotionCorePayload (BlockKey Transaction)
open NotionCoreSource (Atom Slice)
open NotionCoreSpec (Address)
open NotionCorePreparation (characters zeroOrigin)

private theorem zero_total (slices : List Slice) (nonempty : slices ≠ []) :
    ∃ address, zeroOrigin slices = some address := by
  induction slices with
  | nil => contradiction
  | cons slice rest ih =>
    cases rest with
    | nil => exact ⟨slice.start,rfl⟩
    | cons next rest =>
      by_cases empty : (characters slice).isEmpty = true
      · simpa [zeroOrigin,empty] using ih (by simp)
      · exact ⟨slice.start,by simp [zeroOrigin,empty]⟩

private theorem locate_total (slices : List Slice) (nonempty : slices ≠ []) (index : Nat)
    (bound : index ≤ (slices.flatMap characters).length) :
    ∃ address, locateSlices slices index = some address := by
  cases index with
  | zero => simpa [locateSlices] using zero_total slices nonempty
  | succ n =>
    have inside : n < (slices.flatMap characters).length := by omega
    exact ⟨((slices.flatMap characters)[n]).address,by simp only [locateSlices,if_pos bound,List.getElem?_eq_getElem inside,Option.map_some]⟩

private theorem materialize_nonempty (state : State) (tree : NotionCoreSliceForest.Tree)
    (slices : List Slice) (accepted : materialize state tree = some slices) : slices ≠ [] := by
  cases tree with
  | node ref children =>
    simp only [materialize,NotionCoreSliceForest.preorderTree,List.mapM_cons] at accepted
    obtain ⟨head,_,later⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest,_,same⟩ := Option.bind_eq_some_iff.mp later
    have equal : head :: rest = slices := Option.some.inj same
    rw [← equal]
    simp

/-- A valid visible gap selects and decodes a physical address in the actual
stored block; the statement has no successful-selection premise. -/
theorem gap_total (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (part : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (block : BlockKey) (stored : ∃ found ∈ state.forest, found.id = blockName block)
    (index : Nat) (bound : index ≤ visibleLength state block) :
    ∃ address inst origin, locateAddress state block index = some address ∧
      decodeAddress address = some (inst,origin) := by
  cases found : state.forest.find? (fun entry => entry.id == blockName block) with
  | none =>
    obtain ⟨entry,member,name⟩ := stored
    have no := List.find?_eq_none.mp found entry member
    simp [name] at no
  | some entry =>
    obtain ⟨slices,materialized⟩ := NotionCoreMachineDeleteTotal.materialize_total state part unique
      entry (List.mem_of_find?_eq_some found)
    have extracted : blockSlices state block = some slices := by simp [blockSlices,found,materialized]
    have inside : index ≤ (slices.flatMap characters).length := by simpa [visibleLength,extracted] using bound
    obtain ⟨address,selected⟩ := locate_total slices (materialize_nonempty state entry.title slices materialized) index inside
    have located : locateAddress state block index = some address := by simp [locateAddress,extracted,selected]
    obtain ⟨inst,origin,decoded⟩ := located_decode_progress txs state accepted block index address located
    exact ⟨address,inst,origin,located,decoded⟩

/-- Both real positional preparers succeed at every valid gap. -/
theorem prepare_gap_total (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (part : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (block : BlockKey) (stored : ∃ found ∈ state.forest, found.id = blockName block)
    (index : Nat) (bound : index ≤ visibleLength state block) :
    ∃ inst origin, prepareSplit state block index = some (.split block inst origin) ∧
      ∀ atoms : List Nat, atoms ≠ [] →
        prepareInsert state block index atoms = some (.insert block inst origin atoms) := by
  obtain ⟨address,inst,origin,located,decoded⟩ := gap_total txs state accepted part unique block stored index bound
  refine ⟨inst,origin,by simp [prepareSplit,located,decoded],?_⟩
  intro atoms nonempty
  simp [prepareInsert,nonempty,located,decoded]

/-- Honest reconstruction supplies every structural premise of gap selection.
Only block existence and the requested visible-position bound remain. -/
theorem honest_prepare_gap_total (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (block : BlockKey) (index : Nat)
    (stored : ∃ found ∈ ((NotionCoreReconstruction.reconstruct network peer).getD {}).forest,
      found.id = blockName block)
    (bound : index ≤ visibleLength ((NotionCoreReconstruction.reconstruct network peer).getD {}) block) :
    ∃ state inst origin, NotionCoreReconstruction.reconstruct network peer = some state ∧
      prepareSplit state block index = some (.split block inst origin) ∧
      ∀ atoms : List Nat, atoms ≠ [] →
        prepareInsert state block index atoms = some (.insert block inst origin atoms) := by
  obtain ⟨state,accepted,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  rw [accepted] at stored bound
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    peer (NotionCoreReconstruction.transactions network peer) [] (by simp) state accepted
  obtain ⟨inst,origin,splitReady,insertReady⟩ := prepare_gap_total _ state accepted part unique block stored index bound
  exact ⟨state,inst,origin,accepted,splitReady,insertReady⟩

/-- A valid split request reserves and publishes a transaction, so it extends
honest reachability. This proves actual issuance, not merely payload selection. -/
theorem honest_issue_split (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (block : BlockKey) (index : Nat)
    (stored : ∃ found ∈ ((NotionCoreReconstruction.reconstruct network peer).getD {}).forest,
      found.id = blockName block)
    (bound : index ≤ visibleLength ((NotionCoreReconstruction.reconstruct network peer).getD {}) block) :
    ∃ next, NotionCoreMachineNetwork.issue network peer (.split block index) = some next ∧
      NotionCoreMachineNetwork.Reach next := by
  obtain ⟨state,inst,origin,accepted,prepared,_⟩ := honest_prepare_gap_total network reachable peer block index stored bound
  have success : ∃ next, NotionCoreMachineNetwork.issue network peer (.split block index) = some next := by
    simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
      accepted,NotionCoreMachineNetwork.prepareRequest,prepared,NotionCorePayload.prepare,
      NotionCorePayload.Payload.emits]
  obtain ⟨next,issued⟩ := success
  exact ⟨next,issued,NotionCoreMachineNetwork.Reach.request peer (.split block index) reachable issued⟩

theorem honest_issue_insert (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (block : BlockKey) (index : Nat) (atoms : List Nat) (nonempty : atoms ≠ [])
    (stored : ∃ found ∈ ((NotionCoreReconstruction.reconstruct network peer).getD {}).forest,
      found.id = blockName block)
    (bound : index ≤ visibleLength ((NotionCoreReconstruction.reconstruct network peer).getD {}) block) :
    ∃ next, NotionCoreMachineNetwork.issue network peer (.insert block index atoms) = some next ∧
      NotionCoreMachineNetwork.Reach next := by
  obtain ⟨state,inst,origin,accepted,_,prepare⟩ := honest_prepare_gap_total network reachable peer block index stored bound
  have prepared := prepare atoms nonempty
  have success : ∃ next, NotionCoreMachineNetwork.issue network peer (.insert block index atoms) = some next := by
    simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
      nonempty,accepted,NotionCoreMachineNetwork.prepareRequest,prepared,NotionCorePayload.prepare,
      NotionCorePayload.Payload.emits]
  obtain ⟨next,issued⟩ := success
  exact ⟨next,issued,NotionCoreMachineNetwork.Reach.request peer (.insert block index atoms) reachable issued⟩

/-- A nonempty in-range deletion prepares, reserves one transaction, and
extends honest reachability. Empty clamped ranges remain early/no-event cases. -/
theorem honest_issue_erase (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (block : BlockKey) (start stop : Nat)
    (stored : ∃ found ∈ ((NotionCoreReconstruction.reconstruct network peer).getD {}).forest,
      found.id = blockName block)
    (nonempty : start < stop)
    (bounded : stop ≤ visibleLength ((NotionCoreReconstruction.reconstruct network peer).getD {}) block) :
    ∃ next, NotionCoreMachineNetwork.issue network peer (.erase block start stop) = some next ∧
      NotionCoreMachineNetwork.Reach next := by
  obtain ⟨state,inst,ids,accepted,prepared,idsNonempty⟩ :=
    NotionCoreMachineDeleteTotal.honest_erase_request_total network reachable peer block start stop
      stored nonempty bounded
  have sortedNonempty : (NotionCoreRanges.sorted ids).isEmpty = false := by
    rw [(NotionCoreRanges.sorted_perm ids).isEmpty_eq]
    simp [idsNonempty]
  have success : ∃ next, NotionCoreMachineNetwork.issue network peer (.erase block start stop) = some next := by
    simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
      show start ≠ stop by omega,accepted,NotionCoreMachineNetwork.prepareRequest,prepared,
      NotionCorePayload.prepare,NotionCorePayload.Payload.emits,sortedNonempty]
  obtain ⟨next,issued⟩ := success
  exact ⟨next,issued,NotionCoreMachineNetwork.Reach.request peer (.erase block start stop) reachable issued⟩

/-- Creation accepts no predecessor or an actual existing predecessor in the
peer's reconstructed document. Unknown predecessors are not admitted here. -/
theorem honest_issue_create (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (afterBlock : Option BlockKey)
    (valid : ∀ block, afterBlock = some block →
      ∃ found ∈ ((NotionCoreReconstruction.reconstruct network peer).getD {}).forest,
        found.id = blockName block) :
    ∃ next, NotionCoreMachineNetwork.issue network peer (.create afterBlock) = some next ∧
      NotionCoreMachineNetwork.Reach next := by
  obtain ⟨state,accepted,_,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have prepared : prepareCreate state afterBlock = some (.create afterBlock) := by
    cases afterBlock with
    | none => rfl
    | some block =>
        have present := valid block rfl
        rw [accepted] at present
        have found : state.forest.any (fun entry => entry.id == blockName block) = true := by
          simpa using present
        simp [prepareCreate,found]
  have success : ∃ next, NotionCoreMachineNetwork.issue network peer (.create afterBlock) = some next := by
    simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
      accepted,NotionCoreMachineNetwork.prepareRequest,prepared,NotionCorePayload.prepare,
      NotionCorePayload.Payload.emits]
  obtain ⟨next,issued⟩ := success
  exact ⟨next,issued,NotionCoreMachineNetwork.Reach.request peer (.create afterBlock) reachable issued⟩

#print axioms honest_issue_erase
#print axioms honest_issue_create

#print axioms honest_prepare_gap_total
#print axioms honest_issue_split
#print axioms honest_issue_insert

#print axioms gap_total
#print axioms prepare_gap_total
end Sal.MRDTs.Instances.NotionCoreMachineClientTotal
