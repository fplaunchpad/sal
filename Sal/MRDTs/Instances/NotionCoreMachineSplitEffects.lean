import Sal.MRDTs.Instances.NotionCoreMachineDocumentSplit
import Sal.MRDTs.Instances.NotionCoreMachineInsertEffects

/-! Honest split request effects use actual source gap preparation and atomic
create/split execution, then reconstruct the issuer's appended transaction.
Source IDs are payload identities; no Sal RA/event bridge is claimed here. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineSplitEffects
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreMachineDocument
open NotionCoreMachineDocumentClient
open NotionCorePayload (BlockKey Transaction)
open NotionCoreSource (Block Atom)
open NotionCoreSpec (Address)

/-- Both actual preparers use the same selected gap. The inherited marker at
attached index zero is therefore related to the independent PreparedGap. -/
theorem prepared_split_gap (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (part : NotionCoreMachinePartition.Partitioned state)
    (shape : NotionCoreMachineShape.ShapeInvariant state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (block inst : BlockKey) (name : source.id = blockName block)
    (index : Nat) (origin : NotionCoreOriginTree.Origin)
    (prepared : prepareSplit state block index = some (.split block inst origin)) :
    NotionCorePreparation.locate source index = some (NotionCorePhysicalReplay.originAddress (blockName inst) origin) ∧
    NotionCoreSpec.PreparedGap source.project.slots (NotionCorePhysicalReplay.originAddress (blockName inst) origin) index := by
  have insert : prepareInsert state block index [0] = some (.insert block inst origin [0]) := by
    cases located : locateAddress state block index with
    | none => simp [prepareSplit,located] at prepared
    | some address =>
      cases decoded : decodeAddress address with
      | none => simp [prepareSplit,located,decoded] at prepared
      | some pair =>
        rcases pair with ⟨actual,selected⟩
        have same : actual = inst ∧ selected = origin := by simpa [prepareSplit,located,decoded] using prepared
        obtain ⟨rfl,rfl⟩ := same
        simp [prepareInsert,located,decoded]
  exact NotionCoreMachineInsertEffects.prepared_insert_gap txs state accepted part shape document materialized
    source member block inst name index origin [0] insert

private theorem projected_address_instance (state : State) (part : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (shape : NotionCoreMachineShape.ShapeInvariant state) (aligned : NotionCoreMachineDisplay.Aligned state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (address : Address) (member : address ∈ NotionCoreInvariant.addresses (NotionCoreSourceDocument.project document)) :
    ∃ entry ∈ state.instances, entry.1 = address.1 := by
  have permutation := NotionCoreMachineDocumentInvariant.projected_addresses_perm state part shape aligned document materialized
  obtain ⟨owned,present,inside⟩ := List.mem_flatMap.mp (permutation.mem_iff.mp member)
  obtain ⟨atoms,extracted⟩ := NotionCoreMachinePartition.ref_extracts state part unique owned present
  rw [NotionCoreMachineDocumentInvariant.interval_extracted state owned.2 atoms extracted] at inside
  have same : address.1 = owned.2.start.1 := by
    rcases List.mem_cons.mp inside with rfl | inside
    · rfl
    · obtain ⟨atom,atomMember,rfl⟩ := List.mem_map.mp inside
      exact (slice_storage state owned.2 atoms extracted).2 atom atomMember
  simpa only [same] using part.refsExist owned present

private theorem two_steps (document final : NotionCoreSourceDocument.Document)
    (first second : NotionCoreSourceDocument.Command)
    (execution : NotionCoreSourceDocument.Execution document [first,second] final) :
    ∃ middle, NotionCoreSourceDocument.step document first = some middle ∧
      NotionCoreSourceDocument.step middle second = some final := by
  cases execution with
  | cons guard firstStep later =>
    cases later with
    | cons guard secondStep finalStep =>
      cases finalStep
      exact ⟨_,firstStep,secondStep⟩

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- A split prepared at its honest canonical prefix executes atomically and
cuts the requested block's visible text at the selected position. All old and
new structure, fresh names, root absence and routing are derived. -/
theorem canonical_prepared_split_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (before ++ source :: afterBlocks))
    (block inst : BlockKey) (name : source.id = blockName block) (index : Nat)
    (origin : NotionCoreOriginTree.Origin) (payload : tx.payload = .split block inst origin)
    (prepared : prepareSplit state block index = some tx.payload) :
    ∃ next after, applyTransaction state tx = some next ∧ materializeDocument next = some after ∧
      render next = some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take index),
          (blockName (.issued tx.id),(NotionCoreSpec.text source.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨checked,checkedReplay,part,shape,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct
    network reachable peer pre (tx :: suffix) position
  have same : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    peer pre (tx :: suffix) position state accepted
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names]) accepted
  have addresses := NotionCoreMachineDocumentInvariant.projected_addresses_unique state part unique shape aligned _ materialized
  have ids := materialized_ids state _ materialized
  have blockUnique : ((before ++ source :: afterBlocks).map Block.id).Nodup := by
    rw [ids]
    exact aligned.2.nodup_iff.mpr aligned.1
  have located := (prepared_split_gap pre state accepted part shape _ materialized source (by simp) block inst name
    index origin (by simpa only [payload] using prepared)).1
  have bound : index ≤ (NotionCorePreparation.characters source.active).length := by
    by_contra outside
    have tooLarge : ¬index ≤ ((NotionCorePreparation.nodes source).flatMap NotionCorePreparation.characters).length := by
      simpa only [NotionCorePreparation.nodes_characters] using outside
    simp only [NotionCorePreparation.locate,if_neg tooLarge,reduceCtorEq] at located
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh network
    (NotionCoreMachineNetwork.creator_reachable reachable) peer pre suffix tx position state accepted
  have freshName : blockName (.issued tx.id) ∉ (before ++ source :: afterBlocks).map Block.id := by
    rw [ids]
    intro member
    have old := aligned.2.mem_iff.mp member
    obtain ⟨stored,present,equal⟩ := List.mem_map.mp old
    exact freshBlock stored present equal
  have freshRoot : (NotionCoreSpec.root (blockName (.issued tx.id))).address ∉
      NotionCoreInvariant.addresses (NotionCoreSourceDocument.project (before ++ source :: afterBlocks)) := by
    intro member
    obtain ⟨entry,present,equal⟩ := projected_address_instance state part unique shape aligned _ materialized _ member
    exact freshInstance entry present equal
  let markerId := (Encodable.encode tx.id.session,tx.id.counter)
  obtain ⟨selected,created,expected,selection,createStep,splitStep,effect⟩ := NotionCorePreparation.source_split_effect
    before afterBlocks source index (blockName (.issued tx.id)) (blockName (.issued tx.id)) markerId
    addresses blockUnique bound freshName freshRoot
  have selectedEq : selected = NotionCorePhysicalReplay.originAddress (blockName inst) origin :=
    Option.some.inj (selection.symm.trans located)
  obtain ⟨next,after,transaction,extracted,execution⟩ := NotionCoreMachineDocumentSplit.canonical_split_execution
    network reachable peer pre suffix tx position state accepted _ materialized block inst origin payload
  have explicit : NotionCoreSourceDocument.Execution (before ++ source :: afterBlocks)
      [.create (blockName (.issued tx.id)) (blockName (.issued tx.id)) (some source.id),
       .split selected (selected.1,.event markerId) (blockName (.issued tx.id))] after := by
    cases origin <;> simpa [NotionCoreMachineCommands.commands,payload,name,selectedEq,markerId,
      NotionCorePhysicalReplay.address,NotionCorePhysicalReplay.localId,
      NotionCorePhysicalReplay.originAddress] using execution
  obtain ⟨middle,actualCreate,actualSplit⟩ := two_steps _ after _ _ explicit
  have middleEq : created = middle := Option.some.inj (createStep.symm.trans actualCreate)
  rw [← middleEq] at actualSplit
  have afterEq : expected = after := Option.some.inj (splitStep.symm.trans actualSplit)
  have nextReplay : replay {} (pre ++ [tx]) = some next := by
    simp [replay_append,accepted,replay,transaction,Bind.bind,Option.bind]
  have nextPosition : NotionCoreReconstruction.transactions network peer = (pre ++ [tx]) ++ suffix := by
    simpa [List.append_assoc] using position
  obtain ⟨checked,checkedReplay,nextPart,nextShape,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct
    network reachable peer (pre ++ [tx]) suffix nextPosition
  have sameNext : checked = next := Option.some.inj (checkedReplay.symm.trans nextReplay)
  subst checked
  have rendered := materialized_render next nextPart nextShape.1 nextShape.2.2 after extracted
  rw [← afterEq,effect] at rendered
  exact ⟨next,after,transaction,extracted,rendered⟩

#print axioms canonical_prepared_split_effect

private theorem split_preparation_kind (state : State) (block : BlockKey) (index : Nat)
    (payload : NotionCorePayload.Payload) (prepared : prepareSplit state block index = some payload) :
    ∃ inst origin, payload = .split block inst origin := by
  cases located : locateAddress state block index with
  | none => simp [prepareSplit,located] at prepared
  | some address =>
    cases decoded : decodeAddress address with
    | none => simp [prepareSplit,located,decoded] at prepared
    | some pair =>
      rcases pair with ⟨inst,origin⟩
      exact ⟨inst,origin,by simpa [prepareSplit,located,decoded] using prepared.symm⟩

/-- Actual honest issuance places the split transaction after the issuer's
received prefix and yields precisely the visible cut in its new rendering. -/
theorem issued_split_effect (network nextNetwork : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (block : BlockKey) (index : Nat)
    (issued : NotionCoreMachineNetwork.issue network peer (.split block index) = some nextNetwork)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (before ++ source :: afterBlocks))
    (name : source.id = blockName block) :
    ∃ target, (NotionCoreReconstruction.reconstruct nextNetwork peer >>= render) =
      some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take index),
          (target,(NotionCoreSpec.text source.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  have nextReach : NotionCoreMachineNetwork.Reach nextNetwork := .request peer (.split block index) reachable issued
  cases selected : prepareSplit state block index with
  | none => simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
      reconstructed,NotionCoreMachineNetwork.prepareRequest,selected] at issued
  | some payload =>
    cases reserved : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) peer payload with
    | none => simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
        reconstructed,NotionCoreMachineNetwork.prepareRequest,selected,reserved] at issued
    | some tx =>
      have networkEq : NotionCorePayloadNetwork.emit network peer payload tx = nextNetwork := by
        simpa [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,
          reconstructed,NotionCoreMachineNetwork.prepareRequest,selected,reserved] using issued
      obtain ⟨inst,origin,payloadEq⟩ := split_preparation_kind state block index payload selected
      have actualPayload := NotionCorePayloadNetwork.prepared_payload reserved
      have txPayload : tx.payload = .split block inst origin := actualPayload.trans payloadEq
      have nextOrder := NotionCoreMachineInsertEffects.emitted_transactions_append network
        (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
        peer payload tx reserved (by rw [networkEq]; exact
          NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable nextReach))
      rw [networkEq] at nextOrder
      have position : NotionCoreReconstruction.transactions nextNetwork peer =
          NotionCoreReconstruction.transactions network peer ++ tx :: [] := by simpa using nextOrder
      obtain ⟨next,after,transaction,extracted,rendered⟩ := canonical_prepared_split_effect nextNetwork nextReach peer
        (NotionCoreReconstruction.transactions network peer) [] tx position state reconstructed before afterBlocks source
        materialized block inst name index origin txPayload (by simpa only [actualPayload] using selected)
      have nextReplay : NotionCoreReconstruction.reconstruct nextNetwork peer = some next := by
        unfold NotionCoreReconstruction.reconstruct
        rw [nextOrder,replay_append]
        have oldReplay : replay {} (NotionCoreReconstruction.transactions network peer) = some state := reconstructed
        simp [oldReplay,replay,transaction,Bind.bind,Option.bind]
      exact ⟨blockName (.issued tx.id),by simp [nextReplay,rendered]⟩

/-- Every valid honest split request issues successfully and its actual new
issuer rendering is the ordinary visible cut, including zero/end positions. -/
theorem honest_split_request_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (before ++ source :: afterBlocks))
    (block : BlockKey) (name : source.id = blockName block) (index : Nat)
    (bound : index ≤ NotionCoreMachineDeleteTotal.visibleLength state block) :
    ∃ nextNetwork target, NotionCoreMachineNetwork.issue network peer (.split block index) = some nextNetwork ∧
      (NotionCoreReconstruction.reconstruct nextNetwork peer >>= render) =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take index),
            (target,(NotionCoreSpec.text source.project.slots).drop index)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨checked,current,part,shape,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have same : checked = state := Option.some.inj (current.symm.trans reconstructed)
  subst checked
  have slices := document_block_slices state part shape _ materialized source (by simp) block name
  have stored : ∃ found ∈ state.forest, found.id = blockName block := by
    cases found : state.forest.find? (fun old => old.id == blockName block) with
    | none => simp [blockSlices,found] at slices
    | some entry => exact ⟨entry,List.mem_of_find?_eq_some found,by simpa using List.find?_some found⟩
  obtain ⟨next,issued,_⟩ := NotionCoreMachineClientTotal.honest_issue_split network reachable peer block index
    (by simpa [reconstructed] using stored) (by simpa [reconstructed] using bound)
  obtain ⟨target,effect⟩ := issued_split_effect network next reachable peer block index issued state reconstructed
    before afterBlocks source materialized name
  exact ⟨next,target,issued,effect⟩

#print axioms issued_split_effect
#print axioms honest_split_request_effect

namespace SPOT
private def cutId : NotionRunAllocation.Id := ⟨3,[65]⟩
private def nextId : NotionRunAllocation.Id := ⟨4,[65]⟩
private def afterSplit : Option (List (Nat × List Nat)) := do
  let state ← replay {} [NotionCorePayload.bootstrap [97,98],⟨cutId,.split .initial .initial (.item ⟨1,[65]⟩)⟩]
  let payload ← prepareSplit state (.issued cutId) 0
  applyTransaction state ⟨nextId,payload⟩ >>= render
/-- Repeated attached zero split cuts a | b into a | empty | b. The inherited
marker selects b's active interval, rather than the inactive own-title root. -/
theorem attached_zero_split_control :
    afterSplit = some [(0,[97]),(blockName (.issued cutId),[]),(blockName (.issued nextId),[98])] ∧
    afterSplit ≠ some [(0,[]),(blockName (.issued cutId),[98]),(blockName (.issued nextId),[97])] ∧
    afterSplit ≠ some [(0,[97]),(blockName (.issued cutId),[98]),(blockName (.issued nextId),[])] := by decide +kernel
end SPOT
end Sal.MRDTs.Instances.NotionCoreMachineSplitEffects
