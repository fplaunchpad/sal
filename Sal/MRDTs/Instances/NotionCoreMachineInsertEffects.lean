import Sal.MRDTs.Instances.NotionCoreMachineDocumentInsert
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
import Sal.MRDTs.Instances.NotionCoreMachineClientTotal

/-! Local positional insertion through the actual canonical core interpreter.
The selected inherited-leaf anchor at zero is related by PreparedGap; it need
not equal the independent convenience preparer's empty-title anchor. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineInsertEffects
open NotionCoreMachine
open NotionCoreMachineClient
open NotionCoreMachineDocument
open NotionCoreMachineDocumentClient
open NotionCorePayload (BlockKey Transaction)
open NotionCoreSource (Atom Block)
open NotionCoreSpec (Address)

private theorem located_roundtrip (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (block : BlockKey) (index : Nat) (address : Address)
    (located : locateAddress state block index = some address)
    (inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (decoded : decodeAddress address = some (inst,origin)) :
    NotionCorePhysicalReplay.originAddress (blockName inst) origin = address := by
  obtain ⟨_,entry,stored,name⟩ := locate_storage state block index address located
  obtain ⟨_,_,key,_,keyName⟩ := NotionCoreMachineCreators.replay_instance_used txs state accepted address.1
    (List.mem_map.mpr ⟨entry,stored,name⟩)
  have physical := locate_physical state block index address located
  simp only [NotionCoreMachine.physical,NotionCorePhysicalReplay.physical,List.map_cons,List.mem_cons,List.mem_map] at physical
  rcases physical with start | ⟨atom,⟨item,member,equal⟩,addressEq⟩
  · have encoded : NotionCorePhysicalReplay.originAddress (blockName key) .start = address := by
      simpa [NotionCorePhysicalReplay.originAddress,keyName] using start.symm
    have same := decode_originAddress key .start
    rw [encoded,decoded] at same
    have pair : (inst,origin) = (key,.start) := Option.some.inj same
    have instEq : inst = key := congrArg Prod.fst pair
    have originEq := congrArg Prod.snd pair
    dsimp only at originEq
    rw [instEq,originEq]
    exact encoded
  · subst atom
    have encoded : NotionCorePhysicalReplay.originAddress (blockName key) (.item item.id) = address := by
      simpa [NotionCorePhysicalReplay.originAddress,keyName] using addressEq
    have same := decode_originAddress key (.item item.id)
    rw [encoded,decoded] at same
    have pair : (inst,origin) = (key,.item item.id) := Option.some.inj same
    have instEq : inst = key := congrArg Prod.fst pair
    have originEq := congrArg Prod.snd pair
    dsimp only at originEq
    rw [instEq,originEq]
    exact encoded

/-- Actual successful insertion preparation selects a PreparedGap in the
same displayed block's independent slots, including a zero gap after empty
slices of its chain; the prepared block is alive. -/
theorem prepared_insert_gap (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state)
    (document : NotionCoreSourceDocument.Document) (materialized : materializeDocument state = some document)
    (source : Block) (member : source ∈ document) (block inst : BlockKey) (name : source.id = blockName block)
    (index : Nat) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (prepared : prepareInsert state block index atoms = some (.insert block inst origin atoms)) :
    NotionCorePreparation.locate source index =
      some (NotionCorePhysicalReplay.originAddress (blockName inst) origin) ∧
    NotionCoreSpec.PreparedGap source.project.slots
      (NotionCorePhysicalReplay.originAddress (blockName inst) origin) index ∧
    source.alive = true := by
  cases empty : atoms.isEmpty with
  | true => simp [prepareInsert,empty] at prepared
  | false =>
    cases located : locateAddress state block index with
    | none => simp [prepareInsert,empty,located] at prepared
    | some address =>
      cases decoded : decodeAddress address with
      | none => simp [prepareInsert,empty,located,decoded] at prepared
      | some pair =>
        rcases pair with ⟨actual,selected⟩
        have same : actual = inst ∧ selected = origin := by simpa [prepareInsert,empty,located,decoded] using prepared
        obtain ⟨rfl,rfl⟩ := same
        have roundtrip := located_roundtrip txs state accepted block index address located actual selected decoded
        have alive : source.alive = true := by
          cases live : source.alive
          · have none := document_block_tombstone state document materialized source member live block name
            simp [locateAddress,none] at located
          · rfl
        have slices := document_block_slices state document materialized source member alive block name
        have sourceLocated : NotionCorePreparation.locate source index = some address := by
          simpa [locateAddress,slices,locateSlices,NotionCorePreparation.locate] using located
        rw [← roundtrip] at sourceLocated
        exact ⟨sourceLocated,NotionCorePreparation.locate_prepared source index _ sourceLocated,alive⟩

private theorem run_values (atoms : List Nat) :
    (List.range atoms.length).map (fun index => atoms[index]?.getD 0) = atoms := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [List.getElem_map,List.getElem_range]
    simp [List.getElem?_eq_getElem right]

/-- Actual static text decoding contributes exactly the requested atom list. -/
theorem fresh_text_values (inst : Nat) (id : NotionRunAllocation.Id) (atoms : List Nat) :
    NotionCoreSpec.text (((NotionCorePayload.textItems id atoms (fun _ => false)).map
      (NotionCorePhysicalReplay.atom inst)).map Atom.slot) = atoms := by
  simp [NotionCoreSpec.text,NotionCorePayload.textItems,NotionCorePhysicalReplay.atom,Atom.slot,
    List.filter_map,List.map_map,Function.comp_def]
  exact run_values atoms

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- An honestly generated canonical transaction prepared at the current
prefix has the ordinary insertion effect on the actual renderer. All replay
structure, spatial safety, freshness and live birth flags are derived. The
preparation premise records which positional request produced the payload. -/
theorem canonical_prepared_insert_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactions network peer = pre ++ tx :: suffix)
    (state : State) (accepted : replay {} pre = some state)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (before ++ source :: afterBlocks))
    (block inst : BlockKey) (name : source.id = blockName block) (index : Nat)
    (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (payload : tx.payload = .insert block inst origin atoms)
    (prepared : prepareInsert state block index atoms = some tx.payload) :
    ∃ next after, applyTransaction state tx = some next ∧ materializeDocument next = some after ∧
      render next = some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take index ++ atoms ++
          (NotionCoreSpec.text source.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  obtain ⟨checked,checkedReplay,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct
    network reachable peer pre (tx :: suffix) position
  have same : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  have physicalUnique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    peer pre (tx :: suffix) position state accepted
  have aligned := NotionCoreMachineDisplay.replay_aligned {} state pre
    (by simp [NotionCoreMachineDisplay.Aligned,NotionCoreDisplayOrder.Aligned,NotionCoreDisplayOrder.names,
      NotionCoreDisplayOrder.shown]) accepted
  have unique := NotionCoreMachineDocumentInvariant.projected_addresses_unique state part physicalUnique aligned _ materialized
  obtain ⟨_,gap,alive⟩ := prepared_insert_gap pre state accepted _ materialized source (by simp) block inst name
    index origin atoms (by simpa only [payload] using prepared)
  obtain ⟨next,after,transaction,extracted,sourceStep⟩ := NotionCoreMachineDocumentInsert.canonical_insert_source_step
    network reachable peer pre suffix tx position state accepted _ materialized block inst origin atoms payload
  let fresh := ((NotionCorePayload.textItems tx.id atoms (fun _ => false)).map (NotionCorePhysicalReplay.atom (blockName inst)))
  have semanticStep := NotionCoreMachineDocumentInvariant.honest_prefix_source_step network reachable peer
    pre (tx :: suffix) position state accepted _ after materialized
    (.insert (NotionCorePhysicalReplay.originAddress (blockName inst) origin) fresh) sourceStep
  have semanticUnique : ((NotionCoreSourceDocument.project before ++ source.project ::
      NotionCoreSourceDocument.project afterBlocks).flatMap (fun block => block.slots.map NotionCoreSpec.Slot.address)).Nodup := by
    simpa [NotionCoreInvariant.addresses,NotionCoreSourceDocument.project] using unique
  obtain ⟨semantic,semanticAccepted,semanticEffect⟩ := NotionCorePreparation.insert_at_prepared_gap
    (NotionCoreSourceDocument.project before) (NotionCoreSourceDocument.project afterBlocks)
    source.project (NotionCorePhysicalReplay.originAddress (blockName inst) origin) index (fresh.map Atom.slot) semanticUnique gap alive
  have sourceSemantic : NotionCoreSpec.step (NotionCoreSourceDocument.project before ++ source.project ::
      NotionCoreSourceDocument.project afterBlocks)
      (.insert (NotionCorePhysicalReplay.originAddress (blockName inst) origin) (fresh.map Atom.slot)) =
      some (NotionCoreSourceDocument.project after) := by
    simpa [NotionCoreSourceDocument.project,NotionCoreSourceDocument.Command.semantic] using semanticStep
  have projectEq : semantic = NotionCoreSourceDocument.project after := Option.some.inj (semanticAccepted.symm.trans sourceSemantic)
  have effect : NotionCoreSpec.view (NotionCoreSourceDocument.project after) =
      NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take index ++ atoms ++
          (NotionCoreSpec.text source.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks) := by
    rw [← projectEq]
    simpa only [fresh,fresh_text_values] using semanticEffect
  have rendered := materialized_render next after extracted
  rw [effect] at rendered
  exact ⟨next,after,transaction,extracted,rendered⟩

#print axioms prepared_insert_gap
#print axioms canonical_prepared_insert_effect

/-- Source issuance appends its transaction after the issuer's entire received
canonical version. Archive key uniqueness excludes duplicate receipt aliases;
the reserved counter exceeds every previously received run. -/
theorem emitted_transactions_append (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCorePayloadNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (payload : NotionCorePayload.Payload) (tx : Transaction)
    (prepared : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) peer payload = some tx)
    (nextReach : NotionCorePayloadNetwork.Reach (NotionCorePayloadNetwork.emit network peer payload tx)) :
    NotionCoreReconstruction.transactions (NotionCorePayloadNetwork.emit network peer payload tx) peer =
      NotionCoreReconstruction.transactions network peer ++ [tx] := by
  let next := NotionCorePayloadNetwork.emit network peer payload tx
  have reservationEq : NotionCorePayload.reservation tx = NotionRunAllocation.reserve
      (network.allocation.peers peer) peer payload.width := by
    exact congrArg NotionCoreIssuance.Record.run (NotionCorePayload.prepare_record prepared)
  have idEq : tx.id = (NotionRunAllocation.reserve (network.allocation.peers peer) peer payload.width).first :=
    congrArg NotionRunAllocation.Run.first reservationEq
  have keys := NotionCoreArchiveOrder.archive_keys_unique next nextReach
  have absent : tx.id ∉ (network.entries.map NotionCorePayloadNetwork.Entry.tx).map Transaction.id := by
    simpa only [next,NotionCorePayloadNetwork.emit,List.map_cons] using (List.nodup_cons.mp keys).1
  have different : ∀ old ∈ network.entries.map NotionCorePayloadNetwork.Entry.tx,
      NotionCorePayload.reservation old ≠ NotionCorePayload.reservation tx := by
    intro old member equal
    exact absent (List.mem_map.mpr ⟨old,member,congrArg NotionRunAllocation.Run.first equal⟩)
  have receipts : (next.allocation.peers peer).received = NotionCorePayload.reservation tx ::
      (network.allocation.peers peer).received := by
    simp [next,NotionCorePayloadNetwork.emit,NotionRunAllocation.issue,NotionRunAllocation.receive,reservationEq]
  have filtered : (next.entries.map NotionCorePayloadNetwork.Entry.tx).filter
      (fun old => NotionCorePayload.reservation old ∈ (next.allocation.peers peer).received) =
      tx :: (network.entries.map NotionCorePayloadNetwork.Entry.tx).filter
        (fun old => NotionCorePayload.reservation old ∈ (network.allocation.peers peer).received) := by
    change (tx :: network.entries.map NotionCorePayloadNetwork.Entry.tx).filter
      (fun old => NotionCorePayload.reservation old ∈ (next.allocation.peers peer).received) = _
    simp only [receipts,List.filter_cons]
    simp only [List.mem_cons_self,decide_true,if_true,List.cons.injEq,true_and]
    apply List.filter_congr
    intro old member
    simp [different old member]
  have newPerm := List.mergeSort_perm ((next.entries.map NotionCorePayloadNetwork.Entry.tx).filter
    (fun old => NotionCorePayload.reservation old ∈ (next.allocation.peers peer).received))
    (fun a b => decide (NotionCoreReconstruction.Ascending a b))
  change (NotionCoreReconstruction.transactions next peer).Perm _ at newPerm
  rw [filtered] at newPerm
  have oldPerm := List.mergeSort_perm ((network.entries.map NotionCorePayloadNetwork.Entry.tx).filter
    (fun old => NotionCorePayload.reservation old ∈ (network.allocation.peers peer).received))
    (fun a b => decide (NotionCoreReconstruction.Ascending a b))
  change (NotionCoreReconstruction.transactions network peer).Perm _ at oldPerm
  have move : (tx :: NotionCoreReconstruction.transactions network peer).Perm
      (NotionCoreReconstruction.transactions network peer ++ [tx]) := by
    simpa using (List.perm_middle (a := tx) (l₁ := NotionCoreReconstruction.transactions network peer) (l₂ := [])).symm
  have permutation : (NotionCoreReconstruction.transactions next peer).Perm
      (NotionCoreReconstruction.transactions network peer ++ [tx]) :=
    newPerm.trans ((oldPerm.cons tx).symm.trans move)
  have oldOrdered := NotionCoreReconstruction.transactions_ordered network reachable peer
  have nextOrdered := NotionCoreReconstruction.transactions_ordered next nextReach peer
  have ordered : (NotionCoreReconstruction.transactions network peer ++ [tx]).Pairwise
      (fun a b => NotionRunAllocation.Before a.id b.id) := by
    apply List.pairwise_append.mpr
    refine ⟨oldOrdered,by simp,?_⟩
    intro old member fresh single
    have same := List.mem_singleton.mp single
    subst fresh
    obtain ⟨entry,archived,entryEq,received⟩ := NotionCoreReconstruction.transactions_received network peer old member
    have bounded := NotionRunAllocation.reachable_bounded
      (NotionCoreIssuance.allocation_reachable (NotionCorePayloadNetwork.forget_reachable reachable)) peer
    have contained : (NotionCorePayload.reservation old).Contains old.id :=
      ⟨0,NotionCorePayload.width_positive old.payload,by simp [NotionCorePayload.reservation,NotionRunAllocation.Run.at]⟩
    have counter := NotionRunAllocation.received_before_reservation bounded received contained peer payload.width
    exact Or.inl (by simpa only [idEq] using counter)
  exact permutation.eq_of_pairwise (fun _ _ _ _ forward reverse =>
    False.elim (NotionCoreSourceInvariant.before_asymm forward reverse)) nextOrdered ordered

private theorem insert_preparation_kind (state : State) (block : BlockKey) (index : Nat)
    (atoms : List Nat) (payload : NotionCorePayload.Payload)
    (prepared : prepareInsert state block index atoms = some payload) :
    ∃ inst origin, payload = .insert block inst origin atoms := by
  cases empty : atoms.isEmpty with
  | true => simp [prepareInsert,empty] at prepared
  | false =>
    cases located : locateAddress state block index with
    | none => simp [prepareInsert,empty,located] at prepared
    | some address =>
      cases decoded : decodeAddress address with
      | none => simp [prepareInsert,empty,located,decoded] at prepared
      | some pair =>
        rcases pair with ⟨inst,origin⟩
        exact ⟨inst,origin,by simpa [prepareInsert,empty,located,decoded] using prepared.symm⟩

/-- An actual honestly issued insertion has the requested local effect in the
issuer's newly reconstructed document. Appending after the received version
is proved from the real allocator and archive, not supplied as an order guard. -/
theorem issued_insert_effect (network nextNetwork : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (block : BlockKey) (index : Nat) (atoms : List Nat)
    (issued : NotionCoreMachineNetwork.issue network peer (.insert block index atoms) = some nextNetwork)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (before ++ source :: afterBlocks))
    (name : source.id = blockName block) :
    (NotionCoreReconstruction.reconstruct nextNetwork peer >>= render) =
      some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
        [(source.id,(NotionCoreSpec.text source.project.slots).take index ++ atoms ++
          (NotionCoreSpec.text source.project.slots).drop index)] ++
        NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  have nextReach : NotionCoreMachineNetwork.Reach nextNetwork := .request peer (.insert block index atoms) reachable issued
  cases empty : atoms.isEmpty with
  | true => simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,empty] at issued
  | false =>
    cases selected : prepareInsert state block index atoms with
    | none => simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,empty,
        reconstructed,NotionCoreMachineNetwork.prepareRequest,selected] at issued
    | some payload =>
      cases reserved : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget network) peer payload with
      | none => simp [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,empty,
          reconstructed,NotionCoreMachineNetwork.prepareRequest,selected,reserved] at issued
      | some tx =>
        have networkEq : NotionCorePayloadNetwork.emit network peer payload tx = nextNetwork := by
          simpa [NotionCoreMachineNetwork.issue,NotionCoreMachineNetwork.Request.earlyNoop,empty,
            reconstructed,NotionCoreMachineNetwork.prepareRequest,selected,reserved] using issued
        obtain ⟨inst,origin,payloadEq⟩ := insert_preparation_kind state block index atoms payload selected
        have actualPayload := NotionCorePayloadNetwork.prepared_payload reserved
        have txPayload : tx.payload = .insert block inst origin atoms := actualPayload.trans payloadEq
        have nextOrder := emitted_transactions_append network
          (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
          peer payload tx reserved (by rw [networkEq]; exact
            NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable nextReach))
        rw [networkEq] at nextOrder
        have position : NotionCoreReconstruction.transactions nextNetwork peer =
            NotionCoreReconstruction.transactions network peer ++ tx :: [] := by simpa using nextOrder
        obtain ⟨next,after,transaction,extracted,rendered⟩ := canonical_prepared_insert_effect nextNetwork nextReach peer
          (NotionCoreReconstruction.transactions network peer) [] tx position state reconstructed before afterBlocks source
          materialized block inst name index origin atoms txPayload (by simpa only [actualPayload] using selected)
        have nextReplay : NotionCoreReconstruction.reconstruct nextNetwork peer = some next := by
          unfold NotionCoreReconstruction.reconstruct
          rw [nextOrder,replay_append]
          have oldReplay : replay {} (NotionCoreReconstruction.transactions network peer) = some state := reconstructed
          simp [oldReplay,replay,transaction,Bind.bind,Option.bind]
        simp [nextReplay,rendered]

/-- Valid nonempty honest requests issue successfully and have the exact
local insertion effect; issuance, ordering, and the resulting rendering are
all conclusions. Bounds use source visible iterator-atom positions. -/
theorem honest_insert_request_effect (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session)
    (state : State) (reconstructed : NotionCoreReconstruction.reconstruct network peer = some state)
    (before afterBlocks : NotionCoreSourceDocument.Document) (source : Block)
    (materialized : materializeDocument state = some (before ++ source :: afterBlocks))
    (block : BlockKey) (name : source.id = blockName block) (alive : source.alive = true)
    (index : Nat) (atoms : List Nat)
    (nonempty : atoms ≠ []) (bound : index ≤ NotionCoreMachineDeleteTotal.visibleLength state block) :
    ∃ nextNetwork, NotionCoreMachineNetwork.issue network peer (.insert block index atoms) = some nextNetwork ∧
      (NotionCoreReconstruction.reconstruct nextNetwork peer >>= render) =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project before) ++
          [(source.id,(NotionCoreSpec.text source.project.slots).take index ++ atoms ++
            (NotionCoreSpec.text source.project.slots).drop index)] ++
          NotionCoreSpec.view (NotionCoreSourceDocument.project afterBlocks)) := by
  have slices := document_block_slices state _ materialized source (by simp) alive block name
  have stored : ∃ found ∈ state.forest, found.id = blockName block := by
    cases found : state.forest.find? (fun old => old.id == blockName block) with
    | none => simp [blockSlices,found] at slices
    | some entry => exact ⟨entry,List.mem_of_find?_eq_some found,by simpa using List.find?_some found⟩
  obtain ⟨next,issued,_⟩ := NotionCoreMachineClientTotal.honest_issue_insert network reachable peer block index atoms nonempty
    (by simpa [reconstructed] using stored) (by simpa [reconstructed] using bound)
  exact ⟨next,issued,issued_insert_effect network next reachable peer block index atoms issued state reconstructed
    before afterBlocks source materialized name⟩

#print axioms emitted_transactions_append
#print axioms issued_insert_effect
#print axioms honest_insert_request_effect

namespace SPOT
private def cutId : NotionRunAllocation.Id := ⟨3,[65]⟩
private def afterInsert : Option (List (Nat × List Nat)) := do
  let state ← replay {} [NotionCorePayload.bootstrap [97,98],⟨cutId,.split .initial .initial (.item ⟨1,[65]⟩)⟩]
  let payload ← prepareInsert state (.issued cutId) 0 [88]
  match payload with
  | .insert block inst origin atoms => applyOperation state (.insert block inst ⟨4,[65]⟩ origin atoms) >>= render
  | _ => none
/-- Actual preparation and insertion at an inherited leaf's zero gap yield
 a | Xb. Its empty dead title cannot redirect X into the preceding block or end. -/
theorem attached_zero_control :
    afterInsert = some [(0,[97]),(blockName (.issued cutId),[88,98])] ∧
    afterInsert ≠ some [(0,[97,88]),(blockName (.issued cutId),[98])] ∧
    afterInsert ≠ some [(0,[97]),(blockName (.issued cutId),[98,88])] := by decide +kernel
end SPOT
end Sal.MRDTs.Instances.NotionCoreMachineInsertEffects
