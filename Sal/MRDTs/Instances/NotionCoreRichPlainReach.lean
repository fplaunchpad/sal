import Sal.MRDTs.Instances.NotionCoreRichPlainNetwork
import Sal.MRDTs.Instances.NotionCoreMachineNetwork
import Sal.MRDTs.Instances.NotionCoreRichProtocolEvents

/-! Reachable repaired rich callers project to the existing plain caller.
Formatting consumes source IDs and projects to clock gaps, rather than dummy
edits or renamed transactions. Rendered-state correspondence is derived from
the two actual transaction enumerations and their checked unique source IDs.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichPlainReach
open NotionRunAllocation (Id Run Session)
open NotionCoreRichPayload (Transaction Payload)
open NotionCoreRichCoreProjection (project edits)
open NotionCoreRichPlainNetwork (erase keep eraseEntry)
abbrev RichState := NotionCoreRichProtocolNetwork.State
abbrev PlainState := NotionCorePayloadNetwork.State

private theorem plain_ext {left right : PlainState}
    (allocation : left.allocation = right.allocation) (entries : left.entries = right.entries) : left = right := by
  cases left
  cases right
  cases allocation
  cases entries
  rfl

private theorem allocation_ext {left right : NotionRunAllocation.Network}
    (peers : left.peers = right.peers) (published : left.published = right.published) : left = right := by
  cases left
  cases right
  cases peers
  cases published
  rfl

theorem transactions_eq (state : RichState)
    (richReach : NotionCoreRichProtocolNetwork.Reach state)
    (plainReach : NotionCoreMachineNetwork.Reach (erase state)) (session : Session) :
    NotionCoreReconstruction.transactions (erase state) session =
      edits (NotionCoreRichPayload.sort (NotionCoreRichProtocolNetwork.receivedTransactions state session)) := by
  have plainPayload := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable plainReach)
  have leftOrdered := NotionCoreReconstruction.transactionsFor_ordered (erase state) plainPayload
    ((erase state).allocation.peers session).received
  have rightOrdered := NotionCoreRichCoreProjection.edits_ordered
    (NotionCoreRichProtocolNetwork.receivedTransactions state session)
    (NotionCoreRichProtocolNetwork.received_keys_unique richReach session)
  have leftPerm : (NotionCoreReconstruction.transactions (erase state) session).Perm
      (edits (NotionCoreRichProtocolNetwork.receivedTransactions state session)) := by
    unfold NotionCoreReconstruction.transactions
    rw [NotionCoreRichPlainNetwork.received_edits]
    exact List.mergeSort_perm _ _
  have rightPerm := NotionCoreRichCoreProjection.edits_perm
    (NotionCoreRichPayload.sort_perm (NotionCoreRichProtocolNetwork.receivedTransactions state session))
  exact (leftPerm.trans rightPerm.symm).eq_of_pairwise
    (fun _ _ _ _ forward reverse => False.elim (NotionCoreSourceInvariant.before_asymm forward reverse))
    leftOrdered rightOrdered

theorem eraseFormats_eq (transactions : List Transaction) :
    NotionCoreAtomicFormattingMachine.eraseFormats transactions = edits transactions := by
  induction transactions with
  | nil => rfl
  | cons transaction rest ih =>
    cases transaction with
    | mk id payload => cases payload <;>
        simp [NotionCoreAtomicFormattingMachine.eraseFormats,edits,project,ih]

theorem reconstruct_core_of_reach (state : RichState)
    (richReach : NotionCoreRichProtocolNetwork.Reach state)
    (plainReach : NotionCoreMachineNetwork.Reach (erase state)) (session : Session) :
    (NotionCoreRichProtocolNetwork.reconstruct state session).map NotionCoreAtomicFormattingMachine.State.core =
      NotionCoreReconstruction.reconstruct (erase state) session := by
  unfold NotionCoreRichProtocolNetwork.reconstruct NotionCoreReconstruction.reconstruct
  rw [NotionCoreAtomicFormattingMachine.replay_core_projection,eraseFormats_eq,
    transactions_eq state richReach plainReach session]

def exchangeGap (state : RichState) (target source : Session) : Nat :=
  NotionCoreRichCoreAllocation.importedClock (state.allocation.peers target).clock
      (state.allocation.peers source).received -
    NotionCoreRichCoreAllocation.importedClock (state.allocation.peers target).clock
      ((state.allocation.peers source).received.filter (keep state))

theorem erase_exchange (state : RichState) (target source : Session) :
    erase (NotionCoreRichProtocolNetwork.exchange state target source) =
      NotionCorePayloadNetwork.gap (NotionCorePayloadNetwork.exchange (erase state) target source)
        target (exchangeGap state target source) := by
  apply plain_ext
  · exact NotionCoreRichCoreAllocation.erase_import (keep state) state.allocation target
      (state.allocation.peers source).received
  · rfl

theorem keep_emit_old (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) (payload : Payload) (run : Run) (published : run ∈ state.allocation.published) :
    keep (NotionCoreRichProtocolNetwork.emit state session payload) run = keep state run := by
  apply Bool.eq_iff_iff.mpr
  rw [NotionCoreRichPlainNetwork.keep_iff,NotionCoreRichPlainNetwork.keep_iff]
  constructor
  · rintro ⟨entry,member,plain,projected,sameRun⟩
    simp only [NotionCoreRichProtocolNetwork.emit,NotionCoreRichProtocolNetwork.publish,List.mem_cons] at member
    rcases member with rfl | member
    · have same := (NotionCoreRichPlainNetwork.project_reservation projected).symm.trans sameRun
      have fresh := NotionRunAllocation.fresh_transaction_key
        (NotionCoreRichProtocolNetwork.allocation_reachable reachable) published session payload.width
      exact False.elim (fresh (congrArg Run.first same))
    · exact ⟨entry,member,plain,projected,sameRun⟩
  · rintro ⟨entry,member,plain,projected,sameRun⟩
    exact ⟨entry,List.mem_cons_of_mem _ member,plain,projected,sameRun⟩

theorem filter_emit_frame (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) (payload : Payload) (runs : List Run)
    (supported : ∀ run ∈ runs, run ∈ state.allocation.published) :
    runs.filter (keep (NotionCoreRichProtocolNetwork.emit state session payload)) = runs.filter (keep state) := by
  apply List.filter_congr
  intro run member
  exact keep_emit_old state reachable session payload run (supported run member)

theorem erase_entries_frame (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) (payload : Payload) :
    state.entries.filterMap (eraseEntry (keep (NotionCoreRichProtocolNetwork.emit state session payload))) =
      state.entries.filterMap (eraseEntry (keep state)) := by
  apply List.filterMap_congr
  intro entry member
  have past := filter_emit_frame state reachable session payload entry.past
    (NotionCoreRichProtocolNetwork.entry_provenance reachable entry member).2
  simp only [eraseEntry]
  rw [past]

theorem erase_allocation_frame (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) (payload : Payload) :
    NotionCoreRichCoreAllocation.erase (keep (NotionCoreRichProtocolNetwork.emit state session payload)) state.allocation =
      NotionCoreRichCoreAllocation.erase (keep state) state.allocation := by
  apply allocation_ext
  · funext peer
    have received := filter_emit_frame state reachable session payload (state.allocation.peers peer).received
      (fun run member => NotionRunAllocation.reachable_received_published
        (NotionCoreRichProtocolNetwork.allocation_reachable reachable) peer run member)
    change (⟨_,_⟩ : NotionRunAllocation.Peer) = ⟨_,_⟩
    rw [received]
  · exact filter_emit_frame state reachable session payload state.allocation.published (fun _ h => h)

def plainDraft (state : RichState) (session : Session) (payload : NotionCorePayload.Payload) :
    NotionCorePayload.Transaction :=
  ⟨(NotionRunAllocation.reserve (state.allocation.peers session) session payload.width).first,payload⟩

theorem erase_emit_edit (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) (payload : NotionCorePayload.Payload) :
    erase (NotionCoreRichProtocolNetwork.emit state session (.edit payload)) =
      NotionCorePayloadNetwork.emit (erase state) session payload (plainDraft state session payload) := by
  let next := NotionCoreRichProtocolNetwork.emit state session (.edit payload)
  have kept : keep next (NotionRunAllocation.reserve (state.allocation.peers session) session payload.width) = true := by
    apply (NotionCoreRichPlainNetwork.keep_iff next _).mpr
    refine ⟨⟨⟨(NotionRunAllocation.reserve (state.allocation.peers session) session payload.width).first,
      .edit payload⟩,(state.allocation.peers session).received⟩,List.mem_cons_self,
      plainDraft state session payload,rfl,rfl⟩
  apply plain_ext
  · change NotionCoreRichCoreAllocation.erase (keep next)
        (NotionRunAllocation.issue state.allocation session payload.width) =
      NotionRunAllocation.issue (erase state).allocation session payload.width
    rw [NotionCoreRichCoreAllocation.erase_issue_kept _ _ _ _ kept,
      erase_allocation_frame state reachable session (.edit payload)]
    rfl
  · have receipts := filter_emit_frame state reachable session (.edit payload)
      (state.allocation.peers session).received
      (fun run member => NotionRunAllocation.reachable_received_published
        (NotionCoreRichProtocolNetwork.allocation_reachable reachable) session run member)
    have old := erase_entries_frame state reachable session (.edit payload)
    change (⟨plainDraft state session payload,(state.allocation.peers session).received.filter (keep next)⟩ ::
      state.entries.filterMap (eraseEntry (keep next))) =
        ⟨plainDraft state session payload,(state.allocation.peers session).received.filter (keep state)⟩ ::
          state.entries.filterMap (eraseEntry (keep state))
    rw [receipts,old]

theorem new_run_not_kept (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) (payload : Payload) :
    keep state (NotionRunAllocation.reserve (state.allocation.peers session) session payload.width) = false := by
  apply Bool.eq_false_iff.mpr
  intro kept
  obtain ⟨entry,member,plain,projected,sameRun⟩ := (NotionCoreRichPlainNetwork.keep_iff state _).mp kept
  have published : entry.transaction.reservation ∈ state.allocation.published := by
    rw [← NotionCoreRichProtocolNetwork.archive_runs reachable]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  have oldNew := (NotionCoreRichPlainNetwork.project_reservation projected).symm.trans sameRun
  exact (NotionRunAllocation.fresh_transaction_key
    (NotionCoreRichProtocolNetwork.allocation_reachable reachable) published session payload.width)
      (congrArg Run.first oldNew.symm)

theorem keep_emit_format (state : RichState) (session : Session)
    (parts : List NotionCoreRichPayload.Part) (value : Bool) :
    keep (NotionCoreRichProtocolNetwork.emit state session (.format parts value)) = keep state := by
  funext run
  simp [keep,NotionCoreRichPlainNetwork.editRuns,NotionCoreRichProtocolNetwork.emit,
    NotionCoreRichProtocolNetwork.publish,project]

theorem erase_emit_format (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) (parts : List NotionCoreRichPayload.Part) (value : Bool) :
    erase (NotionCoreRichProtocolNetwork.emit state session (.format parts value)) =
      NotionCorePayloadNetwork.gap (erase state) session (Payload.format parts value).width := by
  apply plain_ext
  · change NotionCoreRichCoreAllocation.erase
        (keep (NotionCoreRichProtocolNetwork.emit state session (.format parts value)))
        (NotionRunAllocation.issue state.allocation session (Payload.format parts value).width) = _
    rw [keep_emit_format]
    exact NotionCoreRichCoreAllocation.erase_issue_omitted (keep state) state.allocation session _
      (NotionCoreRichProtocolNetwork.width_positive _) (new_run_not_kept state reachable session _)
  · change (eraseEntry (keep (NotionCoreRichProtocolNetwork.emit state session (.format parts value)))
        ⟨⟨(NotionRunAllocation.reserve (state.allocation.peers session) session
          (Payload.format parts value).width).first,.format parts value⟩,
          (state.allocation.peers session).received⟩).toList ++
        state.entries.filterMap (eraseEntry (keep (NotionCoreRichProtocolNetwork.emit state session (.format parts value)))) = _
    rw [keep_emit_format]
    rfl

theorem prepared_not_bootstrap (state : NotionCoreMachine.State)
    (request : NotionCoreMachineNetwork.Request) (payload : NotionCorePayload.Payload)
    (prepared : NotionCoreMachineNetwork.prepareRequest state request = some payload) :
    ∀ atoms, payload ≠ .bootstrap atoms := by
  intro atoms equal
  subst payload
  cases request with
  | create after =>
      cases after <;> simp [NotionCoreMachineNetwork.prepareRequest,
        NotionCoreMachineClient.prepareCreate] at prepared
  | insert block index text =>
      simp [NotionCoreMachineNetwork.prepareRequest,NotionCoreMachineClient.prepareInsert,
        Option.bind_eq_some_iff] at prepared
  | split block index =>
      simp [NotionCoreMachineNetwork.prepareRequest,NotionCoreMachineClient.prepareSplit,
        Option.bind_eq_some_iff] at prepared
  | erase block start stop =>
      obtain ⟨groups,equal⟩ := NotionCoreMachineDelete.selectErase_kind state block start stop _ prepared
      cases equal
  | merge source =>
      obtain ⟨_,inst,stop,last,equal,_⟩ := NotionCoreMachineClient.prepareMerge_some state source _ prepared
      cases equal

theorem plain_issue_prepared (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (plainReach : NotionCoreMachineNetwork.Reach (erase state)) (session : Session)
    (current : NotionCoreAtomicFormattingMachine.State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct state session = some current)
    (request : NotionCoreMachineNetwork.Request) (payload : NotionCorePayload.Payload)
    (nonempty : request.earlyNoop = false)
    (prepared : NotionCoreMachineNetwork.prepareRequest current.core request = some payload)
    (emits : payload.emits = true) :
    NotionCoreMachineNetwork.issue (erase state) session request =
      some (NotionCorePayloadNetwork.emit (erase state) session payload (plainDraft state session payload)) := by
  have projection := reconstruct_core_of_reach state reachable plainReach session
  have plainReconstruction : NotionCoreReconstruction.reconstruct (erase state) session = some current.core := by
    rw [reconstructed] at projection
    exact projection.symm
  have ordinary := prepared_not_bootstrap current.core request payload prepared
  have reservation : NotionCorePayload.prepare (NotionCorePayloadNetwork.forget (erase state)) session payload =
      some (plainDraft state session payload) := by
    cases payload with
    | bootstrap atoms => exact (ordinary atoms rfl).elim
    | _ => simp [NotionCorePayload.prepare,emits,plainDraft,NotionCorePayloadNetwork.forget,
        NotionRunAllocation.reserve]
  simp [NotionCoreMachineNetwork.issue,nonempty,plainReconstruction,prepared,reservation]

theorem erase_seeded (text : List Nat) :
    erase (NotionCoreRichProtocolNetwork.seeded text) = NotionCorePayloadNetwork.seeded text := by
  exact erase_emit_edit NotionCoreRichProtocolNetwork.initial .init [65] (.bootstrap text)

/-- Erasing formats from any actual rich caller execution yields an actual
plain positional-caller execution. Format allocation and receipt clocks become
explicit source clock gaps; all edit payloads and their IDs stay unchanged. -/
theorem erase_reachable {state : RichState} (reachable : NotionCoreRichProtocolNetwork.Reach state) :
    NotionCoreMachineNetwork.Reach (erase state) := by
  induction reachable with
  | init => exact .init
  | bootstrap text => rw [erase_seeded]; exact .bootstrap text
  | @exchange state target source prior ih =>
      rw [erase_exchange]
      exact .gap target _ (.exchange target source ih)
  | @request state next session request prior issued ih =>
      obtain ⟨current,payload,currentEq,payloadEq,known,rfl⟩ :=
        NotionCoreRichProtocolNetwork.issue_data state next session request issued
      cases payload with
      | format parts value =>
          rw [erase_emit_format state prior session parts value]
          exact .gap session _ ih
      | edit payload =>
          rw [erase_emit_edit state prior session payload]
          cases request with
          | toggle block start stop =>
              simp [NotionCoreRichProtocolNetwork.prepare,NotionCoreRichProtocolNetwork.formatPayload,
                Option.bind_eq_some_iff] at payloadEq
          | edit request =>
              simp only [NotionCoreRichProtocolNetwork.prepare] at payloadEq
              split at payloadEq
              · contradiction
              · rename_i noEarly
                obtain ⟨chosen,chosenEq,result⟩ := Option.bind_eq_some_iff.mp payloadEq
                split at result
                · rename_i emitting
                  have same : chosen = payload := by simpa using result
                  subst chosen
                  have nonempty : request.earlyNoop = false := Bool.eq_false_iff.mpr noEarly
                  exact .request session request ih
                    (plain_issue_prepared state prior ih session current currentEq request payload nonempty chosenEq emitting)
                · contradiction

theorem reconstruct_core (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (session : Session) :
    (NotionCoreRichProtocolNetwork.reconstruct state session).map NotionCoreAtomicFormattingMachine.State.core =
      NotionCoreReconstruction.reconstruct (erase state) session :=
  reconstruct_core_of_reach state reachable (erase_reachable reachable) session

theorem version_membership (state : RichState) (runs : List Run)
    (plain : NotionCorePayload.Transaction) :
    plain ∈ NotionCoreReconstruction.transactionsFor (erase state) (runs.filter (keep state)) ↔
      plain ∈ edits (NotionCoreRichProtocolEvents.transactionsFor state runs) := by
  rw [NotionCoreReconstruction.transactionsFor_membership,
    NotionCoreRichCoreProjection.edits_member]
  constructor
  · rintro ⟨⟨plainEntry,member,same⟩,received⟩
    obtain ⟨entry,entryMember,tx,projected,rfl⟩ :=
      (NotionCoreRichPlainNetwork.erase_entry_member state plainEntry).mp member
    change tx = plain at same
    subst tx
    have selected := (List.mem_filter.mp received).1
    refine ⟨entry.transaction,?_,projected⟩
    apply (NotionCoreRichProtocolEvents.transactionsFor_membership state runs _).mpr
    refine ⟨⟨entry,entryMember,rfl⟩,?_⟩
    change entry.transaction.reservation ∈ runs
    rwa [← NotionCoreRichPlainNetwork.project_reservation projected]
  · rintro ⟨transaction,member,projected⟩
    obtain ⟨⟨entry,entryMember,rfl⟩,received⟩ :=
      (NotionCoreRichProtocolEvents.transactionsFor_membership state runs transaction).mp member
    refine ⟨⟨⟨plain,entry.past.filter (keep state)⟩,?_,rfl⟩,?_⟩
    · exact (NotionCoreRichPlainNetwork.erase_entry_member state _).mpr
        ⟨entry,entryMember,plain,projected,rfl⟩
    · apply List.mem_filter.mpr
      have equal := NotionCoreRichPlainNetwork.project_reservation projected
      exact ⟨equal.symm ▸ received,equal.symm ▸
        NotionCoreRichPlainNetwork.edit_kept state entry entryMember plain projected⟩

private theorem ordered_nodup (transactions : List NotionCorePayload.Transaction)
    (ordered : transactions.Pairwise (fun a b => NotionRunAllocation.Before a.id b.id)) : transactions.Nodup := by
  apply ordered.imp
  intro a b before same
  subst b
  exact NotionCoreSourceInvariant.before_irrefl _ before

/-- Arbitrary saved versions keep exactly the same complete edit transactions
in exactly the same source order; no current receipt peer is required. -/
theorem transactionsFor_eq (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (runs : List Run) :
    NotionCoreReconstruction.transactionsFor (erase state) (runs.filter (keep state)) =
      edits (NotionCoreRichProtocolEvents.transactionsFor state runs) := by
  have plainPayload := NotionCoreCreatorNetwork.payload_reachable
    (NotionCoreMachineNetwork.creator_reachable (erase_reachable reachable))
  have leftOrdered := NotionCoreReconstruction.transactionsFor_ordered (erase state) plainPayload (runs.filter (keep state))
  have rightOrdered := NotionCoreRichCoreProjection.edits_pairwise NotionRunAllocation.Before _
    (NotionCoreRichProtocolEvents.transactionsFor_ordered state reachable runs)
  have permutation := (List.perm_ext_iff_of_nodup (ordered_nodup _ leftOrdered)
    (ordered_nodup _ rightOrdered)).mpr (version_membership state runs)
  exact permutation.eq_of_pairwise
    (fun _ _ _ _ forward reverse => False.elim (NotionCoreSourceInvariant.before_asymm forward reverse))
    leftOrdered rightOrdered

/-- Closure of a selected rich version transports to the existing plain
source protocol's captured-past condition, including every historical version. -/
theorem erase_closed (state : RichState) (runs : List Run)
    (closed : NotionCoreRichProtocolEvents.Closed state runs) :
    NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget (erase state)).records (runs.filter (keep state)) := by
  intro record member received old past
  obtain ⟨plainEntry,entryMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨entry,richMember,plain,projected,rfl⟩ :=
    (NotionCoreRichPlainNetwork.erase_entry_member state plainEntry).mp entryMember
  have selected : entry.transaction.reservation ∈ runs := by
    have selected := (List.mem_filter.mp received).1
    change NotionCorePayload.reservation plain ∈ runs at selected
    rwa [NotionCoreRichPlainNetwork.project_reservation projected] at selected
  have prior : old ∈ entry.past ∧ keep state old = true := List.mem_filter.mp past
  exact List.mem_filter.mpr ⟨closed entry richMember selected old prior.1,prior.2⟩

theorem reconstruct_core_version (state : RichState) (reachable : NotionCoreRichProtocolNetwork.Reach state)
    (runs : List Run) :
    (NotionCoreAtomicFormattingMachine.replay {} (NotionCoreRichProtocolEvents.transactionsFor state runs)).map
        NotionCoreAtomicFormattingMachine.State.core =
      NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor (erase state) (runs.filter (keep state))) := by
  rw [NotionCoreAtomicFormattingMachine.replay_core_projection,eraseFormats_eq,
    transactionsFor_eq state reachable runs]

#print axioms erase_reachable
#print axioms reconstruct_core
#print axioms erase_closed
#print axioms transactionsFor_eq

end Sal.MRDTs.Instances.NotionCoreRichPlainReach
