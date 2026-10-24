import Sal.MRDTs.Instances.NotionCoreRichProtocolNetwork
import Sal.MRDTs.Instances.NotionCoreRichCoreProjection
import Sal.MRDTs.Instances.NotionCoreRichCoreAllocation

/-!
The plain editing projection of the repaired rich caller.

Format transactions are removed from archives and receipt histories, while
their observed counters remain in each clock. The subsequent reachability
proof uses explicit plain clock gaps; no edit is renamed or replaced by a
dummy operation. This module does not assume successful rendering.
-/
namespace Sal.MRDTs.Instances.NotionCoreRichPlainNetwork
open NotionRunAllocation (Id Run Session)
open NotionCoreRichPayload (Transaction)
open NotionCoreRichCoreProjection (project edits)
abbrev RichState := NotionCoreRichProtocolNetwork.State
abbrev RichEntry := NotionCoreRichProtocolNetwork.Entry
abbrev PlainState := NotionCorePayloadNetwork.State
abbrev PlainEntry := NotionCorePayloadNetwork.Entry

def editRuns (state : RichState) : List Run :=
  state.entries.filterMap fun entry => (project entry.transaction).map NotionCorePayload.reservation

def keep (state : RichState) (run : Run) : Bool := (editRuns state).contains run

def eraseEntry (keepRun : Run → Bool) (entry : RichEntry) : Option PlainEntry :=
  (project entry.transaction).map fun plain => ⟨plain,entry.past.filter keepRun⟩

def erase (state : RichState) : PlainState :=
  ⟨NotionCoreRichCoreAllocation.erase (keep state) state.allocation,
    state.entries.filterMap (eraseEntry (keep state))⟩

theorem project_reservation {transaction : Transaction} {plain : NotionCorePayload.Transaction}
    (projected : project transaction = some plain) :
    NotionCorePayload.reservation plain = transaction.reservation := by
  cases transaction with
  | mk id payload =>
    cases payload with
    | edit payload => cases Option.some.inj projected; rfl
    | format parts value => cases projected

theorem keep_iff (state : RichState) (run : Run) :
    keep state run = true ↔ ∃ entry ∈ state.entries,
      ∃ plain, project entry.transaction = some plain ∧ NotionCorePayload.reservation plain = run := by
  simp only [keep,List.contains_iff_mem,editRuns,List.mem_filterMap]
  constructor
  · rintro ⟨entry,member,equal⟩
    obtain ⟨plain,projected,same⟩ := Option.map_eq_some_iff.mp equal
    exact ⟨entry,member,plain,projected,same⟩
  · rintro ⟨entry,member,plain,projected,same⟩
    exact ⟨entry,member,by simp [projected,same]⟩

theorem edit_kept (state : RichState) (entry : RichEntry) (member : entry ∈ state.entries)
    (plain : NotionCorePayload.Transaction) (projected : project entry.transaction = some plain) :
    keep state entry.transaction.reservation = true :=
  (keep_iff state _).mpr ⟨entry,member,plain,projected,project_reservation projected⟩

@[simp] theorem erase_clock (state : RichState) (session : Session) :
    ((erase state).allocation.peers session).clock = (state.allocation.peers session).clock := rfl

theorem erase_receipts (state : RichState) (session : Session) (run : Run) :
    run ∈ ((erase state).allocation.peers session).received ↔
      run ∈ (state.allocation.peers session).received ∧ keep state run = true := by
  exact List.mem_filter

private theorem erased_transactions (keepRun : Run → Bool) (entries : List RichEntry) :
    ((entries.filterMap (eraseEntry keepRun)).map NotionCorePayloadNetwork.Entry.tx) =
      edits (entries.map NotionCoreRichProtocolNetwork.Entry.transaction) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases projected : project entry.transaction with
    | none => simp [eraseEntry,edits,projected,ih]
    | some plain => simp [eraseEntry,edits,projected,ih]

theorem erase_transactions (state : RichState) :
    ((erase state).entries.map NotionCorePayloadNetwork.Entry.tx) = edits (state.entries.map NotionCoreRichProtocolNetwork.Entry.transaction) :=
  erased_transactions (keep state) state.entries

theorem erase_entry_member (state : RichState) (plainEntry : PlainEntry) :
    plainEntry ∈ (erase state).entries ↔ ∃ entry ∈ state.entries,
      ∃ plain, project entry.transaction = some plain ∧
        plainEntry = ⟨plain,entry.past.filter (keep state)⟩ := by
  simp only [erase,List.mem_filterMap,eraseEntry]
  constructor
  · rintro ⟨entry,member,equal⟩
    obtain ⟨plain,projected,same⟩ := Option.map_eq_some_iff.mp equal
    exact ⟨entry,member,plain,projected,same.symm⟩
  · rintro ⟨entry,member,plain,projected,rfl⟩
    exact ⟨entry,member,by simp [projected]⟩

private theorem received_edits_list (entries : List RichEntry) (receipts : List Run)
    (keepRun : Run → Bool)
    (kept : ∀ entry ∈ entries, ∀ payload,
      entry.transaction.payload = .edit payload → keepRun entry.transaction.reservation = true) :
    (((entries.filterMap (eraseEntry keepRun)).map NotionCorePayloadNetwork.Entry.tx).filter
      (fun tx => NotionCorePayload.reservation tx ∈ receipts.filter keepRun)) =
      edits ((entries.filter (fun entry => receipts.contains entry.transaction.reservation)).map
        NotionCoreRichProtocolNetwork.Entry.transaction) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    have tail : ∀ entry ∈ rest, ∀ payload,
        entry.transaction.payload = .edit payload → keepRun entry.transaction.reservation = true :=
      fun entry member payload same => kept entry (by simp [member]) payload same
    cases entry with
    | mk transaction past =>
      cases transaction with
      | mk id payload =>
        cases payload with
        | format parts value =>
          by_cases received : (⟨id,.format parts value⟩ : Transaction).reservation ∈ receipts <;>
            simpa [eraseEntry,edits,project,received] using ih tail
        | edit payload =>
          have first : keepRun (⟨id,.edit payload⟩ : Transaction).reservation = true :=
            kept ⟨⟨id,.edit payload⟩,past⟩ (by simp) payload rfl
          have sameRun : (⟨id,.edit payload⟩ : Transaction).reservation =
              NotionCorePayload.reservation ⟨id,payload⟩ := rfl
          rw [sameRun] at first
          by_cases received : NotionCorePayload.reservation ⟨id,payload⟩ ∈ receipts <;>
            simpa [eraseEntry,edits,project,sameRun,received,first] using ih tail

theorem received_edits (state : RichState) (session : Session) :
    (((erase state).entries.map NotionCorePayloadNetwork.Entry.tx).filter
      (fun tx => NotionCorePayload.reservation tx ∈ ((erase state).allocation.peers session).received)) =
      edits (NotionCoreRichProtocolNetwork.receivedTransactions state session) := by
  apply received_edits_list
  intro entry member payload same
  apply edit_kept state entry member ⟨entry.transaction.id,payload⟩
  simp [project,same]

end Sal.MRDTs.Instances.NotionCoreRichPlainNetwork
