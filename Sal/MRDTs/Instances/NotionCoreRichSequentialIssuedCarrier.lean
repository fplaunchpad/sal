import Sal.MRDTs.Instances.NotionCoreRichSequentialSelection

/-! The locally issued formatting effect is an actual update/query of the
finite carrier. Receipt bounds derive the new transaction's position after
all old canonical transactions; no source-state image or desired query is
assumed. -/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.IssuedCarrier
open Sal.MRDTs.Foundation
open NotionCoreRichPayload (Transaction Part)
open NotionCoreRichSequential.Refinement (Related)
open NotionCoreRichProtocolCarrier (D carrierFor)

/-- The actual next allocator reservation determines this complete payload's
header. The source caller supplies parts and its already-chosen Boolean. -/
def issuedFormat (network : NotionCoreRichProtocolNetwork.State) (session : NotionRunAllocation.Session)
    (parts : List Part) (value : Bool) : Transaction :=
  ⟨(NotionRunAllocation.reserve (network.allocation.peers session) session
    (NotionCoreRichPayload.Payload.format parts value).width).first,.format parts value⟩

def formatted (actual : NotionCoreAtomicFormattingMachine.State)
    (network : NotionCoreRichProtocolNetwork.State) (session : NotionRunAllocation.Session)
    (parts : List Part) (value : Bool) : NotionCoreAtomicFormattingMachine.State :=
  {actual with batches := actual.batches ++
    [NotionCoreAtomicFormatting.Batch.ofFormat (issuedFormat network session parts value).id parts value]}

/-- Every complete received transaction header precedes the next reservation,
including edit transactions and formatting batches. -/
theorem received_before_reserve (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (payload : NotionCoreRichPayload.Payload) (transaction : Transaction)
    (present : transaction ∈ NotionCoreRichProtocolNetwork.receivedTransactions network session) :
    NotionRunAllocation.Before transaction.id
      (NotionRunAllocation.reserve (network.allocation.peers session) session payload.width).first := by
  obtain ⟨entry,selected,same⟩ := List.mem_map.mp present
  subst transaction
  have entryReceived : entry.transaction.reservation ∈ (network.allocation.peers session).received := by
    simpa only [List.contains_iff_mem] using (List.mem_filter.mp selected).2
  have positive := NotionCoreRichProtocolNetwork.width_positive entry.transaction.payload
  apply Or.inl
  exact NotionRunAllocation.received_before_reservation
    (NotionRunAllocation.reachable_bounded (NotionCoreRichProtocolNetwork.allocation_reachable reachable) session)
    entryReceived ⟨0,positive,by simp [NotionRunAllocation.Run.at,Transaction.reservation]⟩ session payload.width

/-- Finite-store insertion enumerates as the old canonical receipt sequence
followed by exactly this whole new format transaction. -/
theorem transactions_update (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (parts : List Part) (value : Bool) (time : Timestamp) (replica : Replica) :
    NotionCoreRichProtocolCarrier.transactions
      (D.update (carrierFor network session) (time,replica,issuedFormat network session parts value)) =
      NotionCoreRichPayload.sort (NotionCoreRichProtocolNetwork.receivedTransactions network session) ++
        [issuedFormat network session parts value] := by
  let old := NotionCoreRichPayload.sort (NotionCoreRichProtocolNetwork.receivedTransactions network session)
  let next := issuedFormat network session parts value
  have ordered : (old ++ [next]).Pairwise (fun a b => NotionRunAllocation.Before a.id b.id) := by
    apply List.pairwise_append.mpr
    refine ⟨NotionCoreRichPayload.sort_ordered _
      (NotionCoreRichProtocolNetwork.received_keys_unique reachable session),by simp,?_⟩
    intro a member b newMember
    have same : b = next := by simpa using newMember
    subst b
    exact received_before_reserve network reachable session (.format parts value) a
      ((NotionCoreRichPayload.sort_perm _).mem_iff.mp member)
  have carrier : D.update (carrierFor network session) (time,replica,next) = (old ++ [next]).toFinset := by
    rw [NotionCoreRichProtocolCarrier.update_payload]
    apply Finset.ext
    intro tx
    simp only [carrierFor,Finset.mem_insert,List.mem_toFinset,List.mem_append,List.mem_singleton]
    have kept := (NotionCoreRichPayload.sort_perm
      (NotionCoreRichProtocolNetwork.receivedTransactions network session)).mem_iff (a := tx)
    change (tx = next ∨ tx ∈ NotionCoreRichProtocolNetwork.receivedTransactions network session) ↔
      tx ∈ old ∨ tx = next
    rw [kept]
    tauto
  rw [carrier,NotionCoreRichProtocolCarrier.transactions_of_sorted _ ordered]

private theorem replay_append (state : NotionCoreAtomicFormattingMachine.State)
    (left right : List Transaction) :
    NotionCoreAtomicFormattingMachine.replay state (left ++ right) =
      (NotionCoreAtomicFormattingMachine.replay state left >>= fun next =>
        NotionCoreAtomicFormattingMachine.replay next right) := by
  induction left generalizing state with
  | nil => rfl
  | cons transaction rest ih =>
    simp only [List.cons_append,NotionCoreAtomicFormattingMachine.replay]
    cases one : NotionCoreAtomicFormattingMachine.applyTransaction state transaction <;> simp [ih]

/-- This is the real finite-carrier update and query. Its successful old
reconstruction and the allocator determine the entire new source replay. -/
theorem query_update (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (parts : List Part) (value : Bool) (time : Timestamp) (replica : Replica) :
    D.query (D.update (carrierFor network session)
      (time,replica,issuedFormat network session parts value)) () =
      (NotionCoreAtomicFormattingMachine.render (formatted actual network session parts value)).map
        NotionCoreRichProtocolCarrier.neutral := by
  change NotionCoreRichProtocolCarrier.observe _ = _
  rw [NotionCoreRichProtocolCarrier.observe,transactions_update network reachable session parts value time replica,
    replay_append]
  have oldReplay : NotionCoreAtomicFormattingMachine.replay {}
      (NotionCoreRichPayload.sort (NotionCoreRichProtocolNetwork.receivedTransactions network session)) = some actual :=
    reconstructed
  rw [oldReplay]
  simp [NotionCoreAtomicFormattingMachine.replay,NotionCoreAtomicFormattingMachine.applyTransaction,
    issuedFormat,formatted]

/-- A mark-only update preserves successful rendering. This is derived from
the old related document, rather than assuming a successful new observation. -/
theorem formatted_render_total (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (network : NotionCoreRichProtocolNetwork.State)
    (session : NotionRunAllocation.Session) (parts : List Part) (value : Bool) :
    ∃ raw, NotionCoreAtomicFormattingMachine.render (formatted actual network session parts value) = some raw := by
  obtain ⟨before,beforeRead,_⟩ := NotionCoreRichSequential.Refinement.render_total_related related
  unfold NotionCoreAtomicFormattingMachine.render at beforeRead
  obtain ⟨base,baseRead,_⟩ := Option.map_eq_some_iff.mp beforeRead
  refine ⟨NotionCoreAtomicFormattingMachine.markDocument (formatted actual network session parts value) base,?_⟩
  change (NotionCoreFormattingMachine.render (NotionCoreAtomicFormattingMachine.plainState actual)).map _ = _
  rw [baseRead]
  rfl

/-- All three rich fields survive the carrier's neutral projection, and every
returned Boolean is the actual post-update address read. -/
theorem render_flags (actual : NotionCoreAtomicFormattingMachine.State)
    (raw : NotionCoreAtomicFormattingMachine.View)
    (rendered : NotionCoreAtomicFormattingMachine.render actual = some raw) :
    ∀ row ∈ NotionCoreRichProtocolCarrier.neutral raw, ∀ char ∈ row.2,
      char.bold = NotionCoreAtomicFormattingMachine.boldAt actual char.address := by
  unfold NotionCoreAtomicFormattingMachine.render at rendered
  obtain ⟨base,_,same⟩ := Option.map_eq_some_iff.mp rendered
  subst raw
  intro row member char inside
  simp only [NotionCoreRichProtocolCarrier.neutral,NotionCoreAtomicFormattingMachine.markDocument,
    List.map_map,Function.comp_def,NotionCoreAtomicFormattingMachine.markAtom] at member
  obtain ⟨baseRow,_,rfl⟩ := List.mem_map.mp member
  obtain ⟨atom,_,rfl⟩ := List.mem_map.mp inside
  rfl

/-- The actual finite-carrier update returns a successful complete rich view,
whose flags are the exact whole-selection issuer effect. The client supplies
only the request; identity, Boolean, coverage, order and freshness are derived. -/
theorem format_update_effect (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (related : Related actual abstract) (block : NotionCorePayload.BlockKey) (start stop : Nat)
    (parts : List Part) (value : Bool)
    (prepared : NotionCoreRichProtocolNetwork.formatPayload actual block start stop = some (.format parts value))
    (time : Timestamp) (replica : Replica) :
    ∃ raw rich,
      D.query (D.update (carrierFor network session)
        (time,replica,issuedFormat network session parts value)) () = some (NotionCoreRichProtocolCarrier.neutral raw) ∧
      NotionCoreAtomicFormattingMachine.render (formatted actual network session parts value) = some raw ∧
      Selection.selectRich abstract (NotionCoreMachine.blockName block) start stop = some rich ∧ rich ≠ [] ∧
      value = !(rich.all (·.bold)) ∧
      (∀ row ∈ NotionCoreRichProtocolCarrier.neutral raw, ∀ char ∈ row.2,
        char.bold = NotionCoreAtomicFormattingMachine.boldAt (formatted actual network session parts value) char.address) ∧
      ∀ shown ∈ abstract.document, shown.alive = true → ∀ slot ∈ shown.slots, slot.visible = true →
        NotionCoreAtomicFormattingMachine.boldAt (formatted actual network session parts value) slot.address =
          if (rich.map (·.address)).contains slot.address then value
          else NotionCoreAtomicFormattingMachine.boldAt actual slot.address := by
  obtain ⟨raw,rendered⟩ := formatted_render_total actual abstract related network session parts value
  obtain ⟨rich,selected,nonempty,ballot,effect⟩ := Selection.formatPayload_issued_effect network reachable session actual
    abstract reconstructed related block start stop parts value prepared
  refine ⟨raw,rich,?_,rendered,selected,nonempty,ballot,render_flags _ _ rendered,effect⟩
  rw [query_update network reachable session actual reconstructed parts value time replica,rendered]
  rfl

#print axioms transactions_update
#print axioms query_update
#print axioms format_update_effect

end Sal.MRDTs.Instances.NotionCoreRichSequential.IssuedCarrier
