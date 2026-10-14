import Sal.MRDTs.Instances.NotionCoreIssuance
import Sal.MRDTs.Instances.NotionCoreParentMap

/-! Typed core source transactions and their atomic payload expansion.
This is a decoder boundary, not a JavaScript/JSON parser theorem. Text values
are already source iterator atoms, encoded as opaque naturals. Block keys keep
the special bootstrap name separate from generated session/counter names;
their injection into source strings remains separate.
-/
namespace Sal.MRDTs.Instances.NotionCorePayload
open NotionRunAllocation (Id Run)
open NotionCoreOriginTree (Origin Item)
open NotionCoreParentMap (Row)

inductive BlockKey where
  | initial
  | issued (id : Id)
  deriving DecidableEq, Repr

/-- Positional selection has already produced the source's instance and item
identities. Delete IDs are after expansion of the source range encoding. -/
inductive Payload where
  | bootstrap (atoms : List Nat)
  | create (afterBlock : Option BlockKey)
  | insert (block inst : BlockKey) (origin : Origin) (atoms : List Nat)
  | erase (block inst : BlockKey) (targets : List Id)
  | split (block inst : BlockKey) (origin : Origin)
  deriving DecidableEq, Repr

structure Transaction where
  id : Id
  payload : Payload
  deriving DecidableEq, Repr

inductive Operation where
  | create (block : BlockKey) (afterBlock : Option BlockKey)
  | insert (block inst : BlockKey) (first : Id) (origin : Origin) (atoms : List Nat)
  | erase (block inst : BlockKey) (targets : List Id)
  | marker (block inst : BlockKey) (id : Id) (origin : Origin)
  | moveInto (source inst : BlockKey) (marker : Id) (target : BlockKey)
  deriving DecidableEq, Repr

/-- Preserve the actual atomic order. Bootstrap create and insertion share
one transaction key; split creates its target, inserts its marker, then moves
the marker's slice into the new target. Pointer/path/search-label fields do
not affect these core document dispatch branches. Source mapping validation
can still reject duplicate labels; that runtime check is not modeled here. -/
def operations (tx : Transaction) : List Operation := match tx.payload with
  | .bootstrap atoms =>
      [.create .initial none, .insert .initial .initial tx.id .start atoms]
  | .create afterBlock => [.create (.issued tx.id) afterBlock]
  | .insert block inst origin atoms => [.insert block inst tx.id origin atoms]
  | .erase block inst targets => [.erase block inst targets]
  | .split block inst origin =>
      [.create (.issued tx.id) (some block), .marker block inst tx.id origin,
       .moveInto block inst tx.id (.issued tx.id)]

def Payload.itemCount : Payload → Nat
  | .bootstrap atoms | .insert _ _ _ atoms => atoms.length
  | .split _ _ _ => 1
  | .create _ | .erase _ _ _ => 0

def Payload.width (payload : Payload) : Nat := max 1 payload.itemCount

def originReference : Origin → List Id
  | .start => []
  | .item id => [id]

/-- Only external RGA references. The marker referenced by moveInto is born
inside the same atomic transaction. Block creators have separate provenance. -/
def Payload.references : Payload → List Id
  | .insert _ _ origin _ | .split _ _ origin => originReference origin
  | .erase _ _ targets => targets
  | .bootstrap _ | .create _ => []

def reservation (tx : Transaction) : Run := ⟨tx.id, tx.payload.width⟩

def record (tx : Transaction) (past : List Run) : NotionCoreIssuance.Record :=
  ⟨reservation tx, past, tx.payload.references, decide (0 < tx.payload.itemCount)⟩

def offsetId (first : Id) (offset : Nat) : Id :=
  ⟨first.counter + offset, first.session⟩

/-- Source `insertRun` visits its iterator atoms in order and assigns
consecutive IDs. Pending tombstones are read when the item is born. -/
def textItems (first : Id) (atoms : List Nat) (deleted : Id → Bool) : List Item :=
  (List.range atoms.length).map fun index =>
    ⟨offsetId first index, .text atoms[index]! (deleted (offsetId first index))⟩

abbrev Birth := BlockKey × Row

def Operation.births (deleted : BlockKey → Id → Bool) : Operation → List Birth
  | .insert _ inst first origin atoms =>
      (NotionCoreParentMap.runRows origin (textItems first atoms (deleted inst))).map (inst, ·)
  | .marker _ inst id origin => [(inst, ⟨⟨id, .split⟩, origin⟩)]
  | .create _ _ | .erase _ _ _ | .moveInto _ _ _ _ => []

def births (tx : Transaction) (deleted : BlockKey → Id → Bool) : List Birth :=
  (operations tx).flatMap (Operation.births deleted)

def birthId (birth : Birth) : Id := birth.2.item.id

theorem runRows_ids (origin : Origin) (items : List Item) :
    (NotionCoreParentMap.runRows origin items).map (fun row => row.item.id) = items.map Item.id := by
  induction items generalizing origin with
  | nil => rfl
  | cons item rest ih => simp [NotionCoreParentMap.runRows, ih]

theorem textItems_ids (first : Id) (atoms : List Nat) (deleted : Id → Bool) :
    (textItems first atoms deleted).map Item.id = (List.range atoms.length).map (offsetId first) := by
  simp [textItems, List.map_map, Function.comp_def]

/-- The actual expanded operation list produces exactly the allocated item
prefix. The metadata phases add no RGA item and no second reservation. -/
theorem birth_ids (tx : Transaction) (deleted : BlockKey → Id → Bool) :
    (births tx deleted).map birthId =
      (List.range tx.payload.itemCount).map (offsetId tx.id) := by
  cases tx with
  | mk id payload =>
    cases payload <;>
      simp [births, operations, Operation.births, Payload.itemCount, birthId,
        List.map_map, Function.comp_def, runRows_ids, textItems_ids, offsetId]

/-- This supplies the item-production tag used by the issuance proof from
the expanded typed source payload, rather than assuming a free Boolean tag. -/
theorem born_iff_record (tx : Transaction) (past : List Run) (deleted : BlockKey → Id → Bool) (id : Id) :
    id ∈ (births tx deleted).map birthId ↔
      (record tx past).items = true ∧ (record tx past).run.Contains id := by
  rw [birth_ids]
  simp only [List.mem_map, List.mem_range, record, reservation, Run.Contains, Run.at,
    Payload.width, decide_eq_true_eq]
  constructor
  · rintro ⟨offset, within, same⟩
    refine ⟨by omega, offset, ?_, same.symm⟩
    omega
  · rintro ⟨positive, offset, within, same⟩
    refine ⟨offset, ?_, same.symm⟩
    omega

def Operation.clockEnd : Operation → Nat
  | .insert _ _ first _ atoms => first.counter + atoms.length - 1
  | .marker _ _ id _ => id.counter
  | .create _ _ | .erase _ _ _ | .moveInto _ _ _ _ => 0

/-- Literal `transactionClockMax` fold on the typed operation list, including
the transaction ID even when the bootstrap insertion is empty. -/
def clockMax (tx : Transaction) : Nat :=
  (operations tx).foldl (fun maximum op => max maximum op.clockEnd) tx.id.counter

theorem clockMax_reservation (tx : Transaction) : clockMax tx = (reservation tx).last := by
  cases tx with
  | mk id payload =>
    cases payload <;>
      simp [clockMax, operations, Operation.clockEnd, reservation,
        Payload.width, Payload.itemCount, Run.last] <;> omega

/-- The public request API emits no transaction for empty insert/delete.
Bootstrap is a separate factory and still emits its create+empty-insert pair. -/
def Payload.emits : Payload → Bool
  | .insert _ _ _ atoms => !atoms.isEmpty
  | .erase _ _ targets => !targets.isEmpty
  | .bootstrap _ | .create _ | .split _ _ _ => true

def bootstrap (atoms : List Nat) : Transaction := ⟨⟨1, [65]⟩, .bootstrap atoms⟩

/-- The typed client constructor covers already-selected ordinary requests.
Bootstrap is excluded: the source supplies it separately at fixed A@1. -/
def prepare (state : NotionCoreIssuance.State) (session : NotionRunAllocation.Session)
    (payload : Payload) : Option Transaction :=
  match payload with
  | .bootstrap _ => none
  | _ => if payload.emits then
      some ⟨(NotionRunAllocation.reserve (state.allocation.peers session) session payload.width).first, payload⟩
    else none

theorem width_positive (payload : Payload) : 0 < payload.width := by
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)

/-- Prepared nonempty payloads reproduce the exact ghost mint record. The
remaining client-domain premise is actual selection of known item references;
the item-production tag and clock width are no longer independent choices. -/
theorem prepare_record {state : NotionCoreIssuance.State} {session : NotionRunAllocation.Session}
    {payload : Payload} {tx : Transaction} (prepared : prepare state session payload = some tx) :
    record tx (state.allocation.peers session).received =
      ⟨NotionRunAllocation.reserve (state.allocation.peers session) session payload.width,
       (state.allocation.peers session).received, payload.references, decide (0 < payload.itemCount)⟩ := by
  cases payload <;> simp only [prepare] at prepared
  all_goals try contradiction
  all_goals split at prepared <;> simp_all [record, reservation, NotionRunAllocation.reserve]
  all_goals subst tx; simp

/-- Once source selection establishes reference presence, typed payload
preparation is admitted by the existing whole-version issuance relation. -/
theorem prepare_admitted {state : NotionCoreIssuance.State} {session : NotionRunAllocation.Session}
    {payload : Payload} {tx : Transaction} (reachable : NotionCoreIssuance.Reach state)
    (prepared : prepare state session payload = some tx)
    (known : ∀ id ∈ payload.references, NotionCoreIssuance.ItemKnown state session id) :
    NotionCoreIssuance.Reach (NotionCoreIssuance.mint state session payload.width
      (decide (0 < payload.itemCount)) payload.references) ∧
    (NotionCoreIssuance.mint state session payload.width
      (decide (0 < payload.itemCount)) payload.references).records =
        record tx (state.allocation.peers session).received :: state.records := by
  refine ⟨.mint session payload.width _ payload.references reachable (width_positive payload) known, ?_⟩
  rw [prepare_record prepared]
  rfl

/-- PASS+FAIL: nonempty bootstrap is one two-operation transaction, with its
first text item sharing A@1. Create contributes no competing item birth. -/
theorem bootstrap_control :
    (operations (bootstrap [97,98])).length = 2 ∧
    (births (bootstrap [97,98]) (fun _ _ => false)).map birthId = [⟨1,[65]⟩, ⟨2,[65]⟩] ∧
    (births (bootstrap [97,98]) (fun _ _ => false)).map birthId ≠ [⟨2,[65]⟩, ⟨3,[65]⟩] := by decide

/-- Empty bootstrap still consumes/observes A@1 but does not create a dummy
RGA character. Ordinary empty insertion emits no transaction. -/
theorem empty_control :
    clockMax (bootstrap []) = 1 ∧ births (bootstrap []) (fun _ _ => false) = [] ∧
    (record (bootstrap []) []).items ≠ true ∧
    prepare NotionCoreIssuance.initial [66] (.insert .initial .initial .start []) = none := by decide

/-- Split's third operation references its own new marker internally; only
the old origin is an external issuance reference. -/
theorem split_control :
    let tx : Transaction := ⟨⟨3,[66]⟩, .split .initial .initial (.item ⟨2,[65]⟩)⟩
    operations tx = [.create (.issued ⟨3,[66]⟩) (some .initial),
      .marker .initial .initial ⟨3,[66]⟩ (.item ⟨2,[65]⟩),
      .moveInto .initial .initial ⟨3,[66]⟩ (.issued ⟨3,[66]⟩)] ∧
    (record tx []).references = [⟨2,[65]⟩] ∧
    (record tx []).references ≠ [⟨3,[66]⟩] := by decide

/-- Source pending deletion is read at text-item birth, but split markers
remain undeleted even if the raw deleted-ID set mentions their ID. -/
theorem pending_delete_control :
    births (⟨⟨1,[65]⟩, .insert .initial .initial .start [97]⟩ : Transaction) (fun _ _ => true) =
      [(.initial, ⟨⟨⟨1,[65]⟩, .text 97 true⟩, .start⟩)] ∧
    births (⟨⟨1,[65]⟩, .insert .initial .initial .start [97]⟩ : Transaction) (fun _ _ => true) ≠
      [(.initial, ⟨⟨⟨1,[65]⟩, .text 97 false⟩, .start⟩)] ∧
    births (⟨⟨1,[65]⟩, .split .initial .initial .start⟩ : Transaction) (fun _ _ => true) =
      [(.initial, ⟨⟨⟨1,[65]⟩, .split⟩, .start⟩)] ∧
    births (⟨⟨1,[65]⟩, .split .initial .initial .start⟩ : Transaction) (fun _ _ => true) ≠
      [] := by decide

#print axioms born_iff_record
#print axioms clockMax_reservation
#print axioms prepare_admitted
end Sal.MRDTs.Instances.NotionCorePayload
