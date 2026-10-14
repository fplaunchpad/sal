import Sal.MRDTs.Instances.NotionCoreSourceInvariant

/-! Whole-version exchange and mint provenance for the MRDT adaptation.
The source receiver also permits arbitrary individual delivery. Here an exchange
imports a complete peer version, as transaction-set union does. Ghost records
remember the actual mint-time received runs; neither dependencies nor the
desired document answer are supplied as an issuance invariant.

References remain inputs selected from item-producing reservations. Extracting those references
from the source document's preparation functions is a separate obligation.
-/
namespace Sal.MRDTs.Instances.NotionCoreIssuance
open NotionRunAllocation

structure Record where
  run : Run
  past : List Run
  /-- RGA item origins and deletion targets. Block-name references require
  their separate allocation/decoding correspondence. -/
  references : List Id
  items : Bool
  deriving DecidableEq, Repr

structure State where
  allocation : Network
  records : List Record

def initial : State := ⟨NotionRunAllocation.initial, []⟩

def importRuns (network : Network) (target : Session) : List Run → Network
  | [] => network
  | run :: rest => importRuns (deliver network target run) target rest

def exchange (state : State) (target source : Session) : State :=
  {state with allocation := importRuns state.allocation target (state.allocation.peers source).received}

def gap (state : State) (session : Session) (ticks : Nat) : State :=
  {state with allocation := skip state.allocation session ticks}

/-- Text insertion and split markers produce every ID of their reserved run;
create/delete and empty bootstrap reservations produce no RGA item. The tag's
correspondence to source payload decoding is still separate. -/
def ItemKnown (state : State) (session : Session) (id : Id) : Prop :=
  ∃ record ∈ state.records, record.run ∈ (state.allocation.peers session).received ∧
    record.items = true ∧ record.run.Contains id

def mint (state : State) (session : Session) (width : Nat) (items : Bool) (references : List Id) : State :=
  let peer := state.allocation.peers session
  ⟨issue state.allocation session width,
    ⟨reserve peer session width, peer.received, references, items⟩ :: state.records⟩

inductive Reach : State → Prop where
  | init : Reach initial
  | exchange {state : State} (target source : Session) :
      Reach state → Reach (exchange state target source)
  | gap {state : State} (session : Session) (ticks : Nat) :
      Reach state → Reach (gap state session ticks)
  | mint {state : State} (session : Session) (width : Nat) (items : Bool) (references : List Id) :
      Reach state → 0 < width →
      (∀ id ∈ references, ItemKnown state session id) →
      Reach (mint state session width items references)

@[simp] theorem import_published (network : Network) (target : Session) (runs : List Run) :
    (importRuns network target runs).published = network.published := by
  induction runs generalizing network with
  | nil => rfl
  | cons run rest ih => simpa [importRuns, deliver] using ih (deliver network target run)

theorem import_received (network : Network) (target : Session) (runs : List Run)
    (peer : Session) (run : Run) :
    run ∈ ((importRuns network target runs).peers peer).received ↔
      run ∈ (network.peers peer).received ∨ peer = target ∧ run ∈ runs := by
  induction runs generalizing network with
  | nil => simp [importRuns]
  | cons first rest ih =>
    rw [importRuns, ih]
    by_cases same : peer = target
    · subst peer
      simp [deliver, receive, or_assoc, or_left_comm, or_comm]
    · simp [deliver, same]

theorem import_reachable {network : Network} (reachable : NotionRunAllocation.Reach network)
    (target : Session) (runs : List Run) (published : ∀ run ∈ runs, run ∈ network.published) :
    NotionRunAllocation.Reach (importRuns network target runs) := by
  induction runs generalizing network with
  | nil => exact reachable
  | cons run rest ih =>
    apply ih (.delivery run target reachable (published run (by simp)))
    intro old member
    exact published old (by simp [member])

theorem allocation_reachable {state : State} (reachable : Reach state) :
    NotionRunAllocation.Reach state.allocation := by
  induction reachable with
  | init => exact .init
  | @exchange state target source _ ih =>
    exact import_reachable ih target _ (fun run member => reachable_received_published ih source run member)
  | gap session ticks _ ih => exact .gap ticks session ih
  | mint session width items references _ positive _ ih => exact .issuance width session ih positive

theorem record_runs {state : State} (reachable : Reach state) :
    state.records.map Record.run = state.allocation.published := by
  induction reachable with
  | init => rfl
  | exchange target source _ ih => simpa [exchange] using ih
  | gap session ticks _ ih => simpa [gap, skip] using ih
  | mint session width items references _ _ _ ih => simpa [mint, issue] using ih

theorem record_published {state : State} (reachable : Reach state)
    {record : Record} (member : record ∈ state.records) :
    record.run ∈ state.allocation.published := by
  rw [← record_runs reachable]
  exact List.mem_map.mpr ⟨record, member, rfl⟩

/-- The references' complete provider runs and their observed clock maxima
are consequences of the saved mint state, not a replay-order assumption. -/
theorem record_provenance {state : State} (reachable : Reach state) :
    ∀ record ∈ state.records,
      (∀ id ∈ record.references, ∃ run ∈ record.past, run.Contains id) ∧
      (∀ run ∈ record.past, run.last < record.run.first.counter) ∧
      (∀ run ∈ record.past, run ∈ state.allocation.published) := by
  induction reachable with
  | init => simp [initial]
  | @exchange state target source _ ih => simpa [exchange] using ih
  | @gap state session ticks _ ih => simpa [gap, skip] using ih
  | @mint state session width items references before positive known ih =>
    intro record member
    simp only [mint, List.mem_cons] at member
    rcases member with rfl | member
    · refine ⟨?_, ?_, ?_⟩
      · intro id reference
        obtain ⟨provider, _, received, _, contains⟩ := known id reference
        exact ⟨provider.run, received, contains⟩
      · intro old received
        have bounded := reachable_bounded (allocation_reachable before) session old received
        simp only [reserve]
        omega
      · intro old received
        exact List.mem_cons_of_mem _ (reachable_received_published (allocation_reachable before) session old received)
    · obtain ⟨referencesKnown, smaller, published⟩ := ih record member
      exact ⟨referencesKnown, smaller, fun old received => List.mem_cons_of_mem _ (published old received)⟩

/-- Every referenced ID was produced by an item-producing transaction in the
actual mint past. A create/delete reservation alone cannot supply an origin. -/
theorem record_reference_births {state : State} (reachable : Reach state) :
    ∀ record ∈ state.records, ∀ id ∈ record.references,
      ∃ provider ∈ state.records, provider.run ∈ record.past ∧
        provider.items = true ∧ provider.run.Contains id := by
  induction reachable with
  | init => simp [initial]
  | exchange target source _ ih => simpa [exchange] using ih
  | gap session ticks _ ih => simpa [gap] using ih
  | @mint state session width items references before positive known ih =>
    intro record member id reference
    simp only [mint, List.mem_cons] at member
    rcases member with rfl | member
    · obtain ⟨provider, present, received, produces, contains⟩ := known id reference
      exact ⟨provider, List.mem_cons_of_mem _ present, received, produces, contains⟩
    · obtain ⟨provider, present, past, produces, contains⟩ := ih record member id reference
      exact ⟨provider, List.mem_cons_of_mem _ present, past, produces, contains⟩

/-- Every non-START reference predates the new run strictly by counter.
Together with consecutive within-run IDs this supplies the parent-map's
acyclic rank, independently of session tie-breaking. -/
theorem reference_counter_before {state : State} (reachable : Reach state)
    {record : Record} (member : record ∈ state.records) {id : Id}
    (reference : id ∈ record.references) : id.counter < record.run.first.counter := by
  have provenance := record_provenance reachable record member
  obtain ⟨provider, past, contains⟩ := provenance.1 id reference
  exact Nat.lt_of_le_of_lt (contains_le_last contains) (provenance.2.1 provider past)

def Closed (records : List Record) (runs : List Run) : Prop :=
  ∀ record ∈ records, record.run ∈ runs → ∀ old ∈ record.past, old ∈ runs

/-- Every exposed peer version contains the actual entire mint past of each
transaction it contains. Exchange is whole-version union; raw isolated receipt
does not satisfy this theorem. -/
theorem peers_closed {state : State} (reachable : Reach state) :
    ∀ peer, Closed state.records (state.allocation.peers peer).received := by
  induction reachable with
  | init => simp [initial, Closed]
  | @exchange state target source _ ih =>
    intro peer record member present old past
    change record ∈ state.records at member
    change record.run ∈ ((importRuns state.allocation target
      (state.allocation.peers source).received).peers peer).received at present
    change old ∈ ((importRuns state.allocation target
      (state.allocation.peers source).received).peers peer).received
    rw [import_received] at present ⊢
    rcases present with present | ⟨rfl, present⟩
    · exact Or.inl (ih peer record member present old past)
    · exact Or.inr ⟨rfl, ih source record member present old past⟩
  | @gap state session ticks _ ih =>
    intro peer
    by_cases same : peer = session <;> simpa [gap, skip, advance, same] using ih peer
  | @mint state session width items references before positive known ih =>
    intro peer record member present old past
    have allocation := allocation_reachable before
    have fresh : reserve (state.allocation.peers session) session width ∉
        (state.allocation.peers peer).received := by
      intro received
      exact fresh_transaction_key allocation
        (reachable_received_published allocation peer _ received) session width rfl
    simp only [mint, List.mem_cons] at member
    by_cases same : peer = session
    · subst peer
      simp [mint, issue, receive] at present ⊢
      rcases member with rfl | member
      · exact Or.inr past
      · rcases present with new | present
        · have published := record_published before member
          exact False.elim (fresh_transaction_key allocation published session width
            (congrArg Run.first new).symm)
        · exact Or.inr (ih session record member present old past)
    · simp [mint, issue, same] at present ⊢
      rcases member with rfl | member
      · exact False.elim (fresh present)
      · exact ih peer record member present old past

/-- Dependency closure is stable under ternary transaction-set union even
when the base is recursively synthesized. This is independent of base choice. -/
theorem closed_union {records : List Record} {left right : List Run}
    (hl : Closed records left) (hr : Closed records right) : Closed records (left ++ right) := by
  intro record member present old past
  rcases List.mem_append.mp present with present | present
  · exact List.mem_append_left _ (hl record member present old past)
  · exact List.mem_append_right _ (hr record member present old past)

theorem closed_intersection {records : List Record} {left right : List Run}
    (hl : Closed records left) (hr : Closed records right) :
    Closed records (left.filter (· ∈ right)) := by
  intro record member present old past
  have both := List.mem_filter.mp present
  exact List.mem_filter.mpr ⟨hl record member both.1 old past,
    by simpa using hr record member (by simpa using both.2) old past⟩

/-- A source-key ordered replay prefix already includes the entire mint past
of its next transaction. The complete version's closure is derived above;
this lemma transports it through the source's chosen replay order. -/
theorem past_in_prefix {state : State} (reachable : Reach state)
    {record : Record} (member : record ∈ state.records) (pre suffix : List Run)
    (closed : Closed state.records (pre ++ record.run :: suffix))
    (ordered : (pre ++ record.run :: suffix).Pairwise (fun a b => Before a.first b.first)) :
    ∀ old ∈ record.past, old ∈ pre := by
  intro old past
  have provenance := record_provenance reachable record member
  have present := closed record member (by simp) old past
  have smaller := provenance.2.1 old past
  have positive := reachable_positive (allocation_reachable reachable) old (provenance.2.2 old past)
  have lower : old.first.counter ≤ old.last := by
    simp only [Run.last]
    omega
  have tailOrdered := (List.pairwise_append.mp ordered).2.1
  rcases List.mem_append.mp present with earlier | later
  · exact earlier
  · rcases List.mem_cons.mp later with equal | later
    · rw [equal] at lower smaller
      omega
    · have before := (List.pairwise_cons.mp tailOrdered).1 old later
      rcases before with lt | ⟨eq, _⟩ <;> omega

/-- The next transaction's non-START origin or deletion target has a complete
provider transaction in the actual sorted prefix, including internal run IDs. -/
theorem reference_in_prefix {state : State} (reachable : Reach state)
    {record : Record} (member : record ∈ state.records) (pre suffix : List Run)
    (closed : Closed state.records (pre ++ record.run :: suffix))
    (ordered : (pre ++ record.run :: suffix).Pairwise (fun a b => Before a.first b.first))
    {id : Id} (reference : id ∈ record.references) :
    ∃ provider ∈ pre, provider.Contains id ∧ provider.last < record.run.first.counter := by
  have provenance := record_provenance reachable record member
  obtain ⟨provider, past, contains⟩ := provenance.1 id reference
  exact ⟨provider, past_in_prefix reachable member pre suffix closed ordered provider past,
    contains, provenance.2.1 provider past⟩

/-- Internal children inherit their provider's observed whole-run bound.
This derives dominance from the new transaction's referenced predecessor and
globally unique allocation; the child itself need not have been selected. -/
theorem internal_child_dominance {state : State} (reachable : Reach state)
    {record : Record} (member : record ∈ state.records)
    {old : Run} (published : old ∈ state.allocation.published)
    {offset : Nat} (positive : 0 < offset) (within : offset < old.length)
    (reference : old.at (offset - 1) ∈ record.references) :
    Before (old.at offset) record.run.first := by
  have provenance := record_provenance reachable record member
  obtain ⟨provider, past, contains⟩ := provenance.1 _ reference
  have same := reachable_unique_owner (allocation_reachable reachable) old published provider
    (provenance.2.2 provider past) (old.at (offset - 1))
    ⟨offset - 1, by omega, rfl⟩ contains
  have smaller := provenance.2.1 provider past
  have bound := contains_le_last (r := old) (id := old.at offset) ⟨offset, within, rfl⟩
  rw [← same] at smaller
  exact Or.inl (by omega)

/-- Every older direct child is either transaction-first, handled by source
replay sorting, or internal to its run, handled by complete-run provenance. -/
theorem replay_child_dominance {state : State} (reachable : Reach state)
    {record : Record} (member : record ∈ state.records) (pre suffix : List Run)
    (ordered : (pre ++ record.run :: suffix).Pairwise (fun a b => Before a.first b.first))
    {old : Run} (earlier : old ∈ pre) (published : old ∈ state.allocation.published)
    {offset : Nat} (within : offset < old.length)
    (reference : 0 < offset → old.at (offset - 1) ∈ record.references) :
    Before (old.at offset) record.run.first := by
  by_cases zero : offset = 0
  · have before := (List.pairwise_append.mp ordered).2.2 old earlier record.run (by simp)
    simpa [Run.at, zero] using before
  · exact internal_child_dominance reachable member published (by omega) within (reference (by omega))

def Ascending (a b : Run) : Prop := NotionCoreSourceInvariant.Desc b.first a.first
instance : DecidableRel Ascending := fun _ _ => inferInstanceAs (Decidable (NotionCoreSourceInvariant.Desc _ _))
instance : Std.Total Ascending where
  total a b := by
    rcases NotionCoreSourceInvariant.before_trichotomy a.first b.first with before | same | reverse
    · exact Or.inl (Or.inl before)
    · exact Or.inl (Or.inr same.symm)
    · exact Or.inr (Or.inl reverse)
instance : IsTrans Run Ascending where
  trans a b c ab bc := by
    rcases ab with ab | ab <;> rcases bc with bc | bc
    · exact Or.inl (NotionCoreSourceInvariant.before_trans ab bc)
    · exact Or.inl (by simpa only [bc] using ab)
    · exact Or.inl (by simpa only [ab] using bc)
    · exact Or.inr (bc.trans ab)

/-- Deduplicate receipts by immutable published transaction identity and sort
the selected complete runs by the source comparator. Ghost past/reference
fields do not participate in the replay order. -/
def replay (state : State) (version : List Run) : List Run :=
  ((state.records.map Record.run).filter (· ∈ version)).mergeSort
    (fun a b => decide (Ascending a b))

theorem replay_membership (state : State) (version : List Run) (run : Run) :
    run ∈ replay state version ↔ run ∈ state.records.map Record.run ∧ run ∈ version := by
  unfold replay
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

theorem replay_ordered {state : State} (reachable : Reach state) (version : List Run) :
    (replay state version).Pairwise (fun a b => Before a.first b.first) := by
  have allUnique := reachable_transaction_keys_unique (allocation_reachable reachable)
  rw [← record_runs reachable] at allUnique
  have pairwise : (state.records.map Record.run).Pairwise (fun a b => a.first ≠ b.first) :=
    List.pairwise_map.mp allUnique
  have filtered := pairwise.filter (fun run => decide (run ∈ version))
  have filteredUnique : (((state.records.map Record.run).filter (· ∈ version)).map Run.first).Nodup :=
    List.pairwise_map.mpr filtered
  have unique : ((replay state version).map Run.first).Nodup :=
    ((List.mergeSort_perm _ _).map Run.first).nodup_iff.mpr filteredUnique
  have sorted : (replay state version).Pairwise Ascending :=
    List.pairwise_mergeSort' Ascending _
  apply (sorted.and (List.pairwise_map.mp unique)).imp
  intro a b both
  rcases both.1 with before | equal
  · exact before
  · exact False.elim (both.2 equal.symm)

theorem replay_closed {state : State} (reachable : Reach state) (version : List Run)
    (closed : Closed state.records version) : Closed state.records (replay state version) := by
  intro record member present old past
  apply (replay_membership state version old).mpr
  refine ⟨?_, closed record member ((replay_membership state version record.run).mp present).2 old past⟩
  rw [record_runs reachable]
  exact (record_provenance reachable record member).2.2 old past

/-- For every split of the actual canonical whole-version replay, the next
record's references have complete provider runs before it. No source-sorted
list is supplied as a premise. -/
theorem replay_ready {state : State} (reachable : Reach state) (peer : Session)
    {record : Record} (member : record ∈ state.records) (pre suffix : List Run)
    (position : replay state (state.allocation.peers peer).received = pre ++ record.run :: suffix)
    {id : Id} (reference : id ∈ record.references) :
    ∃ provider ∈ pre, provider.Contains id ∧ provider.last < record.run.first.counter := by
  exact reference_in_prefix reachable member pre suffix
    (position ▸ replay_closed reachable _ (peers_closed reachable peer))
    (position ▸ replay_ordered reachable _) reference

/-- Strengthen replay readiness to a provider that actually produces RGA
items, excluding source reservations used only for create/delete metadata. -/
theorem replay_item_ready {state : State} (reachable : Reach state) (peer : Session)
    {record : Record} (member : record ∈ state.records) (pre suffix : List Run)
    (position : replay state (state.allocation.peers peer).received = pre ++ record.run :: suffix)
    {id : Id} (reference : id ∈ record.references) :
    ∃ provider ∈ state.records, provider.run ∈ pre ∧ provider.items = true ∧
      provider.run.Contains id ∧ provider.run.last < record.run.first.counter := by
  obtain ⟨provider, present, past, produces, contains⟩ :=
    record_reference_births reachable record member id reference
  have earlier := past_in_prefix reachable member pre suffix
    (position ▸ replay_closed reachable _ (peers_closed reachable peer))
    (position ▸ replay_ordered reachable _) provider.run past
  exact ⟨provider, present, earlier, produces, contains,
    (record_provenance reachable record member).2.1 provider.run past⟩

private def seed : State := mint initial [65] 2 true []
private def copied : State := exchange seed [66] [65]
private def edited : State := mint copied [66] 1 true [⟨1, [65]⟩]
private def shared : State := exchange (mint edited [67] 1 false []) [66] [67]

/-- PASS+FAIL: whole-version exchange observes the complete two-item bootstrap
run. An edit at its first item allocates B@3, not B@2. -/
theorem whole_run_control :
    edited.records.head?.map (fun record => record.run.first) = some (⟨3, [66]⟩ : Id) ∧
    edited.records.head?.map (fun record => record.run.first) ≠ some (⟨2, [66]⟩ : Id) := by decide

/-- PASS+FAIL: the executable steps used by the control satisfy the issuance
relation, and an unknown fabricated origin cannot be prepared at that state. -/
theorem issuance_control : Reach edited ∧
    ¬ Known (copied.allocation.peers [66]) (⟨10, [90]⟩ : Id) := by
  constructor
  · apply Reach.mint [66] 1 true _ (Reach.exchange [66] [65] (Reach.mint [65] 2 true [] .init (by decide) (by simp)))
    · decide
    · intro id member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst id
      exact ⟨⟨⟨⟨1, [65]⟩, 2⟩, [], [], true⟩, by decide, by decide, rfl, 0, by decide, rfl⟩
  · intro known
    obtain ⟨run, received, offset, within, equal⟩ := known
    have only : run = (⟨⟨1, [65]⟩, 2⟩ : Run) := by simpa [copied, seed, exchange,
      importRuns, mint, initial, NotionRunAllocation.initial, emptyPeer, issue, deliver,
      receive, reserve] using received
    subst run
    have session := congrArg Id.session equal
    simp [Run.at] at session

/-- PASS+FAIL: canonical source order differs from receipt order. A concurrent
C@1 transaction sorts between the bootstrap A@1 and dependent B@3. -/
theorem canonical_replay_control :
    (replay shared (shared.allocation.peers [66]).received).map Run.first =
      [⟨1, [65]⟩, ⟨1, [67]⟩, ⟨3, [66]⟩] ∧
    (replay shared (shared.allocation.peers [66]).received).map Run.first ≠
      [⟨1, [67]⟩, ⟨3, [66]⟩, ⟨1, [65]⟩] := by
  have tie : ¬ ([67] : List Nat) < [65] := by decide
  simp [replay, shared, edited, copied, seed, mint, exchange, importRuns, initial,
    NotionRunAllocation.initial, emptyPeer, issue, deliver, receive, reserve,
    List.mergeSort, Run.last, Ascending, NotionCoreSourceInvariant.Desc, Before, tie]

/-- Whole-version receipt contains the origin's provider; receiving just the
dependent B@3 record, which the raw demo permits, is not dependency-closed. -/
theorem isolated_receipt_control :
    Closed edited.records (edited.allocation.peers [66]).received ∧
    ¬ Closed edited.records [⟨⟨3, [66]⟩, 1⟩] := by
  refine ⟨peers_closed issuance_control.1 [66], ?_⟩
  intro closed
  have impossible := closed
    ⟨⟨⟨3, [66]⟩, 1⟩, [⟨⟨1, [65]⟩, 2⟩], [⟨1, [65]⟩], true⟩
    (by decide) (by simp) ⟨⟨1, [65]⟩, 2⟩ (by simp)
  revert impossible
  decide

/-- A clock reservation for metadata is known as a run but cannot be used
as an RGA origin. This distinguishes item births from allocation alone. -/
theorem metadata_reservation_control :
    Known ((mint initial [65] 1 false []).allocation.peers [65]) (⟨1, [65]⟩ : Id) ∧
    ¬ ItemKnown (mint initial [65] 1 false []) [65] (⟨1, [65]⟩ : Id) := by
  simp [Known, ItemKnown, mint, initial, NotionRunAllocation.initial, emptyPeer,
    issue, receive, reserve, Run.Contains, Run.at]

#print axioms peers_closed
#print axioms reference_in_prefix
#print axioms replay_child_dominance
#print axioms replay_ready
#print axioms replay_item_ready

end Sal.MRDTs.Instances.NotionCoreIssuance
