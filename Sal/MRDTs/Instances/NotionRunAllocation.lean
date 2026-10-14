import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Sal.MRDTs.Framework.Base.Replay

/-! Source allocation model for the split/insert/delete fragment.
The source's compound IDs are distinct from Sal's globally unique outer event
labels. Sessions are explicit UTF-16 code-unit lists, matching JavaScript
lexical comparison (Lean Unicode String ordering would differ). A reservation is an atomic run of
consecutive counters; split/create/delete reserve one counter. This module
models only allocation/receipt, not document interpretation. -/
namespace Sal.MRDTs.Instances.NotionRunAllocation

/-- JavaScript string identity/order represented by UTF-16 code units. Source
encodings use units below 65536; the arithmetic allocation laws need no bound. -/
abbrev Session := List Nat

structure Id where
  counter : Nat
  session : Session
  deriving DecidableEq, Repr

def Before (a b : Id) : Prop :=
  a.counter < b.counter ∨ a.counter = b.counter ∧ a.session < b.session

structure Run where
  first : Id
  length : Nat
  deriving DecidableEq, Repr

def Run.at (r : Run) (offset : Nat) : Id :=
  ⟨r.first.counter + offset, r.first.session⟩
def Run.last (r : Run) : Nat := r.first.counter + r.length - 1
def Run.Contains (r : Run) (id : Id) : Prop :=
  ∃ offset, offset < r.length ∧ id = r.at offset

structure Peer where
  clock : Nat
  received : List Run

def emptyPeer : Peer := ⟨0, []⟩
def receive (s : Peer) (r : Run) : Peer :=
  ⟨max s.clock r.last, r :: s.received⟩
def advance (s : Peer) (ticks : Nat) : Peer :=
  { s with clock := s.clock + ticks }
def reserve (s : Peer) (session : Session) (width : Nat) : Run :=
  ⟨⟨s.clock + 1, session⟩, width⟩

def Bounded (s : Peer) : Prop := ∀ r ∈ s.received, r.last ≤ s.clock

theorem receive_bounded {s : Peer} (h : Bounded s) (r : Run) :
    Bounded (receive s r) := by
  intro old mem
  simp only [receive, List.mem_cons] at mem
  rcases mem with rfl | mem
  · exact Nat.le_max_right _ _
  · exact Nat.le_trans (h old mem) (Nat.le_max_left _ _)

theorem contains_le_last {r : Run} {id : Id} (h : r.Contains id) :
    id.counter ≤ r.last := by
  obtain ⟨offset, bound, rfl⟩ := h
  simp only [Run.at, Run.last]
  omega

theorem received_before_reservation {s : Peer} (h : Bounded s)
    {r : Run} (mem : r ∈ s.received) {id : Id} (item : r.Contains id)
    (session : Session) (width : Nat) :
    id.counter < (reserve s session width).first.counter := by
  have := Nat.le_trans (contains_le_last item) (h r mem)
  simp only [reserve]
  omega

/-- There is exactly one serialized allocator per source session. A receive
can import any previously published transaction, including repeated delivery.
Unlike the document model, this skeleton exposes no validity constraints on
which editing request needs a reservation. -/
structure Network where
  peers : Session → Peer
  published : List Run

def initial : Network := ⟨fun _ => emptyPeer, []⟩
def deliver (n : Network) (session : Session) (r : Run) : Network :=
  { n with peers := Function.update n.peers session (receive (n.peers session) r) }
def skip (n : Network) (session : Session) (ticks : Nat) : Network :=
  { n with peers := Function.update n.peers session (advance (n.peers session) ticks) }
def issue (n : Network) (session : Session) (width : Nat) : Network :=
  let r := reserve (n.peers session) session width
  ⟨Function.update n.peers session (receive (n.peers session) r), r :: n.published⟩

inductive Reach : Network → Prop where
  | init : Reach initial
  | delivery {n : Network} (r : Run) (session : Session) :
      Reach n → r ∈ n.published → Reach (deliver n session r)
  | gap {n : Network} (ticks : Nat) (session : Session) : Reach n → Reach (skip n session ticks)
  | issuance {n : Network} (width : Nat) (session : Session) :
      Reach n → 0 < width → Reach (issue n session width)

/-- Every recipient has observed the maximum of each complete received run. -/
theorem reachable_bounded {n : Network} (h : Reach n) :
    ∀ session, Bounded (n.peers session) := by
  induction h with
  | init => simp [initial, Bounded, emptyPeer]
  | @delivery n r session _ _ ih =>
      intro target
      by_cases eq : target = session
      · subst target
        simpa [deliver] using receive_bounded (ih session) r
      · simpa [deliver, eq] using ih target
  | @gap n ticks session _ ih =>
      intro target
      by_cases eq : target = session
      · subst target
        intro r mem
        simp [skip, advance] at mem ⊢
        have bound := ih session r mem
        omega
      · simpa [skip, eq] using ih target
  | @issuance n width session _ _ ih =>
      intro target
      by_cases eq : target = session
      · subst target
        simpa [issue] using receive_bounded (ih session) (reserve (n.peers session) session width)
      · simpa [issue, eq] using ih target

/-- A session never forgets any of its own published reservations. -/
theorem reachable_owns {n : Network} (h : Reach n) :
    ∀ r ∈ n.published, r ∈ (n.peers r.first.session).received := by
  induction h with
  | init => simp [initial]
  | @delivery n r session _ _ ih =>
      intro old mem
      have known := ih old mem
      by_cases eq : old.first.session = session
      · simpa [deliver, receive, eq] using List.mem_cons_of_mem r known
      · simpa [deliver, eq] using known
  | @gap n ticks session _ ih =>
      intro old mem
      have known := ih old mem
      by_cases eq : old.first.session = session <;>
        simpa [skip, advance, eq] using known
  | @issuance n width session _ _ ih =>
      intro old mem
      simp only [issue, List.mem_cons] at mem
      rcases mem with rfl | mem
      · simp [issue, reserve, receive]
      · have known := ih old mem
        by_cases eq : old.first.session = session
        · simpa [issue, receive, eq] using
            List.mem_cons_of_mem (reserve (n.peers session) session width) known
        · simpa [issue, eq] using known

/-- Existing reservations from the same session end before its next run. -/
theorem own_run_before_new {n : Network} (h : Reach n) {r : Run}
    (mem : r ∈ n.published) (session : Session)
    (same : r.first.session = session) (width : Nat) :
    r.last < (reserve (n.peers session) session width).first.counter := by
  have known := reachable_owns h r mem
  rw [same] at known
  have bound := reachable_bounded h session r known
  simp only [reserve]
  omega

/-- Session serialization and receipt-derived clock bounds imply globally
unique item ownership. The invariant is derived from the allocation steps. -/
theorem reachable_unique_owner {n : Network} (h : Reach n) :
    ∀ a ∈ n.published, ∀ b ∈ n.published, ∀ id,
      a.Contains id → b.Contains id → a = b := by
  induction h with
  | init => simp [initial]
  | @delivery n r session _ _ ih => simpa [deliver] using ih
  | @gap n ticks session _ ih => simpa [skip] using ih
  | @issuance n width session pre positive ih =>
      intro a ha b hb id ina inb
      simp only [issue, List.mem_cons] at ha hb
      have disjoint : ∀ old ∈ n.published,
          ¬ (reserve (n.peers session) session width).Contains id ∨ ¬ old.Contains id := by
        intro old mem
        by_cases newContains : (reserve (n.peers session) session width).Contains id
        · right
          intro oldContains
          obtain ⟨offset, lt, eq⟩ := newContains
          obtain ⟨oldOffset, oldLt, oldEq⟩ := oldContains
          have same : old.first.session = session := by
            have := congrArg Id.session (oldEq.symm.trans eq)
            simpa [Run.at, reserve] using this
          have before := own_run_before_new pre mem session same width
          have bound := contains_le_last (r := old) ⟨oldOffset, oldLt, oldEq⟩
          rw [eq] at bound
          simp only [Run.at] at bound
          omega
        · exact Or.inl newContains
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact False.elim ((disjoint b hb).elim (fun h => h ina) (fun h => h inb))
      · exact False.elim ((disjoint a ha).elim (fun h => h inb) (fun h => h ina))
      · exact ih a ha b hb id ina inb

/-- Every published reservation has the positive width required by source
allocation. Empty client insertions do not issue an update. -/
theorem reachable_positive {n : Network} (h : Reach n) :
    ∀ r ∈ n.published, 0 < r.length := by
  induction h with
  | init => simp [initial]
  | delivery r session _ _ ih => simpa [deliver] using ih
  | gap ticks session _ ih => simpa [skip] using ih
  | @issuance n width session _ positive ih =>
      intro r mem
      simp only [issue, List.mem_cons] at mem
      rcases mem with rfl | mem
      · exact positive
      · exact ih r mem

/-- Each actual issuance has a source transaction key different from every
previous issuance, including those not observed at other sessions. -/
theorem fresh_transaction_key {n : Network} (h : Reach n) {r : Run}
    (published : r ∈ n.published) (session : Session) (width : Nat) :
    (reserve (n.peers session) session width).first ≠ r.first := by
  intro equal
  have same : r.first.session = session := by
    have := congrArg Id.session equal
    simpa [reserve] using this.symm
  have before := own_run_before_new h published session same width
  have positive := reachable_positive h r published
  have lower : r.first.counter ≤ r.last := by
    simp only [Run.last]
    omega
  rw [equal] at before
  omega

/-- Published transaction keys are globally unique. Repeated receipt does not
publish another transaction. This supplies the allocation part of the map's
same-key/same-payload discipline; payload construction remains separate. -/
theorem reachable_transaction_keys_unique {n : Network} (h : Reach n) :
    (n.published.map Run.first).Nodup := by
  induction h with
  | init => simp [initial]
  | delivery r session _ _ ih => simpa [deliver] using ih
  | gap ticks session _ ih => simpa [skip] using ih
  | @issuance n width session before _ ih =>
      simp only [issue, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro member
      obtain ⟨old, published, equal⟩ := List.mem_map.mp member
      exact fresh_transaction_key before published session width equal.symm

/-- Receipt cannot create an unpublished reservation. -/
theorem reachable_received_published {n : Network} (h : Reach n) :
    ∀ session r, r ∈ (n.peers session).received → r ∈ n.published := by
  induction h with
  | init => simp [initial, emptyPeer]
  | @delivery n r session _ published ih =>
      intro target old mem
      by_cases eq : target = session
      · subst target
        simp [deliver, receive] at mem
        rcases mem with rfl | mem
        · exact published
        · exact ih session old mem
      · apply ih target old
        simpa [deliver, eq] using mem
  | @gap n ticks session _ ih =>
      intro target old mem
      apply ih target old
      by_cases eq : target = session <;>
        simpa [skip, advance, eq] using mem
  | @issuance n width session _ _ ih =>
      intro target old mem
      by_cases eq : target = session
      · subst target
        simp [issue, receive] at mem
        rcases mem with rfl | mem
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih session old mem)
      · apply List.mem_cons_of_mem
        apply ih target old
        simpa [issue, eq] using mem

def Known (s : Peer) (id : Id) : Prop :=
  ∃ r ∈ s.received, r.Contains id

/-- If a prepared origin belongs to a published run, the issuing replica has
received that entire run. This derives transaction provenance from known item
identity and globally unique allocation, rather than assuming it at use. -/
theorem known_run_received {n : Network} (h : Reach n) {r : Run}
    (published : r ∈ n.published) {session : Session} {id : Id}
    (belongs : r.Contains id) (known : Known (n.peers session) id) :
    r ∈ (n.peers session).received := by
  obtain ⟨other, received, contains⟩ := known
  have same := reachable_unique_owner h r published other
    (reachable_received_published h session other received) id belongs contains
  simpa [same] using received

/-- A child internal to an older atomic run follows its preceding character.
An honest issuer knowing that origin has observed the WHOLE run's clock max,
so the new first ID dominates this child even if their transactions' allocation
intervals overlap with unrelated concurrent transactions. -/
theorem internal_child_before_reservation {n : Network} (h : Reach n)
    {r : Run} (published : r ∈ n.published) {offset : Nat}
    (positive : 0 < offset) (within : offset < r.length)
    {session : Session} (known : Known (n.peers session) (r.at (offset - 1)))
    (width : Nat) :
    (r.at offset).counter < (reserve (n.peers session) session width).first.counter := by
  have origin : r.Contains (r.at (offset - 1)) := ⟨offset - 1, by omega, rfl⟩
  have received := known_run_received h published origin known
  exact received_before_reservation (reachable_bounded h session) received
    ⟨offset, within, rfl⟩ session width

/-- The source insertion rule needs domination of origin children, not of all
stored item IDs. Transaction-first children use the sorted replay prefix;
internal-run children use the issuance/receipt argument above. -/
theorem child_dominance {n : Network} (h : Reach n) {r : Run}
    (published : r ∈ n.published) {offset : Nat} (within : offset < r.length)
    {session : Session} {width : Nat}
    (earlier : Before r.first (reserve (n.peers session) session width).first)
    (reference : 0 < offset → Known (n.peers session) (r.at (offset - 1))) :
    Before (r.at offset) (reserve (n.peers session) session width).first := by
  by_cases zero : offset = 0
  · simpa [Run.at, zero] using earlier
  · exact Or.inl (internal_child_before_reservation h published
      (by omega) within (reference (by omega)) width)

/-- PASS+FAIL: transaction-first sorting alone does not imply child dominance.
The older run starts at Z@10 but its internal child is Z@11. A@11 sorts after
Z@10 and before that child. Such an insertion referencing Z@10 cannot be
issued after receiving the complete run, which raises the clock to 11. -/
theorem sorted_first_is_insufficient :
    Before (⟨10, [90]⟩ : Id) ⟨11, [65]⟩ ∧
    ¬ Before ((⟨⟨10, [90]⟩, 2⟩ : Run).at 1) ⟨11, [65]⟩ ∧
    (reserve (receive emptyPeer ⟨⟨10, [90]⟩, 2⟩) [65] 1).first.counter = 12 ∧
    (reserve (receive emptyPeer ⟨⟨10, [90]⟩, 2⟩) [65] 1).first.counter ≠ 11 := by
  unfold Before
  decide

/-- PASS+FAIL: JS compares UTF-16 code units, so the surrogate pair for 😀
comes before U+E000. Comparing Unicode scalar values would reverse this tie. -/
theorem utf16_session_tie_control :
    Before ⟨1, [0xD83D, 0xDE00]⟩ ⟨1, [0xE000]⟩ ∧
    ¬ Before ⟨1, [0xE000]⟩ ⟨1, [0xD83D, 0xDE00]⟩ := by
  unfold Before
  decide

/-- The allocation skeleton's issue transition updates the Lamport counter
exactly as a positive source reserve followed by self-receipt. -/
theorem reserve_receive_clock (s : Peer) (session : Session) (width : Nat)
    (positive : 0 < width) :
    (receive s (reserve s session width)).clock = s.clock + width := by
  simp only [receive, reserve, Run.last]
  omega

/-- Receipt of a complete source transaction gives strict source-clock
causality for the next issuance. Sal's unrelated outer event label is unused. -/
theorem received_transaction_precedes {n : Network} (h : Reach n)
    {session : Session} {r : Run} (received : r ∈ (n.peers session).received)
    (width : Nat) :
    r.first.counter < (reserve (n.peers session) session width).first.counter := by
  have positive := reachable_positive h r
    (reachable_received_published h session r received)
  have first : r.Contains r.first := ⟨0, positive, by simp [Run.at]⟩
  exact received_before_reservation (reachable_bounded h session) received first session width

/-- One source-key-ordered candidate witness preserves causal visibility, and
therefore any specification-conflict restriction of visibility, on that SAME
list. Admission to the independent document language remains a separate
obligation; this theorem deliberately makes no query correctness claim. -/
theorem source_order_preserves_visibility {Event : Type}
    (key : Event → Id) (vis specVis : Event → Event → Prop) (events : List Event)
    (ordered : events.Pairwise (fun a b => Before (key a) (key b)))
    (causal : ∀ a b, vis a b → (key a).counter < (key b).counter)
    (restricted : ∀ a b, specVis a b → vis a b) :
    Sal.MRDTs.Foundation.respects events vis ∧
    Sal.MRDTs.Foundation.respects events specVis := by
  have respects : Sal.MRDTs.Foundation.respects events vis := by
    apply ordered.imp
    intro a b before backward
    have opposite := causal b a backward
    rcases before with lt | ⟨eq, _⟩ <;> omega
  refine ⟨respects, ?_⟩
  exact respects.imp (fun {a b} no edge => no (restricted b a edge))

#print axioms reachable_unique_owner
#print axioms child_dominance
end Sal.MRDTs.Instances.NotionRunAllocation
