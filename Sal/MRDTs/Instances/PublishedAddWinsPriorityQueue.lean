import Sal.MRDTs.Metatheory.Correctness
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max

/-! Algorithm 2 of Zhang et al., Internetware 2023, on integer-valued inputs.
This state-based translation retains immutable birth payloads and separately
identified increment attachments to each observed birth. Projected records have
exactly the source's innate value, acquired increment and accumulated magnitude.
There is no element-wide persistent acquired sum. Operation IDs deduplicate
merge-delivered effects, corresponding to the source's exactly-once network.

Source choices are retained as relations/finite sets of admitted answers:
Most-Change-Win ties have no published tie rule. Early Inc creates a record with
unknown innate value; undefined null arithmetic is reported, not invented. -/
namespace Sal.MRDTs.Instances.PublishedAddWinsPriorityQueue
open Foundation

abbrev Tag := Nat × Timestamp
abbrev Birth := Tag × Int
abbrev Attachment := Tag × Timestamp × Int

structure State where
  births : Finset Birth := ∅
  increments : Finset Attachment := ∅
  removed : Finset Tag := ∅
  deriving DecidableEq

@[ext] theorem State.ext {a b : State} (births : a.births = b.births)
    (increments : a.increments = b.increments) (removed : a.removed = b.removed) : a = b := by
  cases a; cases b
  simp_all

inductive Request where
  | add (element : Nat) (innate : Int)
  | inc (element : Nat) (amount : Int)
  | remove (element : Nat)
  deriving DecidableEq

/-- Inc/Remove carry the exact preparation-time live insertion timestamps. -/
inductive Payload where
  | add (element : Nat) (innate : Int)
  | inc (element : Nat) (amount : Int) (observed : Finset Timestamp)
  | remove (element : Nat) (observed : Finset Timestamp)
  deriving DecidableEq

abbrev Event := Op Payload

def step (s : State) (e : Event) : State := match e.2.2 with
  | .add x v => { s with births := insert ((x,e.1),v) s.births }
  | .inc x n observed => { s with increments := (s.increments ∪ observed.image (fun t => ((x,t),e.1,n))) }
  | .remove x observed => { s with removed := (s.removed ∪ observed.image (fun t => (x,t))) }

/-- Union of per-record attachments, not union of element-wide increments.
The ancestor remains an interface input but immutable effects need no delta. -/
def merge (_l a b : State) : State :=
  ⟨a.births ∪ b.births,a.increments ∪ b.increments,a.removed ∪ b.removed⟩

/-- Inc before its Add creates the source's null-innate placeholder. -/
def recordTags (s : State) : Finset Tag :=
  s.births.image Prod.fst ∪ s.increments.image Prod.fst

def liveTags (s : State) : Finset Tag := recordTags s \ s.removed

def liveElements (s : State) : Finset Nat := (liveTags s).image Prod.fst

def observed (s : State) (x : Nat) : Finset Timestamp :=
  ((liveTags s).filter (fun t => t.1 = x)).image Prod.snd

def lookup (s : State) (x : Nat) : Bool := decide (x ∈ liveElements s)

def acquired (s : State) (tag : Tag) : Int :=
  ∑ a ∈ s.increments.filter (fun a => a.1 = tag), a.2.2

def magnitude (s : State) (tag : Tag) : Nat :=
  ∑ a ∈ s.increments.filter (fun a => a.1 = tag), a.2.2.natAbs

/-- Only honest unique birth IDs have a single payload. Multiple payloads for
one ID are retained as ambiguity on raw forged inputs, not resolved by value. -/
def innateValues (s : State) (tag : Tag) : Finset Int :=
  (s.births.filter (fun b => b.1 = tag)).image Prod.snd

structure Record where
  tag : Tag
  innate : Finset Int
  acquired : Int
  count : Nat
  deriving DecidableEq

def record (s : State) (tag : Tag) : Record :=
  ⟨tag,innateValues s tag,acquired s tag,magnitude s tag⟩

def records (s : State) : Finset Record := (recordTags s).image (record s)

def latestTags (s : State) (x : Nat) : Finset Tag :=
  ((liveTags s).filter (fun t => t.1 = x)).filter
    (fun t => ∀ u ∈ liveTags s, u.1 = x → u.2 ≤ t.2)

def mostChangedTags (s : State) (x : Nat) : Finset Tag :=
  ((liveTags s).filter (fun t => t.1 = x)).filter
    (fun t => ∀ u ∈ liveTags s, u.1 = x → magnitude s u ≤ magnitude s t)

/-- All answers permitted by Algorithm 2 lines 7–9. No secondary tie rule. -/
def priorities (s : State) (x : Nat) : Finset Int :=
  (latestTags s x).biUnion (fun tag =>
    (innateValues s tag).biUnion (fun v =>
      (mostChangedTags s x).image (fun incTag => v + acquired s incTag)))

/-- The source latest record has null innate payload: lookup can still be true
but the paper leaves numerical get_pri behavior unspecified. -/
def unresolvedInnate (s : State) (x : Nat) : Bool :=
  decide (∃ tag ∈ latestTags s x, innateValues s tag = ∅)

/-- Admitted maximum pairs, retaining priority-choice nondeterminism. For each
other element there must be a permitted query value at most the selected value. -/
def maximumPairs (s : State) : Finset (Nat × Int) :=
  ((liveElements s).biUnion (fun x => (priorities s x).image (fun p => (x,p)))).filter
    (fun pair => ∀ x ∈ liveElements s, ∃ q ∈ priorities s x, q ≤ pair.2)

/-- Honest local preparation, including guards and the exact observed snapshot. -/
def prepare (s : State) (t r : Nat) : Request → Option Event
  | .add x v => if lookup s x then none else some (t,r,.add x v)
  | .inc x n => if lookup s x then some (t,r,.inc x n (observed s x)) else none
  | .remove x => if lookup s x then some (t,r,.remove x (observed s x)) else none

/-- Derived Algorithm 1 remove-maximum preparation can return any admitted
maximum. It emits ordinary observed removal of that selected identity. -/
def prepareRmvMax (s : State) (t r : Nat) : Finset (Event × (Nat × Int)) :=
  (maximumPairs s).image (fun pair => ((t,r,Payload.remove pair.1 (observed s pair.1)),pair))

/-- Observable source query evidence; `undefined` preserves the source's null
arithmetic gap rather than treating placeholders as absent queue elements. -/
inductive Query where
  | empty
  | lookup (element : Nat)
  | getPri (element : Nat)
  | getMax
  deriving DecidableEq

inductive ReadView where
  | boolean (value : Bool)
  | priority (values : Finset Int) (undefined : Bool)
  | maximum (values : Finset (Nat × Int))
  deriving DecidableEq

def read (s : State) : Query → ReadView
  | .empty => .boolean (decide (liveElements s = ∅))
  | .lookup x => .boolean (lookup s x)
  | .getPri x => .priority (priorities s x) (unresolvedInnate s x)
  | .getMax => .maximum (maximumPairs s)

/-- The Value is a diagnostic representation of the published answer relation,
not a claim that the paper's get_pri returns a set of integers. -/
def D : MRDTSig where
  State := State
  dec_state := inferInstance
  init := {}
  AppOp := Payload
  dec_op := inferInstance
  Query := Query
  Value := ReadView
  update := step
  merge := merge
  query := read

def requestOf : Payload → Request
  | .add x v => .add x v
  | .inc x n _ => .inc x n
  | .remove x _ => .remove x

def generation : Issuance D where
  CanIssue e s := prepare s e.time e.rep (requestOf e.op) = some e

/-- Immutable effects commute without rebuilding an observed snapshot. -/
theorem effects_commute (a b : Event) : D.toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  change step (step s (ta,ra,oa)) (tb,rb,ob) = step (step s (tb,rb,ob)) (ta,ra,oa)
  cases oa <;> cases ob <;> apply State.ext <;>
    simp [step,Finset.union_assoc,Finset.union_comm,Finset.union_left_comm,Finset.insert_comm]

#print axioms effects_commute
end Sal.MRDTs.Instances.PublishedAddWinsPriorityQueue
