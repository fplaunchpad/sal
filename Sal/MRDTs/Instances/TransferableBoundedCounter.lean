import Sal.MRDTs.Metatheory.Correctness

/-! Source-specific candidate for Bismuth/AegisSheet's experimental
`rdts.experiments.BoundedCounter`, NOT an identification with Sal_paper.
Source snapshot: Bismuth-AegisSheet commit
`dd4c614adf03e57911630a4b73936a818a3d0860`,
`Modules/RDTs/src/main/scala/rdts/experiments/BoundedCounter.scala`.
The Scala delta is joined back into current state here. Int overflow and UID
ordering are abstracted by mathematical integers and natural replica ids.
The source accepts negative transfers; we preserve that behavior deliberately.
Its pointwise-max merge has multiwriter reservation components.
Model restrictions: capacities are nonnegative; ordinary replica ids cannot
name the distinguished `initial-allocation` UID. Its fixed negative capacity
entry is omitted from the ordinary-id maps. Consequently this model does NOT
implement the Scala `invariantOk` assertion or claim full-source equivalence.
The concrete credit-loss and negative-transfer traces involve only ordinary
ids and initialized nonnegative PN components. -/
namespace Sal.MRDTs.Instances.TransferableBoundedCounter.BismuthSource
open Foundation
open Classical

structure State where
  positive : Nat → Int
  negative : Nat → Int
  allocated : Nat → Int
  participants : Finset Nat

inductive Action where
  | addParticipants (ids : Finset Nat)
  | allocate (amount : Int)
  | transfer (amount : Int) (target : Nat)
  | rebalance
  deriving DecidableEq

/-- The distinguished initial-allocation UID is kept outside ordinary Nat IDs. -/
def initial (capacity : Nat) (owner : Nat) : State :=
  ⟨fun r => if r = owner then capacity else 0, fun _ => 0,
    fun _ => 0, {owner}⟩

def reserved (s : State) (r : Nat) : Int := s.positive r - s.negative r
def available (s : State) (r : Nat) : Int := reserved s r - s.allocated r

def bump (f : Nat → Int) (r : Nat) (n : Int) : Nat → Int :=
  fun k => if k = r then f k + n else f k

/-- Joining an emitted delta into its source state. -/
def transfer (s : State) (source target : Nat) (amount : Int) : State :=
  if amount > available s source then s
  else if amount > 0 then
    { s with positive := bump s.positive target amount,
             negative := bump s.negative source amount }
  else if amount < 0 then
    { s with positive := bump s.positive source (-amount),
             negative := bump s.negative target (-amount) }
  else s

/-- Scala compares `(available, UID)` lexicographically. Nat fixes an explicit
UID order for the candidate; the donor is the greatest pair. -/
def pairLE (a b : Int × Nat) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

noncomputable def extremes (s : State) : Option ((Int × Nat) × (Int × Nat)) :=
  s.participants.toList.foldl (fun acc r =>
    let p := (available s r, r)
    match acc with
    | none => some (p,p)
    | some (lo,hi) => some ((if pairLE p lo then p else lo),
                           (if pairLE hi p then p else hi))) none

/-- Empty-participant rebalance is a no-op here; Scala `.max` throws.
Reachable initialized states always have a participant. -/
noncomputable def rebalance (s : State) (source : Nat) : State :=
  match extremes s with
  | none => s
  | some (lo,hi) =>
    if hi.2 = source then transfer s source lo.2 ((hi.1 - lo.1) / 2) else s

noncomputable def update (s : State) (e : Op Action) : State :=
  match e.op with
  | .addParticipants ids => { s with participants := s.participants ∪ ids }
  | .allocate n => if n < 0 ∨ available s e.2.1 < n then s
    else { s with allocated := bump s.allocated e.2.1 n }
  | .transfer n target => transfer s e.2.1 target n
  | .rebalance => rebalance s e.2.1

/-- Aegis's derived join ignores the MRDT base and takes pointwise maxima. -/
def merge (_base a b : State) : State :=
  ⟨fun r => max (a.positive r) (b.positive r),
   fun r => max (a.negative r) (b.negative r),
   fun r => max (a.allocated r) (b.allocated r), a.participants ∪ b.participants⟩

inductive Query where | available (replica : Nat) | reserved (replica : Nat) | allocated (replica : Nat)

def query (s : State) : Query → Int
  | .available r => available s r
  | .reserved r => reserved s r
  | .allocated r => s.allocated r

noncomputable def D (capacity owner : Nat) : MRDTSig where
  State := State
  dec_state := fun _ _ => Classical.propDecidable _
  init := initial capacity owner
  AppOp := Action
  dec_op := inferInstance
  Query := Query
  Value := Int
  update := update
  query := query
  merge := merge

@[ext] theorem state_ext {s t : State}
    (p : ∀ r, s.positive r = t.positive r)
    (n : ∀ r, s.negative r = t.negative r)
    (a : ∀ r, s.allocated r = t.allocated r)
    (parts : s.participants = t.participants) : s = t := by
  cases s; cases t
  simp_all only [State.mk.injEq]
  exact ⟨funext p, funext n, funext a, trivial⟩

theorem merge_comm (base a b : State) : merge base a b = merge base b a := by
  apply state_ext
  · intro r; exact max_comm _ _
  · intro r; exact max_comm _ _
  · intro r; exact max_comm _ _
  · exact Finset.union_comm _ _

/-- Initialization is neutral only on states that already contain its credit. -/
def ExtendsInitial (capacity owner : Nat) (s : State) : Prop :=
  (∀ r, (initial capacity owner).positive r ≤ s.positive r) ∧
  (∀ r, 0 ≤ s.negative r) ∧ (∀ r, 0 ≤ s.allocated r) ∧ owner ∈ s.participants

theorem merge_initial {capacity owner : Nat} {s : State}
    (h : ExtendsInitial capacity owner s) :
    merge (initial capacity owner) (initial capacity owner) s = s := by
  apply state_ext
  · intro r; exact max_eq_right (h.1 r)
  · intro r; exact max_eq_right (h.2.1 r)
  · intro r; exact max_eq_right (h.2.2.1 r)
  · simp only [merge, initial, Finset.singleton_union]
    exact Finset.insert_eq_of_mem h.2.2.2

end Sal.MRDTs.Instances.TransferableBoundedCounter.BismuthSource
