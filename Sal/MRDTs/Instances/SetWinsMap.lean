import Sal.MRDTs.Paper1.ConcreteVCExecution
import Mathlib.Data.Finset.Basic

/-! Faithful finite-state port of Neem's `Set-wins_map/App_mrdt.fst`.
The source has no query. We expose a multimap lookup, because Set retains
older values even at the same key. The selected lookup is accumulating,
not overwriting; the source itself does not specify a query. -/
namespace Sal.MRDTs.Instances.SetWinsMap
open Foundation Sal.MRDTs.Paper1
inductive Action where
  | set (key value : Nat)
  | del (key : Nat)
  deriving DecidableEq, Repr
abbrev Record := Nat × (Nat × Nat)
abbrev State := Finset Record

def update (s : State) (e : Op Action) : State := match e.op with
  | .set k v => insert (e.time,(k,v)) s
  | .del k => s.filter (fun p => p.2.1 ≠ k)

def merge (l a b : State) : State := (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

def lookup (s : State) (k : Nat) : Finset Nat :=
  (s.filter (fun p => p.2.1 = k)).image (fun p => p.2.2)

def D : MRDTSig where
  State := State
  dec_state := inferInstance
  init := ∅
  AppOp := Action
  dec_op := inferInstance
  Query := Nat
  Value := Finset Nat
  update := update
  merge := merge
  query := lookup

def order (a b : Op Action) : OrderResult := match a.op,b.op with
  | .del k,.set j _ => if k=j then .Fst_then_snd else .Either
  | .set k _,.del j => if k=j then .Snd_then_fst else .Either
  | _,_ => .Either

/-- Neem's ordering is Del k before Set k v. -/
def policy : OperationPolicy Action where
  before a b := ∃ k v, a = .del k ∧ b = .set k v

def issuance : Issuance D where
  CanIssue := fun _ _ => True

/-- The source's nested unions have the same finite membership semantics. -/
theorem source_merge (l a b : State) :
    merge l a b = (l ∩ (a ∩ b)) ∪ ((a \ l) ∪ (b \ l)) := by
  ext p
  simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
  tauto

@[simp] theorem source_set (s : State) (t r k v : Nat) :
    update s (t,r,.set k v) = insert (t,(k,v)) s := rfl

@[simp] theorem source_del (s : State) (t r k : Nat) :
    update s (t,r,.del k) = s.filter (fun p => p.2.1 ≠ k) := rfl

/-- Source positive timestamps are a subset of the Lean carrier. Updates and
merge agree with the source on that subset; zero is only used in proof states. -/
def Positive (s : State) := ∀ p ∈ s, 0 < p.1

theorem positive_update (s : State) (e : Op Action) (hs : Positive s) (ht : 0 < e.time) :
    Positive (update s e) := by
  intro p hp
  rcases e with ⟨t,r,op⟩; cases op <;> simp [update,Op.op] at hp
  · rcases hp with rfl | hp
    · exact ht
    · exact hs p hp
  · exact hs p hp.1

theorem positive_merge (l a b : State) (ha : Positive a) (hb : Positive b) :
    Positive (merge l a b) := by
  intro p hp
  simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff] at hp
  rcases hp with (h | h) | h
  · exact ha p h.1.2
  · exact ha p h.1
  · exact hb p h.1
end Sal.MRDTs.Instances.SetWinsMap
