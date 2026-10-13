import Sal.MRDTs.Paper1.ConcreteCommutingVCReplay

/-! Balegas et al., SRDS 2015, §III-B, Figure 1: the lower-bounded
counter with single-writer cumulative rows and componentwise maximum merge.
`Nat` amounts encode the paper's nonnegative operation amounts. The fixed
replica universe is `Finset.range n`; lower bound `K` is an object parameter.
Transfer targets must differ from the source, as required by the prose's
"other replica" interpretation (a diagonal entry records increments).
The update is the effect of an accepted request; guards belong to issuance. -/
namespace Sal.MRDTs.Instances.BalegasBoundedCounter
open Foundation

inductive Action where
  | increment (amount : Nat)
  | decrement (amount : Nat)
  | transfer (amount target : Nat)
  deriving DecidableEq

structure State where
  R : Nat → Nat → Nat
  U : Nat → Nat

def initial : State := ⟨fun _ _ => 0, fun _ => 0⟩
def localRights (n : Nat) (s : State) (r : Nat) : Int :=
  (s.R r r : Int) +
  ∑ j ∈ (Finset.range n).erase r, (s.R j r : Int) -
  ∑ j ∈ (Finset.range n).erase r, (s.R r j : Int) - (s.U r : Int)
def value (n : Nat) (K : Int) (s : State) : Int :=
  K + ∑ r ∈ Finset.range n, (s.R r r : Int) - ∑ r ∈ Finset.range n, (s.U r : Int)

def bump (f : Nat → Nat) (r amount : Nat) : Nat → Nat :=
  fun k => f k + if k = r then amount else 0
def bumpMatrix (f : Nat → Nat → Nat) (r c amount : Nat) : Nat → Nat → Nat :=
  fun i j => f i j + if i = r ∧ j = c then amount else 0

def update (s : State) (e : Op Action) : State := match e.op with
  | .increment amount => {s with R := bumpMatrix s.R e.2.1 e.2.1 amount}
  | .decrement amount => {s with U := bump s.U e.2.1 amount}
  | .transfer amount target => {s with R := bumpMatrix s.R e.2.1 target amount}

def applicable (n : Nat) (s : State) (e : Op Action) : Prop :=
  e.2.1 < n ∧ match e.op with
  | .increment _ => True
  | .decrement amount => (amount : Int) ≤ localRights n s e.2.1
  | .transfer amount target => target < n ∧ target ≠ e.2.1 ∧
      (amount : Int) ≤ localRights n s e.2.1

/-- The third input is the received state; the ancestor is unused. -/
def merge (_base a b : State) : State :=
  ⟨fun i j => max (a.R i j) (b.R i j), fun i => max (a.U i) (b.U i)⟩

inductive Query where
  | value
  | localRights (replica : Nat)
  deriving DecidableEq

def query (n : Nat) (K : Int) (s : State) : Query → Int
  | .value => value n K s
  | .localRights r => localRights n s r

noncomputable def D (n : Nat) (K : Int) : MRDTSig where
  State := State
  dec_state := fun _ _ => Classical.propDecidable _
  init := initial
  AppOp := Action
  dec_op := inferInstance
  Query := Query
  Value := Int
  update := update
  query := query n K
  merge := merge

def generation (n : Nat) (K : Int) : Issuance (D n K) where
  CanIssue := fun e s => applicable n s e

@[ext] theorem state_ext {s t : State}
    (hR : ∀ i j, s.R i j = t.R i j) (hU : ∀ i, s.U i = t.U i) : s = t := by
  cases s; cases t
  simp_all only [State.mk.injEq]
  exact ⟨funext (fun i => funext (hR i)),funext hU⟩

theorem all_comm (n : Nat) (K : Int) : ∀ a b : Op Action,
    (D n K).toUpdateSig.commutes a b := by
  rintro ⟨ta,ra,oa⟩ ⟨tb,rb,ob⟩ s
  change update (update s (ta,ra,oa)) (tb,rb,ob) =
    update (update s (tb,rb,ob)) (ta,ra,oa)
  cases oa <;> cases ob <;> apply state_ext
  all_goals intros
  all_goals simp only [update, Op.op, bump, bumpMatrix]
  all_goals omega

theorem merge_comm (l a b : State) : merge l a b = merge l b a := by
  apply state_ext <;> intros <;> simp [merge, Nat.max_comm]
theorem merge_initial (s : State) : merge initial initial s = s := by
  apply state_ext <;> intros <;> simp [merge, initial]
theorem merge_idempotent (l s : State) : merge l s s = s := by
  apply state_ext <;> intros <;> simp [merge]
theorem merge_assoc (l₁ l₂ a b c : State) :
    merge l₁ (merge l₂ a b) c = merge l₂ a (merge l₁ b c) := by
  apply state_ext <;> intros <;> simp [merge, Nat.max_assoc]

/-- Repeating a delivered snapshot cannot duplicate rights or consumption. -/
theorem snapshot_delivery_idempotent (base s incoming : State) :
    merge base (merge base s incoming) incoming = merge base s incoming := by
  apply state_ext <;> intros <;> simp [merge, Nat.max_assoc]

end Sal.MRDTs.Instances.BalegasBoundedCounter
