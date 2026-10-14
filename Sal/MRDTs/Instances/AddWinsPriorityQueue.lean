import Sal.MRDTs.Framework.MergeLaws
import Sal.MRDTs.Paper1.HistorySpec
import Sal.MRDTs.Paper1.NaturalSetSpec
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Prod.Lex

/-! The archived add-wins priority queue: finite add records, retained signed
increment records, survivor merge for adds and union for increments. Removing
an element never resets its acquired priority. This is Sal's flattened
sum-of-increments variant, not the per-add-record Most-Change-Win algorithm
of the Internetware 2023 CRPQ paper; no observation counts are represented. -/
namespace Sal.MRDTs.Instances.AddWinsPriorityQueue
open Sal.MRDTs.Foundation
variable {α : Type} [DecidableEq α]

inductive Update (α : Type) where
  | add (element : α) (innate : Nat)
  | inc (element : α) (amount : Int)
  | remove (element : α)
  deriving DecidableEq, Repr

abbrev AddRecord (α : Type) := α × Timestamp × Nat
abbrev IncRecord (α : Type) := α × Timestamp × Int
abbrev State (α : Type) := Finset (AddRecord α) × Finset (IncRecord α)

def step (s : State α) (e : Op (Update α)) : State α :=
  match e.2.2 with
  | .add x v => (insert (x,e.1,v) s.1,s.2)
  | .inc x n => (s.1,insert (x,e.1,n) s.2)
  | .remove x => (s.1.filter (fun p => p.1 ≠ x),s.2)

def merge (l a b : State α) : State α :=
  ((l.1 ∩ a.1 ∩ b.1) ∪ (a.1 \ l.1) ∪ (b.1 \ l.1),a.2 ∪ b.2)

/-- The historical implementation applied survivor merge to increments too.
Honest ancestors have only increments retained by both branches, so its
increment component is exactly union. This is the sole raw-state extension. -/
theorem historical_increment_merge (l a b : State α)
    (left : l.2 ⊆ a.2) (right : l.2 ⊆ b.2) :
    (l.2 ∩ a.2 ∩ b.2) ∪ (a.2 \ l.2) ∪ (b.2 \ l.2) = (merge l a b).2 := by
  ext p
  have hl : p ∈ l.2 → p ∈ a.2 := fun h => left h
  have hr : p ∈ l.2 → p ∈ b.2 := fun h => right h
  simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
  tauto

/-- Latest live timestamp; the innate payload deterministically breaks ties
on raw states. Honest execution has globally unique event timestamps. -/
def winner (s : State α) (x : α) : WithBot (Lex (Timestamp × Nat)) :=
  ((s.1.filter (fun p => p.1 = x)).image (fun p => toLex p.2)).max

def acquired (s : State α) (x : α) : Int :=
  ∑ p ∈ s.2.filter (fun p => p.1 = x), p.2.2

def query (s : State α) (x : α) : Option Int :=
  Option.map (fun p => ((ofLex p).2 : Int) + acquired s x) (winner s x)

def D (α : Type) [DecidableEq α] : MRDTSig where
  State := State α
  dec_state := inferInstance
  init := (∅,∅)
  AppOp := Update α
  dec_op := inferInstance
  Query := α
  Value := Option Int
  update := step
  query := query
  merge := merge

def order (a b : Op (Update α)) : OrderResult :=
  match a.2.2, b.2.2 with
  | .remove x, .add y _ => if x = y then .Fst_then_snd else .Either
  | .add x _, .remove y => if x = y then .Snd_then_fst else .Either
  | _, _ => .Either

instance policy : EventOrder (D α).toUpdateSig where
  order := order

@[simp] theorem replayOrder_iff (a b : Op (Update α)) :
    (D α).toUpdateSig.replayBefore a b ↔ ∃ x v, a.2.2 = .remove x ∧ b.2.2 = .add x v := by
  rcases a with ⟨ta, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  cases ao <;> cases bo <;> simp [UpdateSig.replayBefore, EventOrder.Before, policy, order]
  all_goals first | (split <;> simp_all) | exact eq_comm

@[simp] theorem mem_step_adds (s : State α) (e : Op (Update α)) (p : AddRecord α) :
    p ∈ (step s e).1 ↔ match e.2.2 with
    | .add x v => p = (x,e.1,v) ∨ p ∈ s.1
    | .inc _ _ => p ∈ s.1
    | .remove x => p ∈ s.1 ∧ p.1 ≠ x := by
  rcases e with ⟨t,r,op⟩; cases op <;> simp [step]

@[simp] theorem mem_step_incs (s : State α) (e : Op (Update α)) (p : IncRecord α) :
    p ∈ (step s e).2 ↔ match e.2.2 with
    | .inc x n => p = (x,e.1,n) ∨ p ∈ s.2
    | _ => p ∈ s.2 := by
  rcases e with ⟨t,r,op⟩; cases op <;> simp [step]

theorem commute_of_no_conflict (a b : Op (Update α))
    (h : ¬ ((D α).toUpdateSig.replayBefore a b ∨ (D α).toUpdateSig.replayBefore b a)) :
    (D α).toUpdateSig.commutes a b := by
  have hh : ¬ ((∃ x v, a.2.2 = .remove x ∧ b.2.2 = .add x v) ∨ (∃ x v, b.2.2 = .remove x ∧ a.2.2 = .add x v)) := by simpa only [replayOrder_iff] using h
  intro s
  rcases a with ⟨ta, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  change step (step s (ta, ar, ao)) (bt, br, bo) = step (step s (bt, br, bo)) (ta, ar, ao)
  cases ao <;> cases bo <;> apply Prod.ext <;> ext p <;>
    simp [step] at hh ⊢ <;> grind

theorem noncomm_iff_replayOrder (a b : Op (Update α)) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      ((D α).toUpdateSig.replayBefore a b ∨ (D α).toUpdateSig.replayBefore b a) := by
  constructor
  · exact fun hn => Classical.byContradiction (fun h => hn (commute_of_no_conflict a b h))
  · intro hr hc
    rcases hr with hr | hr
    · obtain ⟨x, v, ha, hb⟩ := (replayOrder_iff a b).mp hr
      have h := Finset.ext_iff.mp (congrArg Prod.fst (hc ((∅,∅) : State α))) (x, b.1,v)
      simp [D, step, ha, hb] at h
    · obtain ⟨x, v, hb, ha⟩ := (replayOrder_iff b a).mp hr
      have h := Finset.ext_iff.mp (congrArg Prod.fst (hc ((∅,∅) : State α))) (x, a.1,v)
      simp [D, step, ha, hb] at h

def EqExcept (x : α) (a b : State α) : Prop :=
  (∀ p, p.1 ≠ x → (p ∈ a.1 ↔ p ∈ b.1)) ∧ a.2 = b.2

theorem eqExcept_step {x : α} {a b : State α} (h : EqExcept x a b)
    (e : Op (Update α)) : EqExcept x (step a e) (step b e) := by
  constructor
  · intro p hp
    rcases e with ⟨t, r, op⟩; cases op <;> simp [step, h.1 p hp]
  · rcases e with ⟨t,r,op⟩; cases op <;> simp [step,h.2]

theorem eqExcept_fold {x : α} {a b : State α} (h : EqExcept x a b)
    (ops : List (Op (Update α))) :
    EqExcept x (applySeq (D α).toUpdateSig a ops) (applySeq (D α).toUpdateSig b ops) := by
  induction ops generalizing a b with
  | nil => exact h
  | cons e ops ih => exact ih (eqExcept_step h e)

theorem no_replayOrder_chain (a b c : Op (Update α)) :
    ¬ ((D α).toUpdateSig.replayBefore a b ∧ (D α).toUpdateSig.replayBefore b c) := by
  rintro ⟨hab, hbc⟩
  obtain ⟨x, v, _, hb⟩ := (replayOrder_iff a b).mp hab
  obtain ⟨y, w, hb', _⟩ := (replayOrder_iff b c).mp hbc
  rw [hb] at hb'; cases hb'

theorem replayLaws : ReplayLaws (D α).toUpdateSig := by
  refine ⟨fun a b => (noncomm_iff_replayOrder a b).mp, ?_, ?_⟩
  · exact replayAcyclic_of_noReplayChain no_replayOrder_chain
  · intro s e a r ops _ _ _ hea har
    obtain ⟨x, v, he, ha⟩ := (replayOrder_iff e a).mp hea
    have hr : r.2.2 = .remove x := by
      rcases har with h | h
      · obtain ⟨y, w, ha', _⟩ := (replayOrder_iff a r).mp h
        rw [ha] at ha'; cases ha'
      · obtain ⟨y, w, hr, ha'⟩ := (replayOrder_iff r a).mp h
        rw [ha] at ha'; injection ha' with hxy; subst y; exact hr
    have hbase : EqExcept x (step (step s a) e) (step (step s e) a) := by
      constructor
      · intro p hp; simp [step, he, ha, hp]
      · simp [step,he,ha]
    have hfold := eqExcept_fold hbase ops
    change step _ r = step _ r
    apply Prod.ext
    · ext p
      simp only [step, hr, Finset.mem_filter]
      by_cases hp : p.1 = x
      · simp [hp]
      · exact and_congr (hfold.1 p hp) Iff.rfl
    · simpa only [step,hr] using hfold.2


end Sal.MRDTs.Instances.AddWinsPriorityQueue
