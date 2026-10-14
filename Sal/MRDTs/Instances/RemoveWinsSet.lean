import Sal.MRDTs.Framework.MergeLaws
import Sal.MRDTs.Paper1.HistorySpec
import Sal.MRDTs.Paper1.NaturalSetSpec

/-! Neem's remove-wins set, generalized from its two-element universe to any
finite universe. Source pairs `(timestamp, element)` are stored with coordinates
swapped. Initial timestamp-zero removal tags, Add filtering, Rem insertion,
and the ancestor-sensitive survivor merge are unchanged. `Fin 2` is the exact
source universe under the bijection `i ↦ i.val + 1`. -/
namespace Sal.MRDTs.Instances.RemoveWinsSet
open Sal.MRDTs.Foundation
variable {α : Type} [DecidableEq α] [Fintype α]

inductive Update (α : Type) where
  | remove (element : α)
  | add (element : α)
  deriving DecidableEq, Repr

abbrev State (α : Type) := Finset (α × Timestamp)

def step (s : State α) (e : Op (Update α)) : State α :=
  match e.2.2 with
  | .remove x => insert (x, e.1) s
  | .add x => s.filter (fun p => p.1 ≠ x)

def merge (l a b : State α) : State α :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

def initial (α : Type) [DecidableEq α] [Fintype α] : State α :=
  Finset.univ.image (fun x => (x, 0))

def view (s : State α) : Finset α := Finset.univ \ s.image Prod.fst

def query (s : State α) (x : α) : Bool := decide (x ∈ view s)

def D (α : Type) [DecidableEq α] [Fintype α] : MRDTSig where
  State := State α
  dec_state := inferInstance
  init := initial α
  AppOp := Update α
  dec_op := inferInstance
  Query := α
  Value := Bool
  update := step
  query := query
  merge := merge

def order (a b : Op (Update α)) : OrderResult :=
  match a.2.2, b.2.2 with
  | .add x, .remove y => if x = y then .Fst_then_snd else .Either
  | .remove x, .add y => if x = y then .Snd_then_fst else .Either
  | _, _ => .Either

instance policy : EventOrder (D α).toUpdateSig where
  order := order

@[simp] theorem replayOrder_iff (a b : Op (Update α)) :
    (D α).toUpdateSig.replayBefore a b ↔ ∃ x, a.2.2 = .add x ∧ b.2.2 = .remove x := by
  rcases a with ⟨ta, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  cases ao <;> cases bo <;> simp [UpdateSig.replayBefore, EventOrder.Before, policy, order]
  all_goals first | (split <;> simp_all) | exact eq_comm

@[simp] theorem mem_step (s : State α) (e : Op (Update α)) (p : α × Timestamp) :
    p ∈ step s e ↔ match e.2.2 with
    | .remove x => p = (x, e.1) ∨ p ∈ s
    | .add x => p ∈ s ∧ p.1 ≠ x := by
  rcases e with ⟨t, r, op⟩; cases op <;> simp [step]

theorem commute_of_no_conflict (a b : Op (Update α))
    (h : ¬ ((D α).toUpdateSig.replayBefore a b ∨ (D α).toUpdateSig.replayBefore b a)) :
    (D α).toUpdateSig.commutes a b := by
  have hh : ¬ ((∃ x, a.2.2 = .add x ∧ b.2.2 = .remove x) ∨ (∃ x, b.2.2 = .add x ∧ a.2.2 = .remove x)) := by simpa only [replayOrder_iff] using h
  intro s
  rcases a with ⟨ta, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  change step (step s (ta, ar, ao)) (bt, br, bo) = step (step s (bt, br, bo)) (ta, ar, ao)
  cases ao <;> cases bo <;> ext p <;>
    simp [step] at hh ⊢ <;> grind

theorem noncomm_iff_replayOrder (a b : Op (Update α)) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      ((D α).toUpdateSig.replayBefore a b ∨ (D α).toUpdateSig.replayBefore b a) := by
  constructor
  · exact fun hn => Classical.byContradiction (fun h => hn (commute_of_no_conflict a b h))
  · intro hr hc
    rcases hr with hr | hr
    · obtain ⟨x, ha, hb⟩ := (replayOrder_iff a b).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : State α)) (x, b.1)
      simp [D, step, ha, hb] at h
    · obtain ⟨x, hb, ha⟩ := (replayOrder_iff b a).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : State α)) (x, a.1)
      simp [D, step, ha, hb] at h

def EqExcept (x : α) (a b : State α) : Prop :=
  ∀ p, p.1 ≠ x → (p ∈ a ↔ p ∈ b)

theorem eqExcept_step {x : α} {a b : State α} (h : EqExcept x a b)
    (e : Op (Update α)) : EqExcept x (step a e) (step b e) := by
  intro p hp
  rcases e with ⟨t, r, op⟩; cases op <;> simp [step, h p hp]

theorem eqExcept_fold {x : α} {a b : State α} (h : EqExcept x a b)
    (ops : List (Op (Update α))) :
    EqExcept x (applySeq (D α).toUpdateSig a ops) (applySeq (D α).toUpdateSig b ops) := by
  induction ops generalizing a b with
  | nil => exact h
  | cons e ops ih => exact ih (eqExcept_step h e)

theorem no_replayOrder_chain (a b c : Op (Update α)) :
    ¬ ((D α).toUpdateSig.replayBefore a b ∧ (D α).toUpdateSig.replayBefore b c) := by
  rintro ⟨hab, hbc⟩
  obtain ⟨x, _, hb⟩ := (replayOrder_iff a b).mp hab
  obtain ⟨y, hb', _⟩ := (replayOrder_iff b c).mp hbc
  rw [hb] at hb'; cases hb'

theorem replayLaws : ReplayLaws (D α).toUpdateSig := by
  refine ⟨fun a b => (noncomm_iff_replayOrder a b).mp, ?_, ?_⟩
  · exact replayAcyclic_of_noReplayChain no_replayOrder_chain
  · intro s e a r ops _ _ _ hea har
    obtain ⟨x, he, ha⟩ := (replayOrder_iff e a).mp hea
    have hr : r.2.2 = .add x := by
      rcases har with h | h
      · obtain ⟨y, ha', _⟩ := (replayOrder_iff a r).mp h
        rw [ha] at ha'; cases ha'
      · obtain ⟨y, hr, ha'⟩ := (replayOrder_iff r a).mp h
        rw [ha] at ha'; injection ha' with hxy; subst y; exact hr
    have hbase : EqExcept x (step (step s a) e) (step (step s e) a) := by
      intro p hp; simp [step, he, ha, hp]
    have hfold := eqExcept_fold hbase ops
    change step _ r = step _ r
    ext p
    simp only [step, hr, Finset.mem_filter]
    by_cases hp : p.1 = x
    · simp [hp]
    · exact and_congr (hfold p hp) Iff.rfl


end Sal.MRDTs.Instances.RemoveWinsSet
