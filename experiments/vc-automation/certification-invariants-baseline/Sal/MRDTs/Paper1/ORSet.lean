import Sal.MRDTs.Framework.MergeLaws
import Sal.MRDTs.Paper1.HistorySpec

/-! The finite reachable fragment of the exact OR-set of motivation.tex, Fig. 1.
Every add is retained as an element/timestamp pair; remove erases all pairs
for its element. The ancestor is a genuine input to the three-way merge. -/
namespace Sal.MRDTs.Paper1.ORSet
open Sal.MRDTs.Foundation
variable {α : Type} [DecidableEq α]

inductive Update (α : Type) where
  | add (element : α)
  | remove (element : α)
  deriving DecidableEq, Repr

abbrev State (α : Type) := Finset (α × Timestamp)

def step (s : State α) (e : Op (Update α)) : State α :=
  match e.2.2 with
  | .add x => insert (x, e.1) s
  | .remove x => s.filter (fun p => p.1 ≠ x)

def merge (l a b : State α) : State α :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

def view (s : State α) : Finset α := s.image Prod.fst

def query (s : State α) (x : α) : Bool := decide (x ∈ view s)

def D (α : Type) [DecidableEq α] : MRDTSig where
  State := State α
  dec_state := inferInstance
  init := ∅
  AppOp := Update α
  dec_op := inferInstance
  Query := α
  Value := Bool
  update := step
  query := query
  merge := merge

def order (a b : Op (Update α)) : RcRes :=
  match a.2.2, b.2.2 with
  | .remove x, .add y => if x = y then .Fst_then_snd else .Either
  | .add x, .remove y => if x = y then .Snd_then_fst else .Either
  | _, _ => .Either

instance policy : ReplayPolicy (D α).toUpdateSig where
  order := order

@[simp] theorem rc_iff (a b : Op (Update α)) :
    (D α).toUpdateSig.rc a b ↔ ∃ x, a.2.2 = .remove x ∧ b.2.2 = .add x := by
  rcases a with ⟨ta, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  cases ao <;> cases bo <;> simp [UpdateSig.rc, ReplayPolicy.Before, policy, order]
  all_goals first | (split <;> simp_all) | exact eq_comm

@[simp] theorem mem_step (s : State α) (e : Op (Update α)) (p : α × Timestamp) :
    p ∈ step s e ↔ match e.2.2 with
    | .add x => p = (x, e.1) ∨ p ∈ s
    | .remove x => p ∈ s ∧ p.1 ≠ x := by
  rcases e with ⟨t, r, op⟩; cases op <;> simp [step]

theorem commute_of_no_conflict (a b : Op (Update α))
    (h : ¬ ((D α).toUpdateSig.rc a b ∨ (D α).toUpdateSig.rc b a)) :
    (D α).toUpdateSig.commutes a b := by
  have hh : ¬ ((∃ x, a.2.2 = .remove x ∧ b.2.2 = .add x) ∨ (∃ x, b.2.2 = .remove x ∧ a.2.2 = .add x)) := by simpa only [rc_iff] using h
  intro s
  rcases a with ⟨ta, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  change step (step s (ta, ar, ao)) (bt, br, bo) = step (step s (bt, br, bo)) (ta, ar, ao)
  cases ao <;> cases bo <;> ext p <;>
    simp [step] at hh ⊢ <;> grind

theorem noncomm_iff_rc (a b : Op (Update α)) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      ((D α).toUpdateSig.rc a b ∨ (D α).toUpdateSig.rc b a) := by
  constructor
  · exact fun hn => Classical.byContradiction (fun h => hn (commute_of_no_conflict a b h))
  · intro hr hc
    rcases hr with hr | hr
    · obtain ⟨x, ha, hb⟩ := (rc_iff a b).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : State α)) (x, b.1)
      simp [D, step, ha, hb] at h
    · obtain ⟨x, hb, ha⟩ := (rc_iff b a).mp hr
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

theorem no_rc_chain (a b c : Op (Update α)) :
    ¬ ((D α).toUpdateSig.rc a b ∧ (D α).toUpdateSig.rc b c) := by
  rintro ⟨hab, hbc⟩
  obtain ⟨x, _, hb⟩ := (rc_iff a b).mp hab
  obtain ⟨y, hb', _⟩ := (rc_iff b c).mp hbc
  rw [hb] at hb'; cases hb'

theorem replayLaws : ReplayLaws (D α).toUpdateSig := by
  refine ⟨fun a b => (noncomm_iff_rc a b).mp, ?_, ?_⟩
  · exact rcAcyclic_of_noRcChain no_rc_chain
  · intro s e a r ops _ _ _ hea har
    obtain ⟨x, he, ha⟩ := (rc_iff e a).mp hea
    have hr : r.2.2 = .remove x := by
      rcases har with h | h
      · obtain ⟨y, ha', _⟩ := (rc_iff a r).mp h
        rw [ha] at ha'; cases ha'
      · obtain ⟨y, hr, ha'⟩ := (rc_iff r a).mp h
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

def abstractStep (s : Finset α) : Update α → Finset α
  | .add x => insert x s
  | .remove x => s.erase x

def spec (α : Type) [DecidableEq α] : DeterministicSpec (Update α) α Bool where
  State := Finset α
  initial := ∅
  update := abstractStep
  query := fun s x => decide (x ∈ s)

@[simp] theorem view_empty : view (∅ : State α) = ∅ := by simp [view]

@[simp] theorem view_step (s : State α) (e : Op (Update α)) :
    view (step s e) = abstractStep (view s) e.2.2 := by
  rcases e with ⟨t, r, op⟩
  cases op with
  | add x => simp [step, view, abstractStep]
  | remove x =>
      ext y
      simp only [view, step, abstractStep, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨p, ⟨hp, hpx⟩, rfl⟩; exact ⟨hpx, p, hp, rfl⟩
      · rintro ⟨hyx, p, hp, hpy⟩; exact ⟨p, ⟨hp, hpy ▸ hyx⟩, hpy⟩

theorem view_fold (s : State α) (ops : List (Op (Update α))) :
    view (applySeq (D α).toUpdateSig s ops) =
      (ops.map Op.op).foldl abstractStep (view s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons e ops ih => simpa [applySeq, Op.op] using ih (step s e)

/-- Every implementation replay explains the client read in the independently
specified ordinary-set history language. No timestamps enter its labels. -/
theorem history_bridge (ops : List (Op (Update α))) (x : α) :
    (spec α).toSpec.admits
      (DeterministicSpec.updateLabels (ops.map Op.op) ++
        [.query x (query (applySeq (D α).toUpdateSig (D α).init ops) x)]) := by
  rw [DeterministicSpec.updates_query_iff]
  change decide (x ∈ view (applySeq (D α).toUpdateSig (∅ : State α) ops)) = _
  rw [view_fold, view_empty]
  rfl

end Sal.MRDTs.Paper1.ORSet
