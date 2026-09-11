import Sal.MRDTs.Instances.MVRContract

/-! Compact MVR implementation. The state contains only live tagged writes.
Historical writes below are proof inputs, not fields of the implementation. -/
namespace Sal.MRDTs.Instances.MVRLive
open Sal.MRDTs.Foundation
set_option maxHeartbeats 1000000

abbrev State := Finset (ℕ × ℕ)
abbrev Event := Op MVR.MVROp

def update (s : State) (e : Event) : State := MVR.clientStep s e

def merge (l a b : State) : State :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

def canIssue (e : Event) (s : State) : Prop :=
  (∀ p ∈ s, p.1 ≠ e.1) ∧
  (MVR.overwrites e).toFinset = s.image Prod.fst

instance (e : Event) (s : State) : Decidable (canIssue e s) :=
  inferInstanceAs (Decidable (_ ∧ _))

def query (s : State) : Finset ℕ := s.image Prod.snd

def D : MRDTSig where
  State := State
  dec_state := inferInstance
  init := ∅
  AppOp := MVR.MVROp
  dec_op := inferInstance
  Query := Unit
  Value := Set ℕ
  update := update
  merge := merge
  query := fun s _ => MVR.queryValues s

def rc : ReplayPolicy D.toUpdateSig where
  order := MVR.rc.order

def issuance : Issuance D where
  CanIssue := canIssue

theorem rc_acyclic : @RcAcyclic D.toUpdateSig rc := MVR.rc_acyclic

theorem issued_write_singleton (e : Event) (s : State) (h : canIssue e s) :
    update s e = {(e.1, MVR.writeValue e)} := by
  have hf : s.filter (fun p => p.1 ∉ MVR.overwrites e) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hn⟩ := Finset.mem_filter.mp hp
    apply hn
    apply List.mem_toFinset.mp
    rw [h.2]
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  simp [update, MVR.clientStep, hf]

theorem merge_self (a : State) : merge a a a = a := by simp [merge]
theorem merge_unchanged (l a : State) : merge l a l = a := by
  ext p
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto
theorem merge_comm (l a b : State) : merge l a b = merge l b a := by
  ext p
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- Finite history oracle: retain a write precisely when no event overwrites
its tag. This does not evaluate the proposed merge or replay implementation. -/
def live (history : Finset Event) : State :=
  (history.image (fun e => (e.1, MVR.writeValue e))).filter
    (fun p => ∀ e ∈ history, p.1 ∉ MVR.overwrites e)

def Born (history : Finset Event) (p : ℕ × ℕ) : Prop :=
  ∃ e ∈ history, (e.1,MVR.writeValue e) = p

def Dead (history : Finset Event) (t : ℕ) : Prop :=
  ∃ e ∈ history, t ∈ MVR.overwrites e

theorem mem_live (history : Finset Event) (p : ℕ × ℕ) :
    p ∈ live history ↔ Born history p ∧ ¬ Dead history p.1 := by
  simp [live, Born, Dead]

theorem update_live (history : Finset Event) (e : Event)
    (fresh : ¬ Dead history e.1) (self : e.1 ∉ MVR.overwrites e) :
    update (live history) e = live (insert e history) := by
  ext p
  have hborn : Born (insert e history) p ↔
      (e.1, MVR.writeValue e) = p ∨ Born history p := by
    simp [Born]
  have hdead : Dead (insert e history) p.1 ↔
      p.1 ∈ MVR.overwrites e ∨ Dead history p.1 := by
    simp [Dead]
  simp only [update, MVR.clientStep, Finset.mem_insert, Finset.mem_filter,
    mem_live, hborn, hdead]
  by_cases hp : p = (e.1, MVR.writeValue e)
  · subst p
    simp [fresh, self]
  · have hp' : (e.1, MVR.writeValue e) ≠ p := Ne.symm hp
    simp [hp, hp', and_comm, and_left_comm]

/-- Sufficient history conditions for a genuine shared ancestor. These are
proof premises, not extra data retained by the compact implementation. -/
theorem live_merge (l a b : Finset Event)
    (born_inter : ∀ p, Born l p ↔ Born a p ∧ Born b p)
    (dead_left : ∀ t, Dead l t → Dead a t)
    (dead_right : ∀ t, Dead l t → Dead b t)
    (observed_left : ∀ p, Born b p → Dead a p.1 → Born a p)
    (observed_right : ∀ p, Born a p → Dead b p.1 → Born b p) :
    merge (live l) (live a) (live b) = live (a ∪ b) := by
  ext p
  have hl := dead_left p.1
  have hr := dead_right p.1
  have ha := observed_left p
  have hb := observed_right p
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, mem_live]
  have hborn : Born (a ∪ b) p ↔ Born a p ∨ Born b p := by
    simp [Born, Finset.mem_union, or_and_right, exists_or]
  have hdead : Dead (a ∪ b) p.1 ↔ Dead a p.1 ∨ Dead b p.1 := by
    simp [Dead, Finset.mem_union, or_and_right, exists_or]
  rw [hborn, hdead, born_inter]
  tauto

/-- Each named overwrite target was born in this history. -/
def TargetsPresent (h : Finset Event) : Prop :=
  ∀ e ∈ h, ∀ t ∈ MVR.overwrites e, ∃ birth ∈ h, birth.1 = t

/-- Unlike the lower-level Boolean identity, this theorem's ancestor is
exactly the shared event history. No arbitrary representation compatibility
assumption is needed. -/
theorem merge_shared_history (a b : Finset Event)
    (unique : ∀ x ∈ a ∪ b, ∀ y ∈ a ∪ b, x.1 = y.1 → x = y)
    (ha : TargetsPresent a) (hb : TargetsPresent b) :
    merge (live (a ∩ b)) (live a) (live b) = live (a ∪ b) := by
  apply live_merge
  · intro p
    constructor
    · rintro ⟨e,he,hp⟩
      exact ⟨⟨e,(Finset.mem_inter.mp he).1,hp⟩,
        ⟨e,(Finset.mem_inter.mp he).2,hp⟩⟩
    · rintro ⟨⟨x,hx,hxp⟩,⟨y,hy,hyp⟩⟩
      have hxy := unique x (Finset.mem_union_left _ hx)
        y (Finset.mem_union_right _ hy)
        (congrArg (fun p : ℕ × ℕ => p.1) (hxp.trans hyp.symm))
      subst y
      exact ⟨x,Finset.mem_inter.mpr ⟨hx,hy⟩,hxp⟩
  · intro t h
    obtain ⟨e,he,ht⟩ := h
    exact ⟨e,(Finset.mem_inter.mp he).1,ht⟩
  · intro t h
    obtain ⟨e,he,ht⟩ := h
    exact ⟨e,(Finset.mem_inter.mp he).2,ht⟩
  · rintro p ⟨birth,hbirth,hp⟩ ⟨e,he,ht⟩
    obtain ⟨old,hold,hot⟩ := ha e he p.1 ht
    have heq := unique old (Finset.mem_union_left _ hold)
      birth (Finset.mem_union_right _ hbirth)
      (hot.trans (congrArg Prod.fst hp).symm)
    exact ⟨old,hold,heq ▸ hp⟩
  · rintro p ⟨birth,hbirth,hp⟩ ⟨e,he,ht⟩
    obtain ⟨old,hold,hot⟩ := hb e he p.1 ht
    have heq := unique old (Finset.mem_union_right _ hold)
      birth (Finset.mem_union_left _ hbirth)
      (hot.trans (congrArg Prod.fst hp).symm)
    exact ⟨old,hold,heq ▸ hp⟩

/-- Same human-reviewed sequential machine as the registered MVR. -/
def spec : SequentialSpec D where
  State := State
  init := ∅
  step := MVR.clientStep
  Legal := MVR.clientLegal
  query := fun s _ => MVR.queryValues s

theorem spec_run_eq (ops : List Event) : spec.run ops = MVR.clientSpec.run ops := rfl

theorem update_run_eq (ops : List Event) :
    applySeq D.toUpdateSig D.init ops = spec.run ops := rfl

/-- The compact chronological fold agrees with the independent history
oracle; reuse the checked abstract-machine refinement, not old merge laws. -/
theorem fold_live (ops : List Event)
    (sorted : ops.Pairwise (fun a b => a.1 ≤ b.1))
    (past : ∀ e ∈ ops, ∀ t ∈ MVR.overwrites e, t < e.1) :
    applySeq D.toUpdateSig D.init ops = live ops.toFinset := by
  apply Finset.ext
  intro p
  rw [update_run_eq, spec_run_eq]
  rw [MVR.fold_refines ops sorted past p, mem_live]
  rw [MVR.fold_write_iff]
  have hdead : (applySeq MVR.MVR.toUpdateSig MVR.MVR.init ops).2 p.1 = false ↔
      ¬ Dead ops.toFinset p.1 := by
    rw [Bool.eq_false_iff]
    exact (not_congr (MVR.fold_overwrite_iff ops p.1)).trans (by
      simp only [Dead, List.mem_toFinset])
  rw [hdead]
  simp only [Born, List.mem_toFinset]
  aesop

#print axioms merge_shared_history
#print axioms fold_live


end Sal.MRDTs.Instances.MVRLive
