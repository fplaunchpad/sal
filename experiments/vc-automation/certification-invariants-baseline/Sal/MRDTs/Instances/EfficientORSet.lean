import Sal.MRDTs.Metatheory.Correctness

/-! Neem's efficient OR-set. The public certificate is in `EfficientORSetCertified`.
The operation and merge definitions follow the cached F★ OR-set-efficient
implementation. No removed-tag store occurs in the concrete or abstract state.
-/
namespace Sal.MRDTs.Instances.EfficientORSet

open Sal.MRDTs.Foundation

inductive SetOp (α : Type) where
  | add (element : α)
  | remove (element : α)
  deriving DecidableEq

abbrev Record (α : Type) := Replica × Timestamp × α
abbrev State (α : Type) := Finset (Record α)

variable {α : Type} [DecidableEq α]

def update (s : State α) (e : Op (SetOp α)) : State α :=
  match e.2.2 with
  | .add x => insert (e.2.1, e.1, x)
      (s.filter fun p => ¬ (p.1 = e.2.1 ∧ p.2.2 = x))
  | .remove x => s.filter fun p => p.2.2 ≠ x

def merge (l a b : State α) : State α :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

def elements (s : State α) : Finset α := s.image fun p => p.2.2

def D (α : Type) [DecidableEq α] : MRDTSig where
  State := State α
  dec_state := inferInstance
  init := ∅
  AppOp := SetOp α
  dec_op := inferInstance
  Query := α
  Value := Bool
  update := update
  merge := merge
  query s x := decide (x ∈ elements s)

def rc : ReplayPolicy (D α).toUpdateSig where
  order a b := match a.2.2, b.2.2 with
    | .remove x, .add y => if x = y then .Fst_then_snd else .Either
    | .add x, .remove y => if x = y then .Snd_then_fst else .Either
    | _, _ => .Either

/-- No state-dependent guard is required by Neem's Add/Rem API.
Fresh timestamps and sequential use of a replica belong to execution. -/
def issuance : Issuance (D α) where
  CanIssue _ _ := True

def setStep (s : Finset α) (e : Op (SetOp α)) : Finset α :=
  match e.2.2 with
  | .add x => insert x s
  | .remove x => s.erase x

def spec : SequentialSpec (D α) where
  State := Finset α
  init := ∅
  step := setStep
  Legal _ := True
  query s x := decide (x ∈ s)

def stateRel (s : State α) (q : Finset α) : Prop := elements s = q

/-- At most one timestamp is stored for each replica/element pair. -/
def KeyUnique (s : State α) : Prop :=
  ∀ r t u x, (r,t,x) ∈ s → (r,u,x) ∈ s → t = u

theorem keyUnique_empty : KeyUnique (∅ : State α) := by simp [KeyUnique]

theorem keyUnique_update {s : State α} (h : KeyUnique s) (e : Op (SetOp α)) :
    KeyUnique (update s e) := by
  rcases e with ⟨et, er, op⟩
  intro r t u x ht hu
  cases op with
  | add y =>
    simp only [update, Finset.mem_insert, Finset.mem_filter, Prod.mk.injEq] at ht hu
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact ht.2.1.trans hu.2.1.symm
    · exact False.elim (hu.2 ⟨ht.1, ht.2.2⟩)
    · exact False.elim (ht.2 ⟨hu.1, hu.2.2⟩)
    · exact h r t u x ht.1 hu.1
  | remove y =>
    simp only [update, Finset.mem_filter] at ht hu
    exact h r t u x ht.1 hu.1

theorem keyUnique_fold (ops : List (Op (SetOp α))) {s : State α}
    (h : KeyUnique s) : KeyUnique (ops.foldl update s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons e ops ih => exact ih (keyUnique_update h e)

theorem merge_comm (l a b : State α) : merge l a b = merge l b a := by
  ext p
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem merge_init (s : State α) : merge ∅ ∅ s = s := by simp [merge]

theorem elements_update (s : State α) (e : Op (SetOp α)) :
    elements (update s e) = setStep (elements s) e := by
  rcases e with ⟨t, r, op⟩
  cases op with
  | add x =>
    ext y
    simp only [elements, update, setStep, Finset.mem_image, Finset.mem_insert,
      Finset.mem_filter]
    constructor
    · rintro ⟨p, hp | hp, hpy⟩
      · subst p; exact Or.inl hpy.symm
      · exact Or.inr ⟨p, hp.1, hpy⟩
    · rintro (h | ⟨p, hp, hpy⟩)
      · exact ⟨(r,t,x), Or.inl rfl, h.symm⟩
      · by_cases hy : y = x
        · exact ⟨(r,t,x), Or.inl rfl, hy.symm⟩
        · exact ⟨p, Or.inr ⟨hp, fun h => hy (hpy.symm.trans h.2)⟩, hpy⟩
  | remove x =>
    ext y
    simp only [elements, update, setStep, Finset.mem_image, Finset.mem_filter,
      Finset.mem_erase]
    constructor
    · rintro ⟨p, ⟨hp, hpx⟩, hpy⟩
      exact ⟨fun h => hpx (hpy.trans h), p, hp, hpy⟩
    · rintro ⟨hy, p, hp, hpy⟩
      exact ⟨p, ⟨hp, fun h => hy (hpy.symm.trans h)⟩, hpy⟩

theorem elements_fold (ops : List (Op (SetOp α))) (s : State α) :
    elements (ops.foldl update s) = ops.foldl setStep (elements s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons e ops ih => simpa only [List.foldl_cons, elements_update] using ih (update s e)

theorem sequential_refinement (ops : List (Op (SetOp α))) :
    stateRel (applySeq (D α).toUpdateSig (D α).init ops) (spec.run ops) := by
  simpa [stateRel, applySeq, D, spec, SequentialMachine.run, elements] using
    elements_fold ops (∅ : State α)

/-- Public sequential refinement for any replay witness supplied by the
execution proof. This does not assert the missing replay-adequacy premise. -/
def sequentialCorrectness :
    SequentialCorrectnessCertificate (D α) issuance rc spec stateRel where
  sound := by
    intro C _exec replay v state E hver
    obtain ⟨ops, hp, hr, hf⟩ := replay v state E hver
    have hrel := sequential_refinement (α := α) ops
    rw [hf] at hrel
    refine ⟨ops, hp, hr, True.intro, hrel, ?_⟩
    intro x
    change decide ((x : α) ∈ elements state) =
      decide ((x : α) ∈ ops.foldl setStep (∅ : Finset α))
    change elements state = ops.foldl setStep (∅ : Finset α) at hrel
    exact congrArg (fun (q : Finset α) => decide ((x : α) ∈ q)) hrel

theorem rc_acyclic : @RcAcyclic (D α).toUpdateSig rc := by
  letI : ReplayPolicy (D α).toUpdateSig := rc
  apply rcAcyclic_of_noRcChain
  rintro a b c ⟨hab, hbc⟩
  rcases a with ⟨ta, ra, oa⟩
  rcases b with ⟨tb, rb, ob⟩
  rcases c with ⟨tc, rc', oc⟩
  cases oa <;> cases ob <;> cases oc <;>
    simp_all [UpdateSig.replayOrder, rc]
  all_goals first
    | (split at hab <;> simp_all)
    | (split at hbc <;> simp_all)

namespace SPOT
def a : Op (SetOp Nat) := (1, 0, .add 7)
def a' : Op (SetOp Nat) := (2, 0, .add 7)
def b : Op (SetOp Nat) := (3, 1, .add 7)
def rem : Op (SetOp Nat) := (4, 2, .remove 7)

theorem local_add_replaces : update (update ∅ a) a' = {(0,2,7)} := by decide
theorem replicas_keep_distinct_records :
    update (update ∅ a') b = {(0,2,7), (1,3,7)} := by decide
theorem remove_keeps_no_tombstones : update (update ∅ a) rem = ∅ := by decide
theorem observed_remove_not_union :
    merge (update ∅ a) (update (update ∅ a) rem) (update ∅ a) = ∅ := by decide
theorem concurrent_add_wins :
    merge (update ∅ a) (update (update ∅ a) rem) (update (update ∅ a) b)
      = {(1,3,7)} := by decide
theorem union_would_resurrect :
    (update (update ∅ a) rem ∪ update ∅ a) ≠
      merge (update ∅ a) (update (update ∅ a) rem) (update ∅ a) := by decide
theorem same_replica_adds_not_commuting :
    ¬ (D Nat).toUpdateSig.commutes a a' := by
  intro h
  have bad := h (∅ : State Nat)
  change update (update ∅ a) a' = update (update ∅ a') a at bad
  have ne : update (update ∅ a) a' ≠ update (update ∅ a') a := by decide
  exact ne bad

theorem all_state_replay_laws_unavailable :
    ¬ @ReplayLaws (D Nat).toUpdateSig rc := by
  letI : ReplayPolicy (D Nat).toUpdateSig := rc
  intro laws
  have h := laws.noncomm_covered a a' same_replica_adds_not_commuting
  simpa [UpdateSig.rc, ReplayPolicy.Before, rc, a, a'] using h

/-- Arbitrary independent replay choices cannot be used as merge premises.
All three singleton states are folds of permutations of the same three adds,
but their merge is not the fold of any sequential execution. -/
def a'' : Op (SetOp Nat) := (3, 0, .add 7)

theorem three_replay_choices :
    [a', a'', a].foldl update ∅ = {(0,1,7)} ∧
    [a, a'', a'].foldl update ∅ = {(0,2,7)} ∧
    [a, a', a''].foldl update ∅ = {(0,3,7)} := by decide

theorem incompatible_replays_merge_not_a_fold :
    ∀ ops : List (Op (SetOp Nat)),
      ops.foldl update ∅ ≠ merge {(0,1,7)} {(0,2,7)} {(0,3,7)} := by
  intro ops heq
  have h := keyUnique_fold ops keyUnique_empty
  rw [heq] at h
  have bad := h 0 2 3 7 (by decide) (by decide)
  exact (by decide : (2 : Nat) ≠ 3) bad
end SPOT

#print axioms sequential_refinement
#print axioms sequentialCorrectness
#print axioms rc_acyclic
#print axioms keyUnique_fold
#print axioms SPOT.incompatible_replays_merge_not_a_fold
end Sal.MRDTs.Instances.EfficientORSet
