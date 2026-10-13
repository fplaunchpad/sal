import Sal.MRDTs.Paper1.EnableWinsFlagReplay

/-! Independent Boolean machines for both source flag polarities. Winning
requests set the physical Boolean true; reset requests set it false. The
client sees that value directly or negated according to `invert`. -/
namespace Sal.MRDTs.Paper1.NeemFlagEvent
open Foundation Instances.NeemFlag
open Classical

abbrev Event := Op Action

def boolStep (invert : Bool) (_ : Bool) (e : Event) : Bool := match e.op with
  | .reset => invert
  | .winning => !invert

def machine (initialFlag invert : Bool) : DeterministicSpec Event Unit Bool where
  State := Bool
  initial := if invert then !initialFlag else initialFlag
  update := boolStep invert
  query := fun b _ => b

def spec (initialFlag invert : Bool) := (machine initialFlag invert).toSpec

def simulation (initialFlag invert : Bool) : EventSequentialSimulation (D initialFlag invert) (machine initialFlag invert) where
  Rel s b := (if invert then !active s else active s) = b
  initial := by simp [D,machine,active_initial]
  update := by
    intro s b _ e
    rcases e with ⟨ts,rep,op⟩
    cases op <;> cases invert <;> simp [D,machine,boolStep,active_winning,active_reset,Op.op]
  observes := by intro s b h q; cases q; exact h

theorem historySound (initialFlag invert : Bool) :
    EventFoldHistorySound (D initialFlag invert) (spec initialFlag invert) :=
  (simulation initialFlag invert).sound

variable (initialFlag invert : Bool)
/-- Equal requests commute for any event metadata, including one issuer. -/
theorem same_action_commutes (a b : Event) (same : a.op = b.op) :
    (D initialFlag invert).toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  simp only [Op.op] at same
  subst ob
  cases oa <;> funext r <;> simp only [D,update,Op.op]
  all_goals split_ifs <;> simp_all <;> omega

/-- A reset and a disable have opposite scalar observations in the two orders. -/
theorem different_action_noncommutes (a b : Event) (different : a.op ≠ b.op) :
    ¬ (D initialFlag invert).toUpdateSig.commutes a b := by
  intro comm
  have h := congrArg active (comm (initial initialFlag))
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  cases oa <;> cases ob <;> simp [Op.op] at different
  · simp only [D] at h
    rw [active_reset,active_winning] at h
    contradiction
  · simp only [D] at h
    rw [active_winning,active_reset] at h
    contradiction

private theorem language_commutes (a b : Event)
    (swap : ∀ s, (machine initialFlag invert).update ((machine initialFlag invert).update s a) b = (machine initialFlag invert).update ((machine initialFlag invert).update s b) a) :
    (spec initialFlag invert).Commutes a b := by
  intro pre suf
  have exchange (x y : Event)
      (hs : ∀ s, (machine initialFlag invert).update ((machine initialFlag invert).update s x) y = (machine initialFlag invert).update ((machine initialFlag invert).update s y) x) :
      (spec initialFlag invert).admits (pre ++ [.update x, .update y] ++ suf) →
      (spec initialFlag invert).admits (pre ++ [.update y, .update x] ++ suf) := by
    rintro ⟨final, run⟩
    have run' : Runs (machine initialFlag invert).machine.transition (machine initialFlag invert).initial
        (pre ++ ([.update x, .update y] ++ suf)) final := by
      simpa only [List.append_assoc] using run
    obtain ⟨mid,hpre,pairSuffix⟩ := run'.split pre ([.update x, .update y] ++ suf)
    obtain ⟨afterPair,pair,suffix⟩ := pairSuffix.split [.update x, .update y] suf
    cases pair with
    | cons hx rest =>
      cases rest with
      | cons hy rest =>
        cases rest
        change _ = (machine initialFlag invert).update mid x at hx
        subst hx
        change _ = (machine initialFlag invert).update ((machine initialFlag invert).update mid x) y at hy
        subst hy
        rw [hs mid] at suffix
        exact ⟨final,by
          simpa only [List.append_assoc] using hpre.append
            (Runs.cons (l := SeqLabel.update y) (m := (machine initialFlag invert).update mid y)
              (show (machine initialFlag invert).machine.transition mid (.update y) ((machine initialFlag invert).update mid y) from rfl)
              (Runs.cons (l := SeqLabel.update x) (m := (machine initialFlag invert).update ((machine initialFlag invert).update mid y) x)
                (show (machine initialFlag invert).machine.transition ((machine initialFlag invert).update mid y) (.update x) ((machine initialFlag invert).update ((machine initialFlag invert).update mid y) x) from rfl) suffix))⟩
  exact ⟨exchange a b swap,exchange b a (fun s => (swap s).symm)⟩

theorem compatible : CommutationCompatibility (D initialFlag invert) id (spec initialFlag invert) := by
  intro a b commute
  have same : a.op = b.op := by
    by_contra different
    exact different_action_noncommutes initialFlag invert a b different commute
  apply language_commutes initialFlag invert
  intro s
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  simp only [Op.op] at same
  subst ob
  cases oa <;> rfl

private def CountEq (s t : State) : Prop := ∀ r, (s r).1 = (t r).1

private theorem countEq_update {s t : State} (h : CountEq s t) (e : Event) :
    CountEq (update s e) (update t e) := by
  intro r
  rcases e with ⟨ts,rep,op⟩
  cases op <;> simp only [update,Op.op]
  · split_ifs <;> simp [h r]
  · exact h r

private theorem countEq_fold {s t : State} (h : CountEq s t) (ops : List Event) :
    CountEq (applySeq (D initialFlag invert).toUpdateSig s ops)
      (applySeq (D initialFlag invert).toUpdateSig t ops) := by
  induction ops generalizing s t with
  | nil => exact h
  | cons e rest ih => exact ih (countEq_update h e)

private theorem reset_eq {s t : State} (h : CountEq s t) {e : Event} (reset : e.op = .reset) :
    update s e = update t e := by
  funext r
  simp [update,reset,h r]

def laws : GuardedReplay.Laws (D initialFlag invert).toUpdateSig NeemFlagReplay.policy where
  noncomm_exact a b _ _ := by
    by_cases same : a.op = b.op
    · have commute := same_action_commutes initialFlag invert a b same
      have no : ¬ (NeemFlagReplay.policy.before a.op b.op ∨ NeemFlagReplay.policy.before b.op a.op) := by
        rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
        simp only [Op.op] at same
        subst ob
        cases oa <;> simp [NeemFlagReplay.policy,Op.op]
      exact ⟨fun h => (h commute).elim,fun h => (no h).elim⟩
    · have notcommute := different_action_noncommutes initialFlag invert a b same
      have edge : NeemFlagReplay.policy.before a.op b.op ∨ NeemFlagReplay.policy.before b.op a.op := by
        rcases a with ⟨ta,ra,oa⟩; rcases b with ⟨tb,rb,ob⟩
        cases oa <;> cases ob <;> simp [Op.op] at same ⊢
        all_goals simp [NeemFlagReplay.policy,Op.op]
      exact ⟨fun _ => edge,fun _ => notcommute⟩
  no_chain a b c _ _ := by
    simp only [NeemFlagReplay.policy]
    rintro ⟨⟨_,hb⟩,⟨hb',_⟩⟩
    exact Action.noConfusion (hb.symm.trans hb')
  conditional_commutation s a b c between _ _ _ edge conflict := by
    have ar : a.op = .reset := edge.1
    have bw : b.op = .winning := edge.2
    have cr : c.op = .reset := by
      rcases c with ⟨tc,rc,oc⟩
      cases oc with
      | reset => rfl
      | winning => exact False.elim (conflict (same_action_commutes initialFlag invert b _ bw))
    apply reset_eq (e := c) _ cr
    apply countEq_fold initialFlag invert
    intro r
    simp only [D,update,ar,bw]
    split_ifs <;> simp

#print axioms laws

#print axioms historySound
end Sal.MRDTs.Paper1.NeemFlagEvent
