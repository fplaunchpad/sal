import Sal.MRDTs.Instances.OptionalRegister
import Sal.MRDTs.Paper1.SplitPolicy

namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation Instances.OptionalRegister

/-- Neem's operation policy: concurrent Unset precedes Set. -/
def policy : OperationPolicy Action where
  before a b := a = .unset ∧ ∃ v, b = .set v

theorem sets_commute (ta ra va tb rb vb : Nat) (different : ra ≠ rb) :
    D.toUpdateSig.commutes (ta,ra,.set va) (tb,rb,.set vb) := by
  intro s
  apply State.ext
  · simp [D,update,Op.op,Op.rep,Finset.insert_comm]
  · intro r
    simp only [D,update,Op.op,Op.rep,Op.time]
    split_ifs <;> simp_all <;> omega

theorem unsets_commute (a b : Op Action) (ha : a.op = .unset) (hb : b.op = .unset) :
    D.toUpdateSig.commutes a b := by
  intro s
  apply State.ext
  · simp [D,update,ha,hb]
  · intro r; simp [D,update,ha,hb]

theorem set_unset_noncomm (ta ra va tb rb : Nat) :
    ¬ D.toUpdateSig.commutes (ta,ra,.set va) (tb,rb,.unset) := by
  intro comm
  have h := congrArg (fun s => (s.cells ra).1.2) (comm initial)
  simp [D,update,Op.op,Op.rep,Op.time] at h

theorem guarded_exact (a b : Op Action) (different : a.rep ≠ b.rep) :
    ¬ D.toUpdateSig.commutes a b ↔ policy.before a.op b.op ∨ policy.before b.op a.op := by
  rcases a with ⟨ta,ra,oa⟩
  rcases b with ⟨tb,rb,ob⟩
  change ra ≠ rb at different
  cases oa <;> cases ob
  · simp [policy,Op.op,sets_commute _ _ _ _ _ _ different]
  · rename_i v
    simpa [policy,Op.op] using set_unset_noncomm ta ra v tb rb
  · rename_i v
    have nc : ¬ D.toUpdateSig.commutes (ta,ra,.unset) (tb,rb,.set v) := by
      intro h
      exact set_unset_noncomm tb rb v ta ra (fun s => (h s).symm)
    simp [policy,Op.op,nc]
  · simp [policy,Op.op,unsets_commute (ta,ra,.unset) (tb,rb,.unset) rfl rfl]

/-- Swapping an Unset with a Set changes only the Set's row payload/bit;
all counters and the partial-map domain agree. -/
def DifferAt (r : Nat) (s t : State) : Prop :=
  s.domain = t.domain ∧ (∀ k, (s.cells k).1.1 = (t.cells k).1.1) ∧
    ∀ k, k ≠ r → s.cells k = t.cells k

theorem differ_update {s t : State} {r : Nat} (h : DifferAt r s t) (e : Op Action) :
    DifferAt r (update s e) (update t e) := by
  rcases h with ⟨domain,counts,rows⟩
  refine ⟨?_,?_,?_⟩
  · cases hop : e.op <;> simp [update,hop,domain]
  · intro k; cases hop : e.op <;> simp only [update,hop]
    · split_ifs <;> simp [counts]
    · exact counts k
  · intro k ne
    cases hop : e.op
    · simp [update,hop,counts,rows k ne]
    · simp [update,hop,counts]

theorem differ_fold {s t : State} {r : Nat} (h : DifferAt r s t) (ops : List (Op Action)) :
    DifferAt r (applySeq D.toUpdateSig s ops) (applySeq D.toUpdateSig t ops) := by
  induction ops generalizing s t with
  | nil => exact h
  | cons e rest ih => exact ih (differ_update h e)

theorem resolve_differ {s t : State} {r : Nat} (h : DifferAt r s t) (e : Op Action)
    (resolves : e.op = .unset ∨ (∃ v, e.op = .set v) ∧ e.rep = r) :
    update s e = update t e := by
  rcases h with ⟨domain,counts,rows⟩
  apply State.ext
  · cases hop : e.op <;> simp [update,hop,domain]
  · intro k
    rcases resolves with reset | ⟨⟨v,set⟩,own⟩
    · simp [update,reset,counts]
    · simp only [update,set]
      split_ifs with same
      · simp [counts]
      · exact rows k (by simpa [own] using same)

theorem conditional (s : State) (a b c : Op Action) (between : List (Op Action))
    (edge : policy.before a.op b.op) (conflict : ¬ D.toUpdateSig.commutes b c) :
    D.update (applySeq D.toUpdateSig (D.update (D.update s b) a) between) c =
      D.update (applySeq D.toUpdateSig (D.update (D.update s a) b) between) c := by
  obtain ⟨reset,v,set⟩ := edge
  have diff : DifferAt b.rep (update (update s b) a) (update (update s a) b) := by
    refine ⟨?_,?_,?_⟩
    · simp [update,reset,set]
    · intro k; simp only [update,reset,set]
      split_ifs <;> rfl
    · intro k ne; simp [update,reset,set,ne]
  have resolves : c.op = .unset ∨ (∃ v, c.op = .set v) ∧ c.rep = b.rep := by
    cases hc : c.op with
    | unset => exact Or.inl rfl
    | set w =>
      right
      refine ⟨⟨w,rfl⟩,?_⟩
      by_contra different
      rcases b with ⟨tb,rb,ob⟩
      rcases c with ⟨tc,rc,oc⟩
      simp only [Op.op] at set hc
      subst ob; subst oc
      exact conflict (sets_commute tb rb v tc rc w (by simpa [Op.rep,ne_comm] using different))
  exact resolve_differ (differ_fold diff between) c resolves

def laws : GuardedReplay.Laws D.toUpdateSig policy where
  noncomm_exact a b _ different := guarded_exact a b different
  no_chain a b c _ _ := by
    rintro ⟨⟨_,v,hb⟩,⟨hb',_,_⟩⟩
    simp [hb] at hb'
  conditional_commutation s a b c between _ _ _ := conditional s a b c between

def splitLaws : SplitPolicy.Laws D.toUpdateSig policy := SplitPolicy.Laws.ofGuarded laws

#print axioms splitLaws
end Sal.MRDTs.Paper1.OptionalRegister
