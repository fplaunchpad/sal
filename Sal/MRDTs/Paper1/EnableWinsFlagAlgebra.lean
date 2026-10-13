import Sal.MRDTs.Instances.EnableWinsFlag

set_option maxHeartbeats 4000000

namespace Sal.MRDTs.Paper1.NeemFlagAlgebra
open Foundation Instances.NeemFlag

/-- Binary comparison join used only to prove the source ternary equations.
At equal counters false dominates, because a reset observes that same epoch. -/
def joinCell (a b : Cell) : Cell :=
  (max a.1 b.1, if a.1 < b.1 then b.2 else if b.1 < a.1 then a.2 else a.2 && b.2)
def join (a b : State) : State := fun r => joinCell (a r) (b r)

theorem source_join_of_min (l a b : Cell) (h : l.1 = min a.1 b.1) :
    mergeCell l a b = joinCell a b := by
  obtain ⟨lc,lf⟩ := l
  obtain ⟨ac,af⟩ := a
  obtain ⟨bc,bf⟩ := b
  cases af <;> cases bf
  all_goals simp only [mergeCell,mergeFlag,joinCell,Bool.and_true,Bool.and_false,
    Bool.true_and,Bool.false_and,Bool.not_true,Bool.not_false,ite_true,ite_false]
  all_goals (try split_ifs) <;> simp_all <;> omega

theorem joinCell_comm (a b : Cell) : joinCell a b = joinCell b a := by
  obtain ⟨ac,af⟩ := a
  obtain ⟨bc,bf⟩ := b
  cases af <;> cases bf
  all_goals simp only [joinCell,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and]
  all_goals split_ifs <;> simp_all <;> omega

theorem joinCell_idem (a : Cell) : joinCell a a = a := by
  cases a
  simp [joinCell]

theorem joinCell_assoc (a b c : Cell) : joinCell (joinCell a b) c = joinCell a (joinCell b c) := by
  obtain ⟨ac,af⟩ := a
  obtain ⟨bc,bf⟩ := b
  obtain ⟨cc,cf⟩ := c
  cases af <;> cases bf <;> cases cf
  all_goals simp only [joinCell]
  all_goals split_ifs <;> simp_all <;> omega

theorem source_comm (l a b : State) : merge l a b = merge l b a := by
  funext r
  unfold merge mergeCell mergeFlag
  cases (a r).2 <;> cases (b r).2 <;> simp <;> omega

theorem source_as_join (l a b : State) (h : ∀ r, (l r).1 = min (a r).1 (b r).1) :
    merge l a b = join a b := by
  funext r
  exact source_join_of_min (l r) (a r) (b r) (h r)

theorem join_comm (a b : State) : join a b = join b a := by
  funext r; exact joinCell_comm (a r) (b r)
theorem join_assoc (a b c : State) : join (join a b) c = join a (join b c) := by
  funext r; exact joinCell_assoc (a r) (b r) (c r)
theorem join_idem (a : State) : join a a = a := by
  funext r; exact joinCell_idem (a r)

theorem join_local (t b c : State) : join (join t c) b = join (join t b) c := by
  rw [join_assoc,join_comm c b,← join_assoc]

theorem join_shared (t₁ t₂ c : State) :
    join (join t₁ c) (join t₂ c) = join (join t₁ t₂) c := by
  rw [join_assoc,← join_assoc c t₂ c,join_comm c t₂,join_assoc t₂ c c,join_idem,
    ← join_assoc]

end Sal.MRDTs.Paper1.NeemFlagAlgebra
