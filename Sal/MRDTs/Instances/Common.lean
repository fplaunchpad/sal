/-! Boolean tautologies shared by grow-only, LCA-inclusive instances. -/

namespace Sal.MRDTs.Instances

theorem bor_rc (a b c : Bool) : ((a || b) || c) = ((a || c) || b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bor_comm (l a b : Bool) : (l || (a || b)) = (l || (b || a)) := by
  cases l <;> cases a <;> cases b <;> rfl

theorem bor_init (s : Bool) : (false || (false || s)) = s := by cases s <;> rfl

theorem bor_0op (l a b d : Bool) :
    ((l || d) || ((a || d) || (b || d))) = ((l || (a || b)) || d) := by
  cases l <;> cases a <;> cases b <;> cases d <;> rfl

theorem bor_peel (f a g d : Bool) :
    (f || ((a || d) || g)) = ((f || (a || g)) || d) := by
  cases f <;> cases a <;> cases g <;> cases d <;> rfl

theorem bor_redis (m x0 x1 x2 c : Bool) :
    ((m || (x0 || c)) || ((m || (x1 || c)) || (m || (x2 || c)))) =
      (m || ((x0 || (x1 || x2)) || c)) := by
  cases m <;> cases x0 <;> cases x1 <;> cases x2 <;> cases c <;> rfl

theorem bor_lredis (l m x c y : Bool) :
    (l || ((m || (x || c)) || y)) = (m || ((l || (x || y)) || c)) := by
  cases l <;> cases m <;> cases x <;> cases c <;> cases y <;> rfl

end Sal.MRDTs.Instances
