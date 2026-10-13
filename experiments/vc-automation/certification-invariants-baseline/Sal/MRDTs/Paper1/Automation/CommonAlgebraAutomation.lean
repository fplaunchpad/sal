import Sal.MRDTs.Paper1.Automation.CommonVerificationRules

/-! Registered general algebra, with instance definitions supplied locally.
No datatype theorem or completed VC is selected by this finite solver. -/
/-- Generic max idempotence in the right-associated normal form. -/
theorem mrdt_max_repeat {α : Type} [LinearOrder α] (a b : α) :
    max a (max a b) = max a b := by rw [←max_assoc,max_self]

attribute [mrdt_algebra] mrdt_max_repeat
attribute [mrdt_algebra] max_assoc max_left_comm max_comm max_self max_bot_left max_bot_right

macro "mrdt_finite" : tactic =>
  `(tactic| (intros; simp only [mrdt_implementation, mrdt_algebra]))
