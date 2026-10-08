import Smt

-- The implication alone does not establish q.
theorem missingPremise (p q : Prop) (hpq : p → q) : q := by
  smt (timeout := some 10) [hpq]
