import Smt

-- Deliberately false: its rejection is a required harness control.
theorem falseControl : (1 : Int) = 2 := by
  smt (timeout := some 10)
