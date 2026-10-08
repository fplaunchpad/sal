import Auto.Tactic
set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"
set_option trace.auto.smt.result true
 theorem z3TrueControl (P Q : Prop) (h : P) (f : P → Q) : Q := by auto
#print axioms z3TrueControl
example (P Q : Prop) (h : P) : True := by
  fail_if_success have : Q := by auto
  trivial
