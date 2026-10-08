import Auto.Tactic
set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints.limitedRws false
set_option trace.auto.smt.result true
 theorem cvc5TrueControl (P Q : Prop) (h : P) (f : P → Q) : Q := by auto
#print axioms cvc5TrueControl
example (P Q : Prop) (h : P) : True := by
  fail_if_success have : Q := by auto
  trivial
