import VCAuto
set_option auto.native true
set_option maxHeartbeats 1000000
 theorem duperTrueControl (P Q : Prop) (h : P) (f : P → Q) : Q := by auto
#print axioms duperTrueControl
-- Negative control: a proof attempt must fail without a premise for Q.
example (P Q : Prop) (h : P) : True := by
  fail_if_success have : Q := by auto
  trivial
