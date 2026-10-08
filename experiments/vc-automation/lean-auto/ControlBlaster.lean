import Blaster

theorem blasterTrueControl (P Q : Prop) (h : P) (f : P → Q) : Q := by
  blaster (timeout: 10) (random-seed: 1)
#print axioms blasterTrueControl

-- The missing-premise proposition is false; the guard requires rejection.
/--
error: ❌ Falsified
---
error: Counterexample:
---
error:  - P: true
---
error:  - Q: false
---
error: Tactic `blaster` failed: Goal was falsified (see counterexample above)

⊢ ∀ (P Q : Prop), P → Q
-/
#guard_msgs (error) in
example (P Q : Prop) (h : P) : Q := by
  blaster (timeout: 10) (random-seed: 1)
