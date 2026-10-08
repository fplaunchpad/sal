import Smt

namespace VCAutomation.SmtControls
theorem positive (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
#print axioms positive
end VCAutomation.SmtControls
