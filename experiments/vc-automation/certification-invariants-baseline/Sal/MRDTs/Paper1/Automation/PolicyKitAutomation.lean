import Sal.MRDTs.Paper1.Automation.PolicyExpansionAutomation
import Sal.MRDTs.Paper1.Automation.GenericPolicyExpansion

/-! Type-directed construction of finite policy certificates. -/
macro "derive_policy_kit" : tactic => `(tactic| (
  constructor
  case localKernels => constructor <;> policy_auto
  case causalKernels => constructor <;> policy_auto
  case eventCertificate => constructor <;> policy_auto
  all_goals policy_auto))
