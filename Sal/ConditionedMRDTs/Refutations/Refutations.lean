import Sal.ConditionedMRDTs.Refutations.CD_Not_Derivable_Ternary
import Sal.ConditionedMRDTs.Refutations.FeasibleInit_Not_Derivable_At_Empty
import Sal.ConditionedMRDTs.Refutations.LocalRedistribute_Not_Derivable
import Sal.ConditionedMRDTs.Refutations.G2_Transport_Probe
import Sal.ConditionedMRDTs.Refutations.G2_Applicability_Aware
import Sal.ConditionedMRDTs.Refutations.Impossibility
import Sal.ConditionedMRDTs.Refutations.InterLca2op_Defeater_Arbiter
import Sal.ConditionedMRDTs.Refutations.JoinLemma3F_Of_AlmostClosed
import Sal.ConditionedMRDTs.Refutations.LWW_Merge_Needs_Timestamps
import Sal.ConditionedMRDTs.Refutations.Reunification_Peel_Obstruction
import Sal.ConditionedMRDTs.Refutations.RGA_Rehoming_Gate
import Sal.ConditionedMRDTs.Refutations.SiblingSplice_Fooling
import Sal.ConditionedMRDTs.Refutations.UpdateFeasibility_Gate

/-!
# Refutations — umbrella

One import per refutation module, so `lake build
Sal.ConditionedMRDTs.Refutations.Refutations` compiles the whole
directory. Several of these files are cited by `sal-mrdts.pdf` but are
leaves by design (nothing in Framework/Metatheory/MRDT_Instances may
import a refutation except where a counterexample is consumed as a
gate); without this umbrella the leaf modules are outside every build
target and can rot silently. Build this target alongside
`MRDT_Instances.MRDT_Instances` when verifying the tree.

The catalogue:

- `CD_Not_Derivable_Ternary` — the causal-delta bound is not derivable
  from the ternary laws (the CD ladder negative).
- `FeasibleInit_Not_Derivable_At_Empty` — VC5° (the nullary unit) is
  independent: the poisoned-empty G-set (#114 phase 2, T2).
- `LocalRedistribute_Not_Derivable` — VC6 (feasible local-redistribute)
  is independent: the change-wins flag (#114 phase 2, T1).
- `G2_Transport_Probe`, `G2_Applicability_Aware` — the G2 gate probes
  (also imported by Development and the gate files).
- `Impossibility` — the flat impossibility theorem.
- `InterLca2op_Defeater_Arbiter` — the fully LCA-legal execution that
  defeats the published bottom-up soundness induction
  (`awset_rem_output_empty`, `no_inter_lca_2op_rem_peel_of_defeater`,
  `crack1_witness`).
- `JoinLemma3F_Of_AlmostClosed` — the almost-closed route refutation.
- `LWW_Merge_Needs_Timestamps` — LWW arbitration cannot be recovered
  from the order-free state.
- `Reunification_Peel_Obstruction` — the peel obstruction consumed by
  `JoinLemma3C`.
- `RGA_Rehoming_Gate` — the rehoming RGA's gate refutation.
- `SiblingSplice_Fooling` — the sibling-splice fooling pair (the
  retention lower bound: `sibling_splice_no_merge_function`).
- `UpdateFeasibility_Gate` — the feasibility gate (also imported by
  Development and the NF files).
-/
