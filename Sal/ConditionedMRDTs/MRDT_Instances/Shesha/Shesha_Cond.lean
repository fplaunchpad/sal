import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Presplice_Refuted
import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Rows_Refuted

/-!
# Shesha conditioned-convergence route: retired

The former contents of this module claimed `shesha_join_at_effC` and
`shesha_ra_linearizable3` through `shesha_rows_residue`.  The residue is false,
and the resulting positive capstone is contradicted by a reachable merge.  The
unsound declarations have therefore been retired rather than retained behind a
`sorry` or an axiom.

The executable datatype, sequential theorems, merge combinator facts, witness
machinery, and the proved row-to-forest reduction remain available in the
underlying Shesha modules.  The authoritative conditioned results are the
checked negative theorems imported here:

* `SheshaJoinCX.shesha_join_at_refuted`;
* `SheshaPrespliceCX.shesha_join_at_eff_refuted` and
  `SheshaPrespliceCX.shesha_presplice_refuted`;
* `SheshaRowsCX.shesha_rows_residue_refuted`.

A future positive capstone must use a weaker licensed-divergence specification
or a different immutable-position representation; it must not reinstate the
refuted row-store premise.
-/

#check Sal.ConditionedMRDTs.SheshaJoinCX.shesha_join_at_refuted
#check Sal.ConditionedMRDTs.SheshaPrespliceCX.shesha_join_at_eff_refuted
#check Sal.ConditionedMRDTs.SheshaPrespliceCX.shesha_presplice_refuted
#check Sal.ConditionedMRDTs.SheshaRowsCX.shesha_rows_residue_refuted
