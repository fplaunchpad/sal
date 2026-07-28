import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA
import Sal.MRDTs.RGA_Embed.Embed_Code_EliasDelta

/-!
# The capstone at the flipped Elias-δ code

Because `embed_ra_linearizable3` is parametric in the code `Γ`, upgrading
the per-level coordinate cost from `2 log₂ δ + 1` to `log₂ δ + O(log log δ)`
is pure plug-in — this file's theorem has zero new proof content. Together
with `unaryCode` and `binaryCode`, this gives the datatype three verified
encodings on one proof.
-/

namespace Sal.ConditionedMRDTs

open Sal.EmbedRGA

/-- RA-linearizability per version at every honestly reachable
configuration of the embedded-chain RGA carried by the flipped Elias-δ
code. Inherited, not re-proved. -/
theorem embed_ra_linearizable3_eliasDelta
    {C : Configuration (E eliasDeltaCode)}
    (hReach : EReach eliasDeltaCode C) :
    IsRALinearizable3 C :=
  embed_ra_linearizable3 hReach

#print axioms embed_ra_linearizable3_eliasDelta

end Sal.ConditionedMRDTs
