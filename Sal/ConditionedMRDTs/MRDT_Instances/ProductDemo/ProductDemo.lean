import Sal.ConditionedMRDTs.Metatheory.Product
import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue
import Sal.ConditionedMRDTs.MRDT_Instances.Counter.Counter

/-!
# ProductDemo: `Q ⊗ Counter`, the composition kit's acceptance test

An acceptance test for the composition kit, as a real capstone: the
**mergeable queue** (a genuinely conditioned instance: direct join under the
honest-history contract `QHonestCore`; no `rc` assignment exists for its
enqueue clique) composed with the **counter** (`mergeL l a b = a + b − l`,
unconditional CD-route join), through `prodSig`.

The point of this file is what is *absent*: no new VCs, no witness
manipulation, no re-proof of either component. The capstone is the kit's
composite metatheorem fed the two component joins verbatim:

* the queue supplies `q_join_at : QHonestCore C → JoinLemma3At Q C`, a
  configuration-level certificate, consumed at the **projection** of each
  product-reachable core (which is generally *unreachable* for the queue's
  own LTS: this is why the certificate must be configuration-level, and why
  `queue_ra_linearizable3` itself could never be consumed here);
* the counter supplies `Counter_joinLemma3_cd : JoinLemma3 Counter`, a
  `∀`-configuration certificate, instantiated at the projection for free.

The contract `QCHonest` is `H⊗`: queue honesty read through the first core
projection ("every `inl`-dequeue names a `vis`-prior `inl`-enqueue"), counter
side trivial. The product does not manufacture honesty: `H⊗` is load-bearing
exactly where `QHonestCore` was.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- The composite contract `H⊗`: the queue's honest-history contract
precomposed with the first core projection; the counter is unconditional. -/
def QCHonest : Configuration (prodSig Q Counter) → Prop :=
  prodContract QHonestCore fun _ => True

/-- **The demo capstone**: per-version RA-linearizability of `Q ⊗ Counter` at
every `H⊗`-honestly reachable configuration, an instantiation of the kit's
composite metatheorem, with zero bespoke proof: the queue's join under its
contract and the counter's unconditional join are consumed as-is. -/
theorem qc_ra_linearizable3 {C : Configuration (prodSig Q Counter)}
    (hReach : HonestReach (prodSig Q Counter) QCHonest
      (prodSig_inv_init trivial trivial) C) :
    IsRALinearizable3 C :=
  prod_ra_linearizable3_of_honest_reach
    (fun _Cb hHon => q_join_at hHon)
    (fun Cb _ => Counter_joinLemma3_cd.at Cb)
    hReach

#print axioms qc_ra_linearizable3

end Sal.ConditionedMRDTs
