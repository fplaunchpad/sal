import Sal.ConditionedMRDTs.MRDT_Instances.GSet.GSet
import Sal.ConditionedMRDTs.MRDT_Instances.Counter.Counter
import Sal.ConditionedMRDTs.MRDT_Instances.ORSet.ORSet
import Sal.ConditionedMRDTs.MRDT_Instances.ORSetE.ORSetE
import Sal.ConditionedMRDTs.MRDT_Instances.EWFlag.EWFlag
import Sal.ConditionedMRDTs.MRDT_Instances.GOSet.GOSet
import Sal.ConditionedMRDTs.MRDT_Instances.GOMap.GOMap
import Sal.ConditionedMRDTs.MRDT_Instances.IOC.IOC
import Sal.ConditionedMRDTs.MRDT_Instances.PN.PN
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Tombstone.RGA_Tombstone
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext.Peritext
import Sal.ConditionedMRDTs.MRDT_Instances.MVR.MVR
import Sal.ConditionedMRDTs.MRDT_Instances.AWPQ.AWPQ
import Sal.ConditionedMRDTs.MRDT_Instances.BoundedCounter.BoundedCounter
import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RA_Lin

/-!
# The conditioned MRDT instances — the full catalogue

Every production MRDT, end-to-end through the ONE generic conditioned
framework, up to its observational equivalence `≈`.  Each directory is one
conditioned instance; its presented capstone is the theorem named below
(`IsRALinearizable3Eq` over the `≈`-quotient ternary system).  The eleven
flat datatypes instantiate at the identity (`≈` = `=`,
`Inv = applicable = ⊤`, via `FlatGeneric.flat_ra_linearizable3_eq`); the
tombstone-free RGA is the fully general instantiation.

| instance | conditioned capstone |
|---|---|
| OR-Set | `ORSet_ra_linearizable3_eq` |
| OR-Set-efficient | `ORSetE_ra_linearizable3_eq` |
| Enable-wins flag | `EWFlag_ra_linearizable3_eq` |
| Grow-Only Set | `GOSet_ra_linearizable3_eq` |
| Grow-Only Map | `GOMap_ra_linearizable3_eq` |
| Increment-Only Counter | `IOC_ra_linearizable3_eq` |
| PN-Counter | `PN_ra_linearizable3_eq` |
| RGA (tombstone) | `RGAM_ra_linearizable3_eq` |
| Peritext | `Peritext_ra_linearizable3_eq` |
| Multi-Valued Register | `MVR_ra_linearizable3_eq` |
| Add-Wins Priority Queue | `AWPQ_ra_linearizable3_eq` |
| **Bounded counter** (escrow) | `BC_ra_linearizable3_eq`; safety: `bc_version_inv` |
| **Mergeable queue** (Peepul, PLDI'22) | `queue_ra_linearizable3` (under honest reachability) |
| **RGA (tombstone-free)** | `rga_tombstone_free_ra_linearizable3_eq` |

`GSet/` and `Counter/` additionally carry the two demo kernels of the flat
route (`gset_ra_linearizable3_cd`, `counter_ra_linearizable3_cd`).

The mergeable queue is the third genuinely conditioned instance and the
first proved by a **direct Join Lemma** (`q_join_at`): concurrent enqueues
form a non-commuting clique, so no `rc` assignment exists and the flat
VC engine is structurally unavailable; instead Peepul's three-way merge is
itself exhibited as the linearization witness at every merge, under the
honest-delivery contract `QHonest` (every dequeue names an observed
enqueue — discharged by the `applicable` head-check,
`qHonest_of_applicable`).

The bounded counter is the second genuinely conditioned instance and the
first with a **safety** capstone: `bc_version_inv` proves the escrow
invariant (hence `bc_value_nonneg`, the bound) at every version of every
reachable configuration whose history satisfies the formal client contract
`BCHonest` — the property its CRDT counterpart
(`Sal/CRDTs/Bounded_Counter`) documents as "enforced operationally by
well-behaved clients" and cannot state.
-/
