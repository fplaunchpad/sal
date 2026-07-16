import Sal.ConditionedMRDTs.MRDT_Instances.GSet.GSet
import Sal.ConditionedMRDTs.MRDT_Instances.Counter.Counter
import Sal.ConditionedMRDTs.MRDT_Instances.ORSet.ORSet
import Sal.ConditionedMRDTs.MRDT_Instances.ORSetE.ORSetE
import Sal.ConditionedMRDTs.MRDT_Instances.EWFlag.EWFlag
import Sal.ConditionedMRDTs.MRDT_Instances.GOSet.GOSet
import Sal.ConditionedMRDTs.MRDT_Instances.GOMap.GOMap
import Sal.ConditionedMRDTs.MRDT_Instances.IOC.IOC
import Sal.ConditionedMRDTs.MRDT_Instances.PN.PN
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_WithTombstones.RGA_WithTombstones
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_WithTombstones.Peritext
import Sal.ConditionedMRDTs.MRDT_Instances.MVR.MVR
import Sal.ConditionedMRDTs.MRDT_Instances.AWPQ.AWPQ
import Sal.ConditionedMRDTs.MRDT_Instances.BoundedCounter.BoundedCounter
import Sal.ConditionedMRDTs.MRDT_Instances.ORSetCore.ORSetCore
import Sal.ConditionedMRDTs.MRDT_Instances.BudgetCart.BudgetCart
import Sal.ConditionedMRDTs.MRDT_Instances.FWWRegister.FWWRegister
import Sal.ConditionedMRDTs.MRDT_Instances.LWWRegister.LWWRegister
import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue
import Sal.ConditionedMRDTs.MRDT_Instances.ProductDemo.ProductDemo
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RA_Lin
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_SeqSpec_Refuted
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Composed.Peritext_Composed
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Composed.MarkHonesty
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Composed.MarkIntent
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext.Peritext
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext.Peritext_Read
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_EliasDelta
import Sal.ConditionedMRDTs.MRDT_Instances.SeqSpec_Flat
import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA
-- NOTE: EmbedRGA_ReadEquiv (the compaction theorem) is a standalone build
-- target: it imports the published tombstoned RGA *model*
-- (Sal/MRDTs/RGA_with_tombstones), whose top-level names collide with the
-- rehoming RGA model this umbrella already reaches through RGA/RA_Lin.
-- Build it with `lake build Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_ReadEquiv`.

/-!
# The conditioned MRDT instances — the full catalogue

Every production MRDT, end-to-end through the ONE generic conditioned
framework, up to its observational equivalence `≈`.  Each directory is one
conditioned instance; its presented capstone is the theorem named below
(`IsRALinearizable3Eq` over the `≈`-quotient ternary system).  The eleven
flat datatypes instantiate at the identity (`≈` = `=`,
`Inv = applicable = ⊤`, via `FlatGeneric.flat_ra_linearizable3_eq`); the
**rehoming RGA** (tombstone-free, `RGA_Rehoming/`) is the fully general
instantiation.

**Naming and status (revised 2026-07-16).** `RGA_Rehoming/` formerly held
the plain name `RGA/` and the "canonical" seat.  It is **demoted**: its
convergence capstone `rga_ra_linearizable3_eq` is sound and fully general,
but the design is *sequential-spec-refuted at the `do` level*
(`RGA_Rehoming/RGA_SeqSpec_Refuted.lean`: a single-replica delete reorders
survivors, so the datatype does not implement the naive text buffer).  It
is retained as the framework's generality stress test (the only instance
exercising nontrivial `≈`, `Inv`, `applicable`, and the bespoke honest
chain), as the delete-order countermodel, and — for now — as fused
Peritext's kernel.  The **canonical sequence RDT is the embedded-chain
family** (`EmbedRGA/`, `SidedRGA/`): tombstone-free, seq-spec-sound
(tier 3), delete-order-preserving, read-equal to the published RGA (the
compaction theorem).  `Peritext/` (fused, on the rehoming kernel) inherits
the delete-reorder residual at the render
(`fused_delete_reformats_survivor`); its migration to the embed kernel is
owed (task #85).  The tombstone-carrying and composed variants are
qualified: `RGA_WithTombstones/`, `Peritext_WithTombstones/`, and
`Peritext_Composed/` (the RGA ⊗ marks composition case study).

| instance | conditioned capstone |
|---|---|
| OR-Set | `ORSet_ra_linearizable3_eq` |
| OR-Set-efficient | `ORSetE_ra_linearizable3_eq` |
| Enable-wins flag | `EWFlag_ra_linearizable3_eq` |
| Grow-Only Set | `GOSet_ra_linearizable3_eq` |
| Grow-Only Map | `GOMap_ra_linearizable3_eq` |
| Increment-Only Counter | `IOC_ra_linearizable3_eq` |
| PN-Counter | `PN_ra_linearizable3_eq` |
| RGA (with tombstones) | `rgaWithTombstones_ra_linearizable3_eq` |
| Peritext (with tombstones) | `peritextWithTombstones_ra_linearizable3_eq` |
| Multi-Valued Register | `MVR_ra_linearizable3_eq` |
| Add-Wins Priority Queue | `AWPQ_ra_linearizable3_eq` |
| **Bounded counter** (escrow) | `BC_ra_linearizable3_eq`; safety: `bc_version_inv` |
| **BudgetCart** (per-replica budgets) | `BCart_ra_linearizable3_eq`; safety: `bcart_version_inv_gated` (gated on `CausalCanonical` — OQ8) |
| **FWW reservation register** | `FWW_ra_linearizable3_eq`; characterization: `fww_version_min` |
| **LWW register** | `LWW_ra_linearizable3_eq`; characterization: `lww_version_max` |
| **Mergeable queue** (Peepul, PLDI'22) | `queue_ra_linearizable3` (under honest reachability) |
| **RGA (rehoming)** (tombstone-free; DEMOTED — convergence sound, seq-spec-refuted) | `rga_ra_linearizable3_eq` — the fully general instantiation; negative row: `rehoming_seq_refuted` (`RGA_Rehoming/RGA_SeqSpec_Refuted.lean`) |
| **Peritext** (fused, tombstone-free) | `peritext_ra_linearizable_up_to_eq` — **single-datatype**: the rehoming RGA at `α := char ⊕ boundary`, a *pure instantiation* of `rga_ra_linearizable3_eq` (convergence inherited, ONE honesty contract). Read + genuine positional intent (`render_id_active_iff_between`, `render_span_before` = no backward leak) in `Peritext_Read`; the live-corner contrast to the frozen-path product below. **Inherits the rehoming delete-reorder residual at the render** (`fused_delete_reformats_survivor`, machine-checked); embed-kernel migration owed (#85) |
| Peritext (composed) — RGA ⊗ marks case study | `peritextComposed_ra_linearizable_up_to_eq` — **composed**: RGA_TF ⊗ ORSetCore marks, the composition payoff (`prod_ra_linearizable_up_to_eq_H` at the product parameters; render layer `peritextRender` + `peritextRender_congr`) |
| **Embedded-chain RGA** (tombstone-free, entropy-coded birth chains) | `embed_ra_linearizable3` (under honest reachability, via the queue route's Join) — **parametric in the coordinate code**: `unaryCode`, `binaryCode`, and `eliasDeltaCode` (`embed_ra_linearizable3_eliasDelta`, `EmbedRGA_EliasDelta.lean`) are three verified encodings on one proof; plus the **compaction theorem** `rga_read_eq_embed_read` (`EmbedRGA_ReadEquiv.lean`): on every honest event set the embed read IS the published tombstoned RGA's read (`visible_lt` order equivalence + visibility + element agreement, proved against `Sal/MRDTs/RGA_with_tombstones`'s own relational read) |
| **Sided embedded-chain RGA** (two-sidedness as a parameter; the one-sided embed is the all-R fragment) | `sided_embed_ra_linearizable3` (`SidedRGA/`, the queue route again) — holds for **every side assignment**: sides are payload to convergence, so side *selection* (always-R = the published RGA order; Fugue's between-rule = non-interleaving, `schain_subtree_convex`) is a generation policy above one verified kernel (`Sal/MRDTs/RGA_Embed/Sided_ChainLex.lean`: sided marker theorem, axiom-free totality, unique decodability, all-R fragment theorem `schainBefore_liftR`) |

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
