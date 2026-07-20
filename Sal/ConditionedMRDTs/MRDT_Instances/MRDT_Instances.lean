import Sal.ConditionedMRDTs.Metatheory.GC_Safety
import Sal.ConditionedMRDTs.Metatheory.GC_BoundedState
import Sal.ConditionedMRDTs.Metatheory.EvidenceDischarge
import Sal.ConditionedMRDTs.Metatheory.VirtualLCA_Spot
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
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Rehoming.Peritext
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Rehoming.Peritext_Read
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_EliasDelta
import Sal.ConditionedMRDTs.MRDT_Instances.SeqSpec_Flat
import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Recoding
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_RunTable
import Sal.ConditionedMRDTs.Metatheory.Stability_VC
import Sal.ConditionedMRDTs.MRDT_Instances.ORSet.ORSet_Stability
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Stability_Bridge
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_AnchorsFactor
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_CompactEliasDelta
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_MultiEpoch
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Fusion
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_MergeCongr
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_CompatChain
import Sal.MRDTs.RGA_Embed.SidedRunTable
import Sal.ConditionedMRDTs.Metatheory.FlatGeneric_Bridge_V
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RA_Lin_V
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_Rehoming.RGA_VirtualLCA_Spot
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Intent
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Fugue
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_FugueMax
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_FugueMax_RA_Lin
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_NonInterleaving
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Backward
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_Fugue_ForwardNI
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_SeqSpec
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
compaction theorem).  The fused Peritext exists twice: `Peritext_Rehoming/`
(on the rehoming kernel; inherits the delete-reorder residual at the render,
`fused_delete_reformats_survivor` — retained as the countermodel) and
**`Peritext_Embed/`, the canonical one** (on the embed kernel; the residual
is FIXED, and provably so: `renderIds_del`, deleting a character never
re-formats another).  The tombstone-carrying and composed variants are
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
| **RGA (rehoming)** (tombstone-free; DEMOTED — convergence sound, seq-spec-refuted) | `rga_ra_linearizable3_eq` — the fully general instantiation; over the widened LTS (criss-cross gate lifted, task #90): `rga_ra_linearizable3_eq_V` (`RGA_Rehoming/RA_Lin_V.lean`, via the H-layer virtual-LCA fold `GoodConfig3H_V.lean`; the flats' analogue is `flat_ra_linearizable3_eq_V`); negative row: `rehoming_seq_refuted` (`RGA_Rehoming/RGA_SeqSpec_Refuted.lean`) |
| Peritext (fused, rehoming kernel — countermodel) | `peritext_ra_linearizable_up_to_eq` (`Peritext_Rehoming/`) — the rehoming RGA at `α := char ⊕ boundary`, a *pure instantiation* of `rga_ra_linearizable3_eq`. Carries the pure render layer + positional intent theorems (`render_id_active_iff_between`, `render_span_before` = no backward leak) that both fused instances share. **Inherits the rehoming delete-reorder residual at the render** (`fused_delete_reformats_survivor`, machine-checked); retained as the countermodel |
| **Peritext (fused, embed kernel — CANONICAL)** | `peritextEmbed_ra_linearizable3` (`Peritext_Embed/`) — `embed_ra_linearizable3` at `α := PeritextElt`, pure instantiation (the embed instance is payload-generic). The state IS the document (read = `map`, no traversal), the shared pure render layer applies verbatim, and the rehoming residual is **fixed with a general theorem**: `renderIds_del` (kernel-clean, {propext, Quot.sound}) — deleting a character leaves every other character's formatting bitwise untouched; SPOT replays the rehoming witness trace clean (PASS+FAIL shaped). **Seq-spec tier 4** (`PeritextEmbed_SeqSpec.lean`): `peritextEmbed_seq_sound`(`_ids`) — the render IS the naive marked-text editor's screen on every sequentially honest history (tier 3's buffer soundness, payload-generic, composed with the shared render fold); FAIL pin: a *boundary* delete refutes the `renderIds_del` equation, so the character hypothesis is necessary |
| Peritext (composed) — RGA ⊗ marks case study | `peritextComposed_ra_linearizable_up_to_eq` — **composed**: RGA_TF ⊗ ORSetCore marks, the composition payoff (`prod_ra_linearizable_up_to_eq_H` at the product parameters; render layer `peritextRender` + `peritextRender_congr`) |
| **Embedded-chain RGA** (tombstone-free, entropy-coded birth chains) | `embed_ra_linearizable3` (under honest reachability, via the queue route's Join) — **parametric in the coordinate code**: `unaryCode`, `binaryCode`, and `eliasDeltaCode` (`embed_ra_linearizable3_eliasDelta`, `EmbedRGA_EliasDelta.lean`) are three verified encodings on one proof; plus the **compaction theorem** `rga_read_eq_embed_read` (`EmbedRGA_ReadEquiv.lean`): on every honest event set the embed read IS the published tombstoned RGA's read (`visible_lt` order equivalence + visibility + element agreement, proved against `Sal/MRDTs/RGA_with_tombstones`'s own relational read); and the **verified GC**: `eRecode_*` (reads-identical re-coding at a stable cut, `EmbedRGA_Recoding.lean`), the `SettledAt` bridge (`EmbedRGA_Stability_Bridge.lean` + `EmbedRGA_AnchorsFactor.lean`: the residue routes through the generation discipline, with a recorded countermodel showing bare honest reachability cannot supply it), and the concrete compaction `compactEliasDelta_settled_reads` (`EmbedRGA_CompactEliasDelta.lean`): drop dead ranges + rank-renumber under the Elias-δ code preserves every read of every beyond-cut continuation, the in-flight wrinkle pinned both ways in the SPOTs |
| **Sided embedded-chain RGA** (two-sidedness as a parameter; the one-sided embed is the all-R fragment) | `sided_embed_ra_linearizable3` (`SidedRGA/`, the queue route again) — holds for **every side assignment**: sides are payload to convergence, so side *selection* (always-R = the published RGA order; Fugue's between-rule = non-interleaving, `schain_subtree_convex`) is a generation policy above one verified kernel (`Sal/MRDTs/RGA_Embed/Sided_ChainLex.lean`: sided marker theorem, axiom-free totality, unique decodability, all-R fragment theorem `schainBefore_liftR`). **Per-policy intent** (`SidedRGA_Intent.lean`): `sFold_liftOp` — under always-R the sided instance IS the one-sided instance, fold for fold, unconditionally (a pure simulation; through it tier 3 and the compaction theorem transport); `sided_fold_subtree_convex` — subtrees display as contiguous blocks in any chain-generated fold, so a run that chains (Fugue's shape, forward and backward) is never interleaved; L19 replayed contiguous in the SPOT. Residue: the Fugue rule as a formal generation policy (needs an intent-op layer) |

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
