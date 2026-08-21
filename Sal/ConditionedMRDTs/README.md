# Sal/ConditionedMRDTs: RA-linearizability for MRDTs (ternary merge)

A mechanized soundness metatheory for MRDTs (three-way `merge lca a b` over a
version DAG, the setting of the Neem paper's Theorem 2, arXiv:2502.19967 /
OOPSLA 2025), built on the corrected binary theory of
[`Sal/CRDTs/Metatheory/`](../CRDTs/Metatheory/). Everything below is
0-sorry and kernel-checked (axioms: `propext`, `Classical.choice`,
`Quot.sound`). The paper-style companion note
([`sal-mrdts.pdf`](sal-mrdts.pdf)) is the consolidated account (its
Part I is the metatheory of this directory, from the definition of an
MRDT through the eight VCs to the conditioned metatheorem and the
factored discharge route; Part II is the embedded-chain RGA design
note; Part III is the sequential-specification campaign).

**The tree tells the story:**

| directory | contents |
|---|---|
| [`Framework/`](Framework/) | the definitions instances build against: the base LTS (`Base/`), the signature ladder up to `ConditionedMRDTSig`, the execution model, the σ/`loOn` layer, the VC statements, the orders (`loOnC`, `loOnA`) and the feasibility predicate (`noopFeasible`) |
| [`Metatheory/`](Metatheory/) | the metatheorems: the LCA lemma, flat adequacy, the closure-indexed Join Lemma, the `≈`-quotient functor and the conditioned metatheorem, the flat collapse |
| [`Refutations/`](Refutations/) | the machine-checked negative results that justify the framework's shape: the G2 applicability-transport refutation, the feasibility-gate verdict, the peel obstruction, the kill-tests, the defeater |
| [`MRDT_Instances/`](MRDT_Instances/) | the conditioned instances, one directory per RDT, twelve production capstones through the ONE generic theorem |
| [`Development/`](Development/) | the research record: findings journals, abandoned proof routes, investigation probes. Nothing imports it. |

Commit GC now has two additional checked layers in `Metatheory`.
[`GC_CompressedDAG.lean`](Metatheory/GC_CompressedDAG.lean) specifies a
root-free retained graph and proves exact retained reachability and LCA
preservation, packaged with the existing trace/read theorem by
`gc_safety_compressed`. [`Distributed_GC.lean`](Metatheory/Distributed_GC.lean)
models separate local stores, asynchronous fetch/ingest by union, closed rosters, and
frontier evidence derived from received authored ancestry rather than trusted
as a wire assertion. It separates head synchronization from fetch and proves
finite distributed executions refine a no-GC world while local collection
stutters. Exact projection to one shared global store holds only at a
coordinated cut where every local certificate chooses the same keep set;
`coordinated_collect_projects_global` proves that boundary, and a checked
counterexample refutes exact projection after only one replica collects.
[`Distributed_GC_Refinement.lean`](Metatheory/Distributed_GC_Refinement.lean)
connects that storage protocol to the full datatype-rich `Configuration`:
physical availability gates actual `Step3` apply/merge/query transitions, and
`distributedConfig_refines_Step3` erases silent fetch/GC steps to a genuine
conditioned execution.
The mint-certified layer reuses `GenerationContract` and
`MintCertifiedReach3`; `UnifiedVerifiedMRDT.distributed` exports generic
RA-linearizability, safety, and observable guarantees. Production
instantiations live in
[`DistributedUnifiedCertificates.lean`](MRDT_Instances/DistributedUnifiedCertificates.lean).

Layering: `Framework` imports nothing above it; `Metatheory` builds on
`Framework` (plus one leaf refutation it reuses machinery from);
`MRDT_Instances` builds on both; `Refutations` may reference instance
signatures (counterexamples need concrete witnesses); nothing imports
`Development`.

**The signature: one framework.** An MRDT presents the *conditioned*
signature (`ConditionedMRDTSig`, [`Framework/MRDTSig.lean`](Framework/MRDTSig.lean))

    ⟨ Σ, σ₀, do, mergeL, rc, Inv, applicable ⟩

together with an observational equivalence `≈` on states (`EqEquiv`,
[`Metatheory/GenericEqQuotient.lean`](Metatheory/GenericEqQuotient.lean)):
a state space with initial state, the update `do`, the three-way merge
`mergeL l a b` (LCA first), the conflict-resolution policy `rc` for
concurrent non-commuting pairs, a state invariant `Inv` (a shape
over-approximation of reachability), an applicability predicate
`applicable` (when an op is sensible at a state, it may read the op's
timestamp), and `≈` (what clients can distinguish). Commutation is
**conditioned** (`commutesOn`): two ops must commute only at `Inv`-states
where both are applicable. **Flat datatypes** (counters, sets, registers,
everything whose ops make sense on every state) take
`Inv = applicable = ⊤` and `≈` := `=`; that specialization collapses to the
unconditioned theory, and §§1–3 below are exactly it. §4 is the framework
at full generality, exercised by the one production datatype that needs it.

**The setting.** Replicas fork, apply operations locally, and merge,
git-style. The LTS (`Step3`,
[`Framework/ExecutionModel.lean`](Framework/ExecutionModel.lean),
[`Metatheory/LCA_Lemma.lean`](Metatheory/LCA_Lemma.lean)) keeps a ranked
**version store**: every apply and merge allocates a fresh version carrying
its `(state, event set)` pair, and merge takes the two head states *plus
the state at their lowest common ancestor* (LCA) in the version DAG.
Events are timestamped ops `(t, r, o)`; visibility `vis` is the causal
order delivery induces (Lamport-monotone timestamps and causally-closed
logs are structural fields of `Configuration`: executions violating them
are unrepresentable).

**The property: one definition.** The **linearization order** `lo` on an
event set `E` orders exactly the pairs a correct sequential replay must not
invert: a `vis`-related non-`commutesOn` pair in `vis` order, and a
concurrent non-`commutesOn` pair by `rc` (unless a still-later
non-commuting event already overrides the later one). `lo` is partial and
not transitive, so "π respects `lo`" is the pairwise no-inversion
condition, not sortedness. **RA-linearizability, per version, up to `≈`**:
in every reachable configuration, *every* stored version `(s, E)` (LCAs
included, not just replica heads) satisfies

    ∃ π, π a lo-respecting permutation of E  ∧  fold do σ₀ π ≈ s .

This single definition has two mechanized renderings: at the flat
specialization `≈` is `=` and it is `IsRALinearizable3`
([`Metatheory/Adequacy.lean`](Metatheory/Adequacy.lean)); in general the
store holds `≈`-classes and it is `IsRALinearizable3Eq`
([`Metatheory/GoodConfig3H.lean`](Metatheory/GoodConfig3H.lean)), with
the *raw* `do`-fold as witness. The **canonical state** `σ(E)` is that
fold, well-defined (up to `≈`) because the theory forces all such folds of
`E` to agree.

## 1. The VC set (the flat discharge engine): [`Framework/VC_Set.lean`](Framework/VC_Set.lean)

**Eight verification conditions** discharge a flat datatype
(`Inv = applicable = ⊤`, `≈` = `=`, signature reduced to
`⟨Σ, σ₀, do, mergeL, rc⟩`); what they buy (the closure-indexed Join
Lemma) is exactly what the generic theorem of §4 consumes at the identity
instantiation:

Update layer (`UpdateVCs`, defined in
[`Framework/Sigma_LoOn3.lean`](Framework/Sigma_LoOn3.lean)):
1. `rc_non_comm_directional`: for *different-replica* events with distinct
   timestamps, non-commutativity ⟺ `rc`-ordered in some direction (the
   `differentReplicas` guard is the paper's own F* interface form;
   same-replica pairs are ordered by `vis`-totality instead);
2. `no_rc_chain`: no two consecutive `rc` edges;
3. `cond_comm_lift`: the conditional-commutativity swap survives any
   intervening suffix ending in a non-commuting event.

Merge layer:
4. `mergeL_comm`: `mergeL l a b = mergeL l b a` (`CoreVCs3CD`);
5. `feasible_init`: `mergeL σ₀ σ₀ σ(E) = σ(E)` on canonical states;
6. `feasible_local_redistribute`: a downset-delta application commutes past
   an enclosing merge, on canonical tuples at honest LCAs;
7. `feasible_redistribute`: a delta applied to all three components
   extracts once (the LCA slot cancels the duplicate: this is what
   idempotence did in the binary theory, done by LCA arithmetic);
8. `CDVC3`: the causal-delta equation: for a `loOn(U)`-maximal event `e`,
   `mergeL σ(↓e∖e) σ(U∖e) (do σ(↓e∖e) e) = do σ(U∖e) e`.

On-ramps and variants: `DeltaVCs3` (laws 6–7 unconditional, exactly the
group ⊕ lattice classes: Counter, G-Set, every LCA-blind CRDT);
`JoinLemma3F` (the **full-causal-closure** join notion: counter-comparison
merges like the Enable-wins flag provably need full closure, not just
commutation closure; reunifying this with the feasible route is open).

## 2. Adequacy (the flat engine's internal form): [`Metatheory/Adequacy.lean`](Metatheory/Adequacy.lean)

    ra_linearizable_of_core_feasible_cd3 :
      CoreVCs3CD D → FeasibleDeltaVCs3 D → CDVC3 D →
      ∀ C reachable from initConfig in the ternary system Step3,
        IsRALinearizable3 C

This is the definition above at `≈` := `=`, in direct form (the
headline per-instance results are the §3 theorems through the generic
framework; this chain is the engine that validates the VC set and
supplies each instance's Join Lemma). The proof carries `GoodConfig3`
(every version canonical + store closure facts) through the LTS of
[`Metatheory/LCA_Lemma.lean`](Metatheory/LCA_Lemma.lean); the merge case is
the Join Lemma obtained by `join_lemma3_of_cd_feasible`.
Also here: the unconditional-route bridge (`ra_linearizable_of_core_delta_cd3`),
the commuting-class discharge of CD (`cdVC3_of_all_comm`), and the
full-closure bridge (`ra_linearizable3_of_joinF`) used by the Enable-wins
route.
[`Metatheory/HonestReach.lean`](Metatheory/HonestReach.lean) hosts the
**honest-reachability metatheorem** (`HonestReach`,
`ra_linearizable3_of_honest_reach`): RA-linearizability at every
configuration reachable under a per-configuration honesty contract `H`,
given that `H`-configurations admit the Join (`JoinLemma3At`). This is the
factored form of the conditioned route: the generic induction extracted
once, with the per-datatype join discharge as the residue (three species:
conditioned commutation / flat / direct witness); the queue's and the
bounded counter's inductions are one-line corollaries.
[`Metatheory/GenHonest.lean`](Metatheory/GenHonest.lean) extracts the
**generic honesty shape** (`GenHonest D P`: `P` holds of every event at the
fold of its causal past, the client-checkable form; `AppHonest` is its
`applicable` instance), with the counter's and the queue's contracts
re-derived as instantiations (`BCHonest_iff_genHonest`,
`qHonest_of_genHonest`).
[`Metatheory/GenerationContract.lean`](Metatheory/GenerationContract.lean)
exposes the issuer policy as a public contract and keeps raw `Step3` as the
untrusted environment semantics. `GuardedStep3` checks only applies, at the
issuing head; `MintCertifiedReach3` carries the existential mint-time causal
fold that later configurations do not retain. This existential form is needed
by order-sensitive guards such as the queue head check. The bounded counter
alone lifts it to the older all-enumerations form by a checked permutation-
invariance proof over its count measures.
[`Metatheory/UnifiedVerifiedMRDT.lean`](Metatheory/UnifiedVerifiedMRDT.lean)
packages the established Join/sequential certificate with that generation
contract and a history/global client-safety certificate separate from
structural configuration well-formedness. Optional `LocalSafetyLaws` give a
stronger constructor when raw update/merge induction is sound; the bounded
counter instead uses `bc_version_inv`. Concrete guards for the bounded counter,
queue, EmbedRGA, SidedRGA, and canonical Embed Peritext are catalogued in
[`MRDT_Instances/ProductionGenerationContracts.lean`](MRDT_Instances/ProductionGenerationContracts.lean).
The stable one-sided `PeritextEmbedRGA` endpoint is
[`MRDT_Instances/Peritext_Embed/PeritextFlagship.lean`](MRDT_Instances/Peritext_Embed/PeritextFlagship.lean):
`peritextFlagship` packages distributed correctness, clocked local intent,
compressed and distributed commit-history GC, and state-GC render preservation
without merging their assumptions.
The shipped JavaScript default is `PeritextSidedEmbedRGA`. Its public Lean
endpoint is `PeritextSided.productionCertificate`; the interaction fields
expose finite-trace erasure for interleaved fetch, commit GC, local state GC,
and visible operations, plus query equivalence for every retained physical
version under ordinary unique-LCA `Step3`. The widened `CombinedStepV` layer
also proves finite-trace erasure and query safety for admitted `Step3V` traces;
constructing the virtual merge's physical materialization delta from retained
MCAs remains open. `PeritextSided_Interaction.lean` derives abstract merge coverage from
physical record/delete/endpoint evidence. The JavaScript remains handwritten
and is checked by executable merge audits and differential tests, not extraction.
The exact proved/open matrix is `GC_COVERAGE_AUDIT.md`.
[`Metatheory/GenericSafety.lean`](Metatheory/GenericSafety.lean) and
[`Metatheory/EscrowSafety.lean`](Metatheory/EscrowSafety.lean) carry the
**generic safety metatheorems**: `version_inv_of_causal_canonical` (`Inv` at
every version, by induction along *causal* canonical witnesses
(`CausalCanonical`) parametric in the per-datatype `SafetyStep` obligation;
the naive all-canonical-witness route is refuted by the bounded counter
itself) and `escrow_version_inv` (the measured/affine route, no causal
witness needed). `bc_version_inv` is re-derived through **both**, retiring
the counter's bespoke counting apparatus; the analysis is the pen-and-paper
memo `Development/GENERIC_SAFETY_PENPAPER.md`.
[`Metatheory/Product.lean`](Metatheory/Product.lean) carries the
**composition theorem** (raw kit): the binary heterogeneous product
`D₁ ⊗ D₂` composes at the `JoinLemma3At` boundary (no cross-component
`loOn` edges, concatenation witness) with `joinLemma3At_prod` and the
composite `prod_ra_linearizable3_of_honest_reach`; consumability demo
`MRDT_Instances/ProductDemo/` (queue ⊗ counter, zero bespoke proof).
Analysis: `Development/COMPOSITION_PENPAPER.md`.
[`Metatheory/Product_Safety.lean`](Metatheory/Product_Safety.lean) is the
**safety kit**: pinned-extension, `honestAppOn_prod`, `safetyStepOn_prod`,
the one-sided `causalCanonical_prod_of_one_sided` (the two-sided form is
refuted), and the composite
`prod_version_inv_on_of_one_sided`. [`Metatheory/ProductEq.lean`](Metatheory/ProductEq.lean) is the
**≈-lift kit** (pragmatic cut `≈₂ = Eq`): every eq-quotient obligation
componentwise, `eqJoinLemma3C_H_prod`, and the product ≈-capstone
`prod_ra_linearizable_up_to_eq_H`: one quotiented component, one flat,
exactly the Peritext = RGA ⊗ marks shape. The composition kit is complete.
The LCA lemma `L(v_⊤) = L(v₁) ∩ L(v₂)` and its maintainability are
proved in [`Metatheory/LCA_Lemma.lean`](Metatheory/LCA_Lemma.lean).

## 3. The discharged MRDTs: [`MRDT_Instances/`](MRDT_Instances/)

One directory per RDT; each directory's presented capstone concludes
`IsRALinearizable3Eq` **through the one generic theorem** (§4), and the
same directory carries the flat VC discharge that feeds it. The umbrella
[`MRDT_Instances/MRDT_Instances.lean`](MRDT_Instances/MRDT_Instances.lean)
imports all nineteen capstones:

| MRDT | End-to-end theorem | Instantiation / discharge |
|---|---|---|
| **OR-Set** (production mirror) | `ORSet_ra_linearizable3_eq` | identity (`≈`=`=`); feasible + CD |
| **OR-Set-efficient** (production mirror) | `ORSetE_ra_linearizable3_eq` | identity; feasible + CD |
| **Enable-wins flag** (production mirror) | `EWFlag_ra_linearizable3_eq` | identity; direct full-closure join |
| **Grow-Only Set** (production mirror) | `GOSet_ra_linearizable3_eq` | identity; unconditional delta |
| **Grow-Only Map** (production mirror) | `GOMap_ra_linearizable3_eq` | identity; unconditional delta |
| **Increment-Only Counter** (production mirror) | `IOC_ra_linearizable3_eq` | identity; unconditional delta |
| **PN-Counter** (production mirror) | `PN_ra_linearizable3_eq` | identity; unconditional delta |
| **RGA, with tombstones** (production mirror) | `rgaWithTombstones_ra_linearizable3_eq` | identity; unconditional delta |
| **Peritext, with tombstones** (production mirror) | `peritextWithTombstones_ra_linearizable3_eq` | identity; unconditional delta |
| **Multi-Valued Register** (production mirror) | `MVR_ra_linearizable3_eq` | identity; feasible (all-comm, `B = init`) |
| **Add-Wins Priority Queue** (production mirror) | `AWPQ_ra_linearizable3_eq` | identity; feasible (OR-Set pattern on A) |
| **Bounded counter** (escrow; mirror of `Sal/CRDTs/Bounded_Counter`) | `BC_ra_linearizable3_eq`; **safety**: `bc_version_inv`, `bc_value_nonneg` | identity for convergence; the conditioned contract (`BCInv`/`bcApplicable`/`BCHonest`) delivers the bound as a reachability theorem |
| **FWW reservation register** | `FWW_ra_linearizable3_eq`; **characterization**: `fww_version_min` (the min-ts claim wins, at every version) | payload arbitration (min-semilattice), the positive complement to `LWW_Merge_Needs_Timestamps`; the claim-when-unset discipline is deliberately consumed by no theorem (unstable under concurrent honest extension) |
| **LWW register** | `LWW_ra_linearizable3_eq`; **characterization**: `lww_version_max` (the max-ts write wins, at every version) | payload arbitration (max-semilattice), the `last`-writer twin of FWW; **unconditional** (`applicable = ⊤`, writes always overwrite). Genuinely end-to-end mechanized: unlike the flat CRDT LWW (whose VCs→RA-lin bridge in `Sal/CRDTs/Metatheory/Merge_Linearization.lean` still carries `sorry`s), this rides the framework's kernel-clean bridge. |
| **BudgetCart** | `BCart_ra_linearizable3_eq`; safety **gated**: `bcart_version_inv_gated` | or-set `rc` (add-wins) + derived per-replica spend; ungated `SafetyStepOn` is FALSE (vis-only causal folds are enumeration-dependent under concurrent add/rem), the OQ8 forcer. Convergence is an **instantiation** of the payload-parametric [`ORSetCore/`](MRDT_Instances/ORSetCore/) library (composition level L0): `BudgetCart := OSCore (item × price) fst …` (no bespoke discharge) |
| **Mergeable queue** (Peepul, PLDI'22) | `queue_ra_linearizable3` under honest reachability; `qHonest_of_applicable` | **direct Join Lemma** (`q_join_at`): Peepul's merge is the linearization witness; no `rc` exists (enqueue clique) |
| **RGA** (canonical, tombstone-free) | `rga_ra_linearizable3_eq` | full generality (§4) |
| **Peritext** (canonical, fused, tombstone-free) | `peritext_ra_linearizable_up_to_eq`; intent: `render_id_active_iff_between` + `render_span_before` | **fused, the paper-faithful design**: one RGA at `α := char ⊕ boundary` (marks are id-paired boundary nodes), convergence a one-line instantiation of the RGACore capstone (773 lines total vs the composed design's ~1,500). Delivers the genuine positional intent the composed design retracts: a char is formatted iff it lies between the mark's boundaries in reading order (fold-activation ⟺ structural decomposition, non-circular), and backward leak is forbidden by construction. Residual: interior-deletion reading-order re-sort (`del_can_reorder_survivors`), a bounded change, not a leak: the atomicity horn of the trilemma. |
| **Peritext, composed** (RGA ⊗ marks case study) | `peritextComposed_ra_linearizable_up_to_eq`; read layer: `peritextRender_congr` (well-definedness only) | **composed**: RGA_TF ⊗ ORSetCore marks through the product kit, 1,064 lines total, supply rerun 790, MarkStore 81; ungated (the RGA's own honest-delivery premise through proj₁). **Caveat**: convergence/safety are complete, but mark *positioning* is not paper-faithful: the frozen recorded paths climb tree ancestry, so deleting a mark's anchor leaks formatting backward (`MarkIntent.lean` states the honest containment bound, not a no-leak guarantee; OQ `oq:linspec`). |

**The production catalogue is complete: every MRDT shipped in Sal carries a
kernel-checked end-to-end theorem through the one framework.** The bounded
counter adds the first **safety** capstone: conditioning is used not to
rescue convergence (its ops commute flatly) but to prove the invariant its
name promises: `value ≥ 0` at every reachable version, from a
client-checkable applicability contract. The mergeable queue is the
first instance whose Join Lemma is proved **directly** rather than through
the flat VC engine: concurrent enqueues are a non-commuting clique, so no
`rc` assignment can satisfy `rc_non_comm_directional` + `no_rc_chain`, and
the witness enumeration at every merge is Peepul's merge itself
(LCA-survivors ++ branch-one delta ++ branch-two delta), available under the
honest-delivery contract `QHonest`, which the dequeue `applicable`
head-check discharges (`qHonest_of_applicable`). The
flat corollaries (`*_ra_linearizable3` over the raw system, plus
the `GSet/` and `Counter/` specimens) live in the same per-RDT files as
internal steps of the engine.

The production mirrors are faithful to `Sal/MRDTs/{OR_Set,
OR_Set_Efficient, Enable_Wins_Flag}` (documented deviations only). The
Enable-wins discharge certifies the production per-replica `merge_flag` on
exactly the corner (`inter_right_1op`) where its known-broken
global-counter sibling fails.

## 4. THE framework: [`MRDT_Instances/RGA_Rehoming/RA_Lin.lean`](MRDT_Instances/RGA_Rehoming/RA_Lin.lean)

The soundness theorem is generic, stated over *any* `ConditionedMRDTSig`
with an `EqEquiv`, on the same `Step3` LTS: the **`≈`-quotient functor**
`D ↦ D≈` builds the datatype whose states are `≈`-classes of `Inv`-states,
with update, merge and `applicable` descending by congruence
([`Metatheory/GenericEqQuotient.lean`](Metatheory/GenericEqQuotient.lean));
on top, a **witness-disciplined reachability layer** carries, per version,
an enumeration witness for the general definition above, maintained at
applies and joined at merges (`RA_linearizable_up_to_eq_H`,
[`Metatheory/GoodConfig3H.lean`](Metatheory/GoodConfig3H.lean)). The
datatype's obligations, replacing the eight flat VCs: `≈` is an equivalence
(`EqEquiv`), `Inv` is preserved on wellformed ops (`InvPres`),
update/merge/query are `≈`-congruent on `Inv` (`CongVC`, `InvInvVC`), and
the merge is, up to `≈`, the fold of a `lo`-respecting enumeration of the
joined events (the `≈`-Join, `EqJoinLemma3C_H`). Instantiated flat
(`Inv = applicable = ⊤`, `≈` = `=`) these collapse into the ordinary Join
Lemma of §2, mechanized as
[`Metatheory/FlatGeneric_Bridge.lean`](Metatheory/FlatGeneric_Bridge.lean),
which is how the eleven flat instances of §3 ride the same theorem.

**The exercising instance: the tombstone-free RGA**
([`../MRDTs/RGA_Tombstone_Free/`](../MRDTs/RGA_Tombstone_Free)) is a
replicated list whose deletes *physically remove* nodes, no tombstone set;
every op carries its target's recorded ancestor path, and merge re-anchors
each surviving node by climbing that path to the nearest survivor. Here
`Inv` is the forest well-formedness (with id-monotone anchors),
`applicable` is **accurate** (the recorded path is the target's true live
ancestor chain) **∧ fresh**, and `≈` is indistinguishability under the
RGA's queries (same live nodes, payloads, traversal order, dead-node
representation residue quotiented away). This datatype cannot take the
flat route: commutation over all states is false, a prefix-free variant
that drops the paths is provably impossible
(`RGA_PrefixFree_Impossible.lean`), and rehoming makes
replay-order-dependent residue unavoidable, so `≈` cannot be `=`. The
end-to-end instance theorem:

    rga_ra_linearizable3_eq :
      HonestDelivery →
      ∀ C reachable from initConfig (states quotiented by ≈),
        IsRALinearizable3Eq … C

This is the one definition above, at the general rendering, with the raw
`do`-fold as witness. The discharge replaces the swap-based repair of the
flat theory (unsound here: the needed intermediate states are unreachable)
with a **canonical-state engine** (the fold state is characterized as a
pure function of the applied event *set*) and a witness discipline joined
at merges by plain concatenation, no reordering.

The single assumption, `HonestDelivery`, is per-step *honest delivery*: at
each apply, the delivered op (1) was generated **accurately against a
causal fold of the events its replica had seen** (which is simply how a
client computes an op from its replica's state) and (2) is applicable at
the head version it is delivered to. Everything else is structural or
derived: Lamport clocks and timestamp uniqueness are `Configuration`
fields, and nonzero ids and nonzero delete targets follow from the
delivered op's own wellformedness. The full chain (quotient functor,
witness layer, canonical engine, the discharged merge bundle, the residual
reduction) lives in
[`MRDT_Instances/RGA_Rehoming/`](MRDT_Instances/RGA_Rehoming/)
(see its README for the file-by-file map), topped by
`RGA_Honest_Residual.lean`; an explicit-residual form
(`rga_RA_linearizable_final`, taking the two reachability-level premises
`hHon`/`hBA` directly) is available for substituting a different execution
model.

## Reading order

`Framework/MRDTSig.lean` → `Framework/ExecutionModel.lean` →
`Metatheory/LCA_Lemma.lean` → `Framework/Sigma_LoOn3.lean` →
`Framework/VC_Set.lean` → `Metatheory/Adequacy.lean` →
`MRDT_Instances/<RDT>/<RDT>.lean` → `Metatheory/GenericEqQuotient.lean` →
`Metatheory/GoodConfig3H.lean` →
`MRDT_Instances/RGA_Rehoming/RA_Lin.lean`.
The negative results that shaped all of this: [`Refutations/`](Refutations/).
Everything else: [`Development/`](Development/).

Lean namespace: `Sal.ConditionedMRDTs`. Build:
`lake build Sal.ConditionedMRDTs.MRDT_Instances.MRDT_Instances`
(the production capstones) **and**
`lake build Sal.ConditionedMRDTs.Refutations.Refutations`
(the negative results). The second target exists because refutations
are import leaves by design (nothing in
Framework/Metatheory/MRDT_Instances may import one except where a
counterexample is consumed as a gate): without its umbrella, PDF-cited
modules such as `InterLca2op_Defeater_Arbiter` and
`SiblingSplice_Fooling` sit outside every build target and can rot
silently.
