# Sal/MRDTs/Metatheory — RA-linearizability for MRDTs (ternary merge)

A mechanized soundness metatheory for MRDTs (three-way `merge lca a b` over a
version DAG — the setting of the Neem paper's Theorem 2, arXiv:2502.19967 /
OOPSLA 2025), built on the corrected binary theory of
[`Sal/CRDTs/Metatheory/`](../../CRDTs/Metatheory/). Everything below is
0-sorry and kernel-checked (axioms: `propext`, `Classical.choice`,
`Quot.sound`). The paper-style companion note —
[`mrdt-metatheory.pdf`](mrdt-metatheory.pdf) — is the self-contained
account of everything in this directory, from the definition of an MRDT
through the eight VCs to the conditioned end-to-end proof.
The conditioned framework and the tombstone-free-RGA chain live in
[`Conditioned/`](Conditioned/); the research record (findings T0–T10.7,
planning docs, the historical peel route, the impossibility results,
refutation probes) is in [`Development/`](Development/), which may import
`Conditioned/` but never the reverse.

**The signature — one framework.** An MRDT presents the *conditioned*
signature (`ConditionedMRDTSig`, [`MRDTSig.lean`](MRDTSig.lean))

    ⟨ Σ, σ₀, do, mergeL, rc, Inv, applicable ⟩

together with an observational equivalence `≈` on states (`EqEquiv`,
[`Conditioned/GenericEqQuotient.lean`](Conditioned/GenericEqQuotient.lean)):
a state space with initial state, the update `do`, the three-way merge
`mergeL l a b` (LCA first), the conflict-resolution policy `rc` for
concurrent non-commuting pairs, a state invariant `Inv` (a shape
over-approximation of reachability), an applicability predicate
`applicable` (when an op is sensible at a state — it may read the op's
timestamp), and `≈` (what clients can distinguish). Commutation is
**conditioned** (`commutesOn`): two ops must commute only at `Inv`-states
where both are applicable. **Flat datatypes** — counters, sets, registers,
everything whose ops make sense on every state — take
`Inv = applicable = ⊤` and `≈` := `=`; that specialization collapses to the
unconditioned theory, and §§1–3 below are exactly it. §4 is the framework
at full generality, exercised by the one production datatype that needs it.

**The setting.** Replicas fork, apply operations locally, and merge,
git-style. The LTS (`Step3`, [`ExecutionModel.lean`](ExecutionModel.lean),
[`LCA_Lemma.lean`](LCA_Lemma.lean)) keeps a ranked **version store**: every
apply and merge allocates a fresh version carrying its `(state, event set)`
pair, and merge takes the two head states *plus the state at their lowest
common ancestor* (LCA) in the version DAG. Events are timestamped ops
`(t, r, o)`; visibility `vis` is the causal order delivery induces
(Lamport-monotone timestamps and causally-closed logs are structural fields
of `Configuration` — executions violating them are unrepresentable).

**The property — one definition.** The **linearization order** `lo` on an
event set `E` orders exactly the pairs a correct sequential replay must not
invert: a `vis`-related non-`commutesOn` pair in `vis` order, and a
concurrent non-`commutesOn` pair by `rc` (unless a still-later
non-commuting event already overrides the later one). `lo` is partial and
not transitive, so "π respects `lo`" is the pairwise no-inversion
condition, not sortedness. **RA-linearizability, per version, up to `≈`**:
in every reachable configuration, *every* stored version `(s, E)` — LCAs
included, not just replica heads — satisfies

    ∃ π, π a lo-respecting permutation of E  ∧  fold do σ₀ π ≈ s .

This single definition has two mechanized renderings: at the flat
specialization `≈` is `=` and it is `IsRALinearizable3`
([`Adequacy.lean`](Adequacy.lean)); in general the store holds `≈`-classes
and it is `IsRALinearizable3Eq`
([`Conditioned/GoodConfig3H.lean`](Conditioned/GoodConfig3H.lean)), with
the *raw* `do`-fold as witness. The **canonical state** `σ(E)` is that
fold, well-defined (up to `≈`) because the theory forces all such folds of
`E` to agree.

## 1. The VC set (the flat discharge engine) — [`VC_Set.lean`](VC_Set.lean)

**Eight verification conditions** discharge a flat datatype
(`Inv = applicable = ⊤`, `≈` = `=`, signature reduced to
`⟨Σ, σ₀, do, mergeL, rc⟩`); what they buy — the closure-indexed Join
Lemma — is exactly what the generic theorem of §4 consumes at the identity
instantiation:

Update layer (`UpdateVCs`, defined in [`Sigma_LoOn3.lean`](Sigma_LoOn3.lean)):
1. `rc_non_comm_directional` — for *different-replica* events with distinct
   timestamps, non-commutativity ⟺ `rc`-ordered in some direction (the
   `differentReplicas` guard is the paper's own F* interface form;
   same-replica pairs are ordered by `vis`-totality instead);
2. `no_rc_chain` — no two consecutive `rc` edges;
3. `cond_comm_lift` — the conditional-commutativity swap survives any
   intervening suffix ending in a non-commuting event.

Merge layer:
4. `mergeL_comm` — `mergeL l a b = mergeL l b a` (`CoreVCs3CD`);
5. `feasible_init` — `mergeL σ₀ σ₀ σ(E) = σ(E)` on canonical states;
6. `feasible_local_redistribute` — a downset-delta application commutes past
   an enclosing merge, on canonical tuples at honest LCAs;
7. `feasible_redistribute` — a delta applied to all three components
   extracts once (the LCA slot cancels the duplicate — this is what
   idempotence did in the binary theory, done by LCA arithmetic);
8. `CDVC3` — the causal-delta equation: for a `loOn(U)`-maximal event `e`,
   `mergeL σ(↓e∖e) σ(U∖e) (do σ(↓e∖e) e) = do σ(U∖e) e`.

On-ramps and variants: `DeltaVCs3` (laws 6–7 unconditional — exactly the
group ⊕ lattice classes: Counter, G-Set, every LCA-blind CRDT);
`JoinLemma3F` (the **full-causal-closure** join notion — counter-comparison
merges like the Enable-wins flag provably need full closure, not just
commutation closure; reunifying this with the feasible route is open).

## 2. Adequacy (the flat engine's internal form) — [`Adequacy.lean`](Adequacy.lean)

    ra_linearizable_of_core_feasible_cd3 :
      CoreVCs3CD D → FeasibleDeltaVCs3 D → CDVC3 D →
      ∀ C reachable from initConfig in the ternary system Step3,
        IsRALinearizable3 C

— the definition above at `≈` := `=`, in its historical direct form (the
headline per-instance results are the §3 theorems through the generic
framework; this chain remains as the engine that validates the VC set and
supplies each instance's Join Lemma). The proof carries `GoodConfig3`
(every version canonical + store closure facts) through the LTS of
[`LCA_Lemma.lean`](LCA_Lemma.lean); the merge case is the Join Lemma
obtained by `join_lemma3_of_cd_feasible`.
Also here: the unconditional-route bridge (`ra_linearizable_of_core_delta_cd3`),
the commuting-class discharge of CD (`cdVC3_of_all_comm`), and the
full-closure bridge (`ra_linearizable3_of_joinF`) used by the Enable-wins
route. The LCA lemma `L(v_⊤) = L(v₁) ∩ L(v₂)` and its maintainability are
proved in [`LCA_Lemma.lean`](LCA_Lemma.lean).

## 3. The discharged MRDTs —
[`MRDT_Instances_Generic.lean`](MRDT_Instances_Generic.lean)

Every production instance concludes `IsRALinearizable3Eq` **through the one
generic theorem** (§4); what differs per datatype is the instantiation and
the discharge of its Join Lemma (the VC bundles live in
[`MRDT_Instances.lean`](MRDT_Instances.lean)):

| MRDT | End-to-end theorem | Instantiation / discharge |
|---|---|---|
| **OR-Set** (production mirror) | `ORSet_ra_linearizable3_eq` | identity (`≈`=`=`); feasible + CD |
| **OR-Set-efficient** (production mirror) | `ORSetE_ra_linearizable3_eq` | identity; feasible + CD |
| **Enable-wins flag** (production mirror) | `EWFlag_ra_linearizable3_eq` | identity; direct full-closure join |
| **Grow-Only Set** (production mirror) | `GOSet_ra_linearizable3_eq` | identity; unconditional delta |
| **Grow-Only Map** (production mirror) | `GOMap_ra_linearizable3_eq` | identity; unconditional delta |
| **Increment-Only Counter** (production mirror) | `IOC_ra_linearizable3_eq` | identity; unconditional delta |
| **PN-Counter** (production mirror) | `PN_ra_linearizable3_eq` | identity; unconditional delta |
| **RGA, tombstone** (production mirror) | `RGAM_ra_linearizable3_eq` | identity; unconditional delta |
| **Peritext** (production mirror) | `Peritext_ra_linearizable3_eq` | identity; unconditional delta |
| **Multi-Valued Register** (production mirror) | `MVR_ra_linearizable3_eq` | identity; feasible (all-comm, `B = init`) |
| **Add-Wins Priority Queue** (production mirror) | `AWPQ_ra_linearizable3_eq` | identity; feasible (OR-Set pattern on A) |
| **RGA, tombstone-free** (production) | `rga_tombstone_free_ra_linearizable3_eq` | full generality (§4) |

**The production catalogue is complete: every MRDT shipped in Sal carries a
kernel-checked end-to-end theorem through the one framework.** The
historical flat corollaries (`*_ra_linearizable3` over the raw system, plus
the Counter/G-Set specimens) remain in
[`MRDT_Instances.lean`](MRDT_Instances.lean) as internal steps of the
engine.

The production mirrors are faithful to `Sal/MRDTs/{OR_Set,
OR_Set_Efficient, Enable_Wins_Flag}` (documented deviations only). The
Enable-wins discharge certifies the production per-replica `merge_flag` on
exactly the corner (`inter_right_1op`) where its known-broken
global-counter sibling fails.

## 4. THE framework — [`RGA_TombstoneFree_RA_Lin.lean`](RGA_TombstoneFree_RA_Lin.lean)

The soundness theorem is generic — stated over *any* `ConditionedMRDTSig`
with an `EqEquiv`, on the same `Step3` LTS: the **`≈`-quotient functor** `D ↦ D≈` builds the datatype whose states
are `≈`-classes of `Inv`-states, with update, merge and `applicable`
descending by congruence
([`Conditioned/GenericEqQuotient.lean`](Conditioned/GenericEqQuotient.lean));
on top, a **witness-disciplined reachability layer** carries, per version,
an enumeration witness for the general definition above, maintained at
applies and joined at merges (`RA_linearizable_up_to_eq_H`,
[`Conditioned/GoodConfig3H.lean`](Conditioned/GoodConfig3H.lean)). The
datatype's obligations, replacing the eight flat VCs: `≈` is an equivalence
(`EqEquiv`), `Inv` is preserved on wellformed ops (`InvPres`),
update/merge/query are `≈`-congruent on `Inv` (`CongVC`, `InvInvVC`), and
the merge is, up to `≈`, the fold of a `lo`-respecting enumeration of the
joined events (the `≈`-Join, `EqJoinLemma3C_H`). Instantiated flat
(`Inv = applicable = ⊤`, `≈` = `=`) these collapse into the ordinary Join
Lemma of §2 — mechanized as `Conditioned/FlatGeneric_Bridge.lean`, which is
how the nine flat instances of §3 ride the same theorem.

**The exercising instance: the tombstone-free RGA**
([`../RGA_Tombstone_Free/`](../RGA_Tombstone_Free)) — a replicated list
whose deletes *physically remove* nodes, no tombstone set; every op carries
its target's recorded ancestor path, and merge re-anchors each surviving
node by climbing that path to the nearest survivor. Here `Inv` is the
forest well-formedness (with id-monotone anchors), `applicable` is
**accurate** (the recorded path is the target's true live ancestor chain)
**∧ fresh**, and `≈` is indistinguishability under the RGA's queries (same
live nodes, payloads, traversal order — dead-node representation residue
quotiented away). This datatype cannot take the flat route: commutation
over all states is false, a prefix-free variant that drops the paths is
provably impossible (`RGA_PrefixFree_Impossible.lean`), and rehoming makes
replay-order-dependent residue unavoidable, so `≈` cannot be `=`. The
end-to-end instance theorem:

    rga_tombstone_free_ra_linearizable3_eq :
      HonestDelivery →
      ∀ C reachable from initConfig (states quotiented by ≈),
        IsRALinearizable3Eq … C

— the one definition above, at the general rendering, with the raw
`do`-fold as witness. The discharge replaces the swap-based repair of the
flat theory (unsound here: the needed intermediate states are unreachable)
with a **canonical-state engine** — the fold state is characterized as a
pure function of the applied event *set* — and a witness discipline joined
at merges by plain concatenation, no reordering.

The single assumption, `HonestDelivery`, is per-step *honest delivery*: at
each apply, the delivered op (1) was generated **accurately against a
causal fold of the events its replica had seen** — which is simply how a
client computes an op from its replica's state — and (2) is applicable at
the head version it is delivered to. Everything else is structural or
derived: Lamport clocks and timestamp uniqueness are `Configuration`
fields, and nonzero ids and nonzero delete targets follow from the
delivered op's own wellformedness. The full chain (quotient functor,
witness layer, canonical engine, the discharged merge bundle, the residual
reduction) is kernel-clean under [`Conditioned/`](Conditioned/), topped by
`RGA_Honest_Residual.lean`; an explicit-residual form
(`rga_RA_linearizable_final`, taking the two reachability-level premises
`hHon`/`hBA` directly) is available for substituting a different execution
model.

## Reading order

`MRDTSig.lean` → `ExecutionModel.lean` → `LCA_Lemma.lean` →
`Sigma_LoOn3.lean` → `VC_Set.lean` → `Adequacy.lean` →
`MRDT_Instances.lean` → `MRDT_Instances_Generic.lean` →
`RGA_TombstoneFree_RA_Lin.lean`.
Everything else: [`Development/`](Development/).

Lean namespace: `Sal.Metatheory`. Build:
`lake build Sal.MRDTs.Metatheory.<Module>`.
