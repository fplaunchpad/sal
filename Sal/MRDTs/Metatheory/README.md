# Sal/MRDTs/Metatheory — RA-linearizability for MRDTs (ternary merge)

A mechanized soundness metatheory for MRDTs (three-way `merge lca a b` over a
version DAG — the setting of the Neem paper's Theorem 2, arXiv:2502.19967 /
OOPSLA 2025), built on the corrected binary theory of
[`Sal/CRDTs/Metatheory/`](../../CRDTs/Metatheory/). Everything below is
0-sorry and kernel-checked (axioms: `propext`, `Classical.choice`,
`Quot.sound`). The full research record (findings T0–T10.7, planning docs,
the historical peel route, the impossibility results) is in
[`Development/`](Development/).

## 1. The VC set — [`VC_Set.lean`](VC_Set.lean)

**Eight verification conditions** suffice for RA-linearizability. For an
MRDT `⟨Σ, σ₀, do, mergeL, rc⟩`:

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

## 2. Adequacy — [`Adequacy.lean`](Adequacy.lean)

    ra_linearizable_of_core_feasible_cd3 :
      CoreVCs3CD D → FeasibleDeltaVCs3 D → CDVC3 D →
      ∀ C reachable from initConfig in the ternary system Step3,
        IsRALinearizable3 C

`IsRALinearizable3` is **per version**: every version in the store (LCAs
included, not just replica heads) is a `lo`-respecting linearization of its
event set. The proof carries `GoodConfig3` (every version canonical + store
closure facts) through the LTS of [`LCA_Lemma.lean`](LCA_Lemma.lean); the
merge case is the Join Lemma obtained by `join_lemma3_of_cd_feasible`.
Also here: the unconditional-route bridge (`ra_linearizable_of_core_delta_cd3`),
the commuting-class discharge of CD (`cdVC3_of_all_comm`), and the
full-closure bridge (`ra_linearizable3_of_joinF`) used by the Enable-wins
route. The LCA lemma `L(v_⊤) = L(v₁) ∩ L(v₂)` and its maintainability are
proved in [`LCA_Lemma.lean`](LCA_Lemma.lean).

## 3. The discharged MRDTs — [`MRDT_Instances.lean`](MRDT_Instances.lean)

One file, all instance proofs:

| MRDT | End-to-end theorem | Route |
|---|---|---|
| **OR-Set** (production mirror) | `ORSet_ra_linearizable3` | feasible + CD |
| **OR-Set-efficient** (production mirror) | `ORSetE_ra_linearizable3` | feasible + CD |
| **Enable-wins flag** (production mirror) | `EWFlag_ra_linearizable3` | direct full-closure join |
| Counter (`mergeL l a b = a+b−l`) | `counter_ra_linearizable3_cd` | unconditional delta |
| G-Set | `gset_ra_linearizable3_cd` | unconditional delta |
| **Grow-Only Set** (production mirror) | `goset_ra_linearizable3` | unconditional delta |
| **Grow-Only Map** (production mirror) | `gomap_ra_linearizable3` | unconditional delta |
| **Increment-Only Counter** (production mirror) | `ioc_ra_linearizable3` | unconditional delta |
| **PN-Counter** (production mirror) | `pn_ra_linearizable3` | unconditional delta |
| **RGA, tombstone** (production mirror) | `rga_ra_linearizable3` | unconditional delta |
| **Peritext** (production mirror) | `peritext_ra_linearizable3` | unconditional delta |
| **RGA, tombstone-free** (production) | `rga_tombstone_free_ra_linearizable3_eq` | conditioned end-to-end (§4) |
| all-commuting class | via `cdVC3_of_all_comm` | generic |

Not yet mechanized (class-placed with recipes, draft T11.3–T11.4):
Multi-Valued Register and Add-Wins Priority Queue (feasible class).

The production mirrors are faithful to `Sal/MRDTs/{OR_Set,
OR_Set_Efficient, Enable_Wins_Flag}` (documented deviations only). The
Enable-wins discharge certifies the production per-replica `merge_flag` on
exactly the corner (`inter_right_1op`) where its known-broken
global-counter sibling fails.

## 4. The conditioned route — tombstone-free RGA —
[`RGA_TombstoneFree_RA_Lin.lean`](RGA_TombstoneFree_RA_Lin.lean)

    rga_tombstone_free_ra_linearizable3_eq :
      HonestDelivery →
      ∀ C reachable from initConfig in the quotient ternary system,
        IsRALinearizable3Eq … C

The tombstone-free path-carrying RGA
([`../RGA_Tombstone_Free/`](../RGA_Tombstone_Free)) **cannot** go through
the VC schema above: its commutation only holds *conditioned* on
reachable/accurate states (tombstone-freedom forces delete-rehoming, which
is only correct against states reflecting the op's causal past — and a
prefix-free variant is provably impossible). The result is instead a direct
end-to-end theorem through an **applicability-conditioned metatheory**: the
observational quotient `D ↦ D≈`, an H-disciplined canonical-witness layer
over the same `Step3` LTS, and the RGA's canonical-state engine. The target
is RA-linearizability **up to observational equivalence** — every version
of every reachable configuration is, up to `≈`, the raw `do_`-fold of a
`lo`-respecting linearization of its events.

The single irreducible assumption (`HonestDelivery`) is per-step *honest
delivery*: each delivered op was generated accurately against a causal fold
of the events its replica had seen (born accuracy — how an RGA client
actually works), and delivery is born-applicable. Lamport clocks and
timestamp uniqueness are structural (dishonest-clock executions are
unrepresentable in `Configuration`); nonzero ids and nonzero delete targets
are derived from the op's own wellformedness. The full chain (quotient
functor, canonical engine, the discharged capstone leaves, the residual
reduction) is kernel-clean under [`Development/`](Development/), with
`RGA_Honest_Residual.lean` at the top; the explicit-residual form
(`rga_RA_linearizable_final`, premises `hHon`/`hBA` instead of
`HonestDelivery`) is available for substituting a different execution
model.

## Reading order

`MRDTSig.lean` → `ExecutionModel.lean` → `LCA_Lemma.lean` →
`Sigma_LoOn3.lean` → `VC_Set.lean` → `Adequacy.lean` →
`MRDT_Instances.lean` → `RGA_TombstoneFree_RA_Lin.lean`.
Everything else: [`Development/`](Development/).

Lean namespace: `Sal.Metatheory`. Build:
`lake build Sal.MRDTs.Metatheory.<Module>`.
