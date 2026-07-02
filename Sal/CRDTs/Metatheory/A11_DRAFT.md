# A11 (DRAFT). The (b″) conditional theorem MECHANIZED: `CoreVCs + LatticeVCs⁺ + CD ⇒ JoinLemma ⇒ RA-lin` — with (CD) discharged for AWSet and the commuting class 🔬✅ (0 sorry)

Follow-through on A10: the reduction skeleton sketched there is now
kernel-checked. The metatheorem has a third, sharpest form:

    ra_linearizable_of_core_lattice_cd :
      CoreVCs D → LatticeVCsPlus D → CDVC D →
      ReachableFrom initConfig C → IsRALinearizable C

where `LatticeVCsPlus` = merge associativity + idempotence +
**update-inflationarity** (`∀ s e, merge s (update s e) = update s e`)
— the complete state-based-CRDT contract, definitional for every real
lattice RDT — and `CDVC` is the **causal-delta bound**, the single
remaining per-CRDT obligation:

> for `e` maximal in `loOn(U)` over a backward-closed `U`,
> `A = σ(U∖e)`, `B = σ(↓e∖e)` (`↓e` = the `vis∧¬commutes` past of
> `e`):  `update A e ⊑ A ⊔ update B e`
> (where `x ⊑ y := x ⊔ y = y`).

(CD) is *half a peel identity*: an inequality, not an equation — the
converse inequality is a theorem of the lattice laws. Both peel
identities of `JoinPeelVCs` are consequences (via the Join Lemma), so
the per-CRDT burden strictly decreased from A9's bundle.

## What is proved (all 0 `sorry`)

[`JoinLemma_Of_CD.lean`](JoinLemma_Of_CD.lean):

* `LatticeVCsPlus`, `CDVC`, and the downset infrastructure
  (`downset`, `downset_closed`, `downset_vis`, `downset_max` — the
  *free peel*: `e` is automatically `loOn(↓e)`-maximal, no VC).
* Order algebra from the bundle: `update_mono` — monotonicity of
  update is free from `lem_0op` alone; inflation makes it an
  inflationary monotone map on the `⊑`-semilattice.
* `principal_case` — P(U,e): `σ(U∖e) ⊔ update σ(↓e∖e) e =
  update σ(U∖e) e`, canonical for `U`. `⊑` is IH-absorption +
  monotonicity + inflation; `⊒` is exactly (CD); antisymmetry closes.
* `side_decomposition` — `σ(E) = σ(E∖e) ⊔ update σ(↓e∖e) e` for any
  backward-closed `E ∋ e` inside `U` (IH when `E ⊊ U`; P itself when
  `E = U`).
* `join_lemma_of_cd : CoreVCs D → LatticeVCsPlus D → CDVC D →
  JoinLemma D` — strong induction on `|E₁ ∪ E₂|`.
* `cdVC_of_all_comm` — the commuting class discharges (CD) for free:
  `↓e∖e = ∅`, so `B = init` and the bound holds with equality by
  `merge_peel_comm` + idempotence.
* `ra_linearizable_of_core_lattice_cd` — the end-to-end bridge,
  replaying A9's `GoodConfig` induction with `join_lemma_of_cd`.
* `AWSetF_not_latticeVCsPlus` — the A10 separator fails exactly
  `update_inflation`, so the new bundle is tight against A10.

[`CD_AWSet.lean`](CD_AWSet.lean):

* `AWSet_latticeVCsPlus` — unions are ACI; both update shapes inflate.
* `AWSet_cdVC` — **the AWSet discharge**. `e = add`: context-free set
  algebra (an add's delta is its own timestamp, generated already at
  `B`). `e = rem`: ONE inclusion, `adds(U∖e) ⊆ killed(U∖e) ∪
  adds(↓e∖e)` — the A7 trichotomy: an add of `U∖e` either observed
  `e`'s issue point (∈ `↓e∖e`) or, by maximality, has an absorber
  `z ≠ e` in `U` (already dead in `U∖e`).
* `AWSet_joinLemma_via_cd`, `AWSet_ra_linearizable_via_cd` — the full
  metatheorem for AWSet through the (b″) route.

**Usability comparison (honest).** Both routes share the
σ-characterization (`AWSet_canonical_eq` and its sandwich invariant,
~150 lines of `Convergence_CounterModel.lean`). Beyond it, the
`JoinPeelVCs` route (A7) needs four set-algebra lemmas +
`no_absorber_of_max` + `awAdds_killed_of_rem_max` + the two peel
proofs — lines 899–1096 of `Convergence_CounterModel.lean`, ≈ 197
lines. The (CD) route needs `AWSet_cdVC` (58 lines, of which the
trichotomy inclusion `h_key` is 25) plus the trivial lattice bundle
(28 lines): ≈ 86 lines, under half. More importantly the *shape* is
simpler: no peel-context bookkeeping over two event sets — a single
`U`, a single inclusion, and the add-case is context-free `tauto`.

## Where the mechanization diverged from the A10 paper skeleton

The mechanized induction is *simpler* than sketched. A10 planned
separate cases for `E₁ ⊆ E₂` (absorption) vs. incomparable sides,
with the subset case routed through P on the big side. In the
mechanization the subset-ness never enters: for the `loOn(∪)`-maximal
`e`, each side containing `e` decomposes as `σ(E) = σ(E∖e) ⊔ σ(↓e)` —
by the IH when `E ⊊ U` and *by P itself* when `E = U` (this is the
only place the case distinction survives, hidden inside
`side_decomposition`) — and the `e`-free residue always contracts to
`σ(U∖e)` by an IH instance at union `U∖e`, size `n−1`, regardless of
how the sides overlap. Absorption instances are just the `E = U`
branch. Idempotence is consumed in exactly one spot (collapsing
`σ(↓e) ⊔ σ(↓e)` when `e` is shared); associativity+commutativity in
the two re-association helpers; inflation and (CD) only inside P.
The buried-event difficulty (A3/A5) dissolves structurally: no peel
of `e` from a *side's own* linearization is ever demanded — only
join-decompositions, which exist by induction.

One planned lemma was dropped as **false-as-stated**: A10's
"`joinPeelVCs_iff_joinLemma`". `JoinPeelVCs` quantifies over
configurations *without* `vis`-transitivity/irreflexivity hypotheses,
which the Join Lemma requires; so `JoinLemma → JoinPeelVCs` is not
provable at those types. Harmless: the A9 bridge consumes
`JoinPeelVCs` only through `join_lemma_of_peel`, so the end-to-end
theorem goes through `JoinLemma` directly.

## (b″) proper: is (CD) derivable? — OPEN, sharpened

What remains open is exactly whether (CD) is a *theorem* of
`CoreVCs + LatticeVCsPlus` (making the per-CRDT burden empty), or
per-CRDT-irreducible (needing a countermodel). Both directions were
probed:

* **Countermodel attempts fail on `cond_comm_lift`.** By `lem_0op`,
  any extra semilattice component's update-delta must be a
  join-homomorphism of the state on synchronized pairs — on powerset
  states, a union of element-wise images of components. Untagged
  accumulating deltas (copy `dead`, copy `added`, monotone conflict
  levels) all *satisfy* (CD) via a trichotomy + an accumulation
  invariant ("the same delta already fired at earlier events of
  `U∖e`"). The natural way to defeat accumulation — tagging the delta
  with the firing event's timestamp (`rem_t : X += {t} × (A ∪ D)`) —
  is killed by `cond_comm_lift`: swapping a concurrent
  `rc`-ordered pair (`rem` before/after an `add`) changes the tagged
  copy by `{(t_e, t')}` and *no later event can absorb the
  difference*, since tagged sets only grow and later deltas carry
  different tags. `cond_comm_lift` thus forces deltas to be
  *self-absorbing* under exactly the reorderings whose invisibility
  (CD) needs. This is strong structural evidence for (b″)-positive.
* **Proof attempts stall at a characterization lemma.** With the
  now-mechanized machinery, `A = σ(U∖e)` decomposes (by the IH) into
  `⊔_{x ∈ U∖e} σ(↓x)`, and `lem_0op` splits
  `update A e = ⊔ₓ update σ(↓x) e`; (CD) reduces to the per-downset
  bound `update σ(↓x) e ⊑ A ⊔ update σ(↓e∖e) e`. For `x` with
  `¬commutes(e,x)`, maximality gives the trichotomy shape; for
  commuting `x` there is *no* maximality information, and the bound
  must come from a semantic principle — roughly "`e`'s delta cannot
  distinguish states that differ only by events absorbed within
  themselves", which is a sequence-level consequence of
  `cond_comm_lift` not yet expressible state-level.

**The residual question, stated cold** (for a fresh agent):

> Let `D` satisfy `CoreVCs D` and `LatticeVCsPlus D`. Prove or refute:
> `CDVC D` (defined at `Sal/CRDTs/Metatheory/JoinLemma_Of_CD.lean`,
> `CDVC`). Equivalently by `join_lemma_of_cd` + the A10 countermodel
> chain: does `CoreVCs + LatticeVCsPlus` imply the Join Lemma?
> Suggested attack for the positive direction: prove an abstract
> absorption-invariance lemma — for `z` with `vis x z`,
> `¬commutes x z`, `z ∈ E`, the canonical state `σ(E)` and the
> `e`-delta at `σ(E)` are invariant under "burying `x` deeper", by
> lifting `cond_comm_lift` from sequences to canonical states.
> For the negative direction: the countermodel's extra component must
> carry a join-hom, self-absorbing, yet causally-leaky delta — the
> tagged-copy family is excluded (see above), so it would need
> element-wise images `f` with non-trivial kernel collapse
> (`f` merging timestamps across concurrent events). No such
> candidate survived `merge_peel_comm` + `cond_comm_lift` in ~six
> attempts.

## The metatheorem landscape after A8–A11

| Bundle | Status |
|---|---|
| `CoreVCs` alone | ✗ RA-lin fails reachably (A8: `AWSetX`, non-assoc; not even a lattice) |
| `CoreVCs + LatticeVCs` (ACI) | ✗ RA-lin fails reachably (A10: `AWSetF`, deflationary update) |
| `CoreVCs + LatticeVCsPlus` (ACI + inflation) | **open (b″)** — no separator survives `cond_comm_lift`; no generic proof of (CD) yet |
| `CoreVCs + LatticeVCsPlus + CDVC` | ✅ RA-lin, end-to-end, 0 sorry (A11); (CD) discharged for AWSet + commuting class |
| `CoreVCs + JoinPeelVCs` | ✅ RA-lin (A9); strictly heavier per-CRDT burden than (CD) |

## Artifacts

| File | Content | `sorry` |
|---|---|---|
| `Sal/CRDTs/Metatheory/JoinLemma_Of_CD.lean` | `LatticeVCsPlus`; `CDVC`; downset theory; `principal_case`; `side_decomposition`; `join_lemma_of_cd`; `cdVC_of_all_comm`; `ra_linearizable_of_core_lattice_cd`; `AWSetF_not_latticeVCsPlus` | 0 |
| `Sal/CRDTs/Metatheory/CD_AWSet.lean` | `AWSet_latticeVCsPlus`; `AWSet_cdVC`; `AWSet_joinLemma_via_cd`; `AWSet_ra_linearizable_via_cd` | 0 |

Axiom audit (`#print axioms`, run and reverted):
`join_lemma_of_cd`, `ra_linearizable_of_core_lattice_cd`,
`AWSet_cdVC`, `AWSet_ra_linearizable_via_cd`, `cdVC_of_all_comm`
depend only on `[propext, Classical.choice, Quot.sound]`.
