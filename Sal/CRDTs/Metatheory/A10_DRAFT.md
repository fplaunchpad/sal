# A10 (DRAFT). Open (b′) REFUTED: `CoreVCs` + full lattice laws do NOT imply `JoinPeelVCs` — the boundary is update-inflationarity 🔬✅

**Question resolved.** A8 asked (open (b′)):

> does `CoreVCs D` + `merge` associativity (+ idempotence) imply
> `JoinPeelVCs D`?

**Answer: NO** — machine-checked, 0 `sorry`. There is a `D` whose merge
is a *bona fide bounded join-semilattice* (commutative, associative,
idempotent, `init`-unital), satisfying every field of `CoreVCs`, for
which `peel_local` fails, the Join Lemma fails, **and RA-linearizability
itself fails on a reachable configuration**. The lattice laws are not
the missing ingredient; **update-inflationarity** is.

## The separator `AWSetF` (the last-op flag)

[`Assoc_CounterModel.lean`](Assoc_CounterModel.lean)
(0 `sorry`). State = `AWState × Bool`; base component exactly `AWSet`
(same `update`, union-merge, same `rc`); the extra Boolean is **written
by every update** — `add` sets `true`, `rem` sets `false` — and merged
by `∨` from initial `false`:

    update ((A,D), m) e = (awUpdate (A,D) e, flag e)   flag(add)=true, flag(rem)=false
    merge  ((A,D), m) ((A',D'), m') = (awMerge (A,D) (A',D'), m ∨ m')

`(Bool, ∨, false)` is a semilattice with unit, so the merge is ACI-1
(`AWSetF_latticeVCs`). The flag after any nonempty history is just *the
kind of the last op* — it has no memory.

**Why every `CoreVCs` field survives** (`AWSetF_coreVCs`): each equation
of the bundle either (i) ends both sides in the *same* update — the
update-level fields `rc_non_comm_directional` / `no_rc_chain` /
`cond_comm_lift`, and `lem_0op` (`flag ol ∨ flag ol = flag ol`) — or
(ii) merges against a fold of *commuting* events from `init` —
`merge_peel_comm`, where `e = add` absorbs the join (`true ∨ _`), and
`e = rem` forces the π-side to be all-rems whose fold-flag is `false`.
The flag is invisible to the entire bundle *and* to the lattice laws.
(`commutes` is unchanged: the flag makes add/rem non-commuting — they
already were — and leaves add/add, rem/rem commuting.)

**Why the peel dies** (`AWSetF_not_joinPeelVCs`): `peel_local`'s two
sides end *differently* — the left is a merge (flag = join of flags),
the right ends in `update e`. On the canonical two-replica
configuration (replica 0: `aF = add` then `eF = rem`, `vis aF eF`;
replica 1 merged in between, holding `{aF}`), with `ev₁ = {aF, eF}`,
`ev₂ = {aF}`, `e = eF` union-maximal:

    merge σ(ev₁) σ(ev₂)               flag = false ∨ true = true
    update (merge σ(ev₁∖e) σ(ev₂)) eF flag = flag(rem)     = false

The Join Lemma fails on the same instance (`AWSetF_not_joinLemma`):
the only `loOn(∪)`-respecting enumeration `[aF, eF]` folds to flag
`false` ≠ the merge's `true`. Note the instance has `ev₂ ⊆ ev₁`, so
what fails is precisely **absorption** (`E₁ ⊆ E₂ ⇒ σ(E₁) ⊔ σ(E₂) =
σ(E₂)`, the `merge_absorb_sub` candidate residual of the (b′)
analysis): even the degenerate subset case of the Join Lemma is
out of reach of `CoreVCs` + ACI. Headline:
`coreVCs_lattice_insufficient : ∃ D, CoreVCs D ∧ LatticeVCs D ∧
¬ JoinPeelVCs D ∧ ¬ JoinLemma D`.

## END-TO-END: RA-linearizability itself fails, reachably

[`Assoc_CounterModel_Reachable.lean`](Assoc_CounterModel_Reachable.lean)
(0 `sorry`) closes the "maybe `JoinPeelVCs` was stronger than needed"
loophole. The five-step execution

    createReplica 1; apply add@r0; merge r1←r0; apply rem@r0; merge r1←r0

is exhibited step-by-step from `initConfig`
(`flagC5_reachable`), and its final configuration is **not
RA-linearizable** (`flagC5_not_ra_linearizable`): replica 1 holds flag
`true`, but the only `lo`-respecting witness `[aF, eF]` folds to flag
`false`. Headline: `ra_linearizability_fails_for_lattice_CRDTs`:

    ∃ D C, CoreVCs D ∧ LatticeVCs D ∧ ReachableFrom initConfig C ∧ ¬ IsRALinearizable C

So no proof route whatsoever — not just the σ/`loOn`/Join route —
derives the Neem/Sal metatheorem from `CoreVCs` + the lattice laws.
Contrast A9: with `JoinPeelVCs` instead of `LatticeVCs` the conclusion
is a theorem (`ra_linearizable_of_core_join`).

## Where the true boundary lies: inflationarity

`AWSetF`'s update is **not inflationary** w.r.t. the merge order:
`rem` strictly *decreases* the flag —
`AWSetF_update_not_inflationary : ¬ ∀ s e, merge s (update s e) = update s e`.
Every genuine state-based CRDT satisfies update-inflationarity: it is
the *other half* of the convergent-replication contract, alongside the
ACI merge. So the correct sharpening of (b′) is:

> **Open (b″): does `CoreVCs D` + merge ACI + update-inflationarity
> (`∀ s e, D.merge s (D.update s e) = D.update s e`) imply
> `JoinPeelVCs D` (equivalently, `JoinLemma D`)?**

(b″) is now tight from below in *both* directions: drop associativity
and A8's `AWSetX` refutes it; keep the full lattice laws but drop
inflationarity and `AWSetF` refutes it.

## Evidence for (b″), and the reduction skeleton

A paper-level induction (checked by hand against the A3 defeater and
against `AWSetF`-style flag models made inflationary — which then
*stop* separating) reduces `JoinLemma` under
`CoreVCs + ACI + inflation` to a single residual inequality. Sketch,
by strong induction on `n = |E₁ ∪ E₂|` (write `σ` for canonical
states, `⊔` for merge, `↓e` for the `vis∧¬comm`-backward-closure of
`{e}`, `M(n)` for the Join Lemma at union-size `n`, and `x ⊑ y` for
`x ⊔ y = y`):

1. **Free peel of a principal downset.** For any `e`, every element of
   `↓e∖{e}` is `vis`-before `e`, so `e` is automatically
   `loOn(↓e)`-maximal and `σ(↓e) = update σ(↓e∖e) e`
   (`isCanonicalState_snoc` + uniqueness; no VC needed).
2. **Both peel cases reduce to the principal case.** With `e`
   `loOn(∪)`-maximal: `σ(E₁) = σ(E₁∖e) ⊔ σ(↓e)` is an `M(<n)` instance
   (union `E₁`; `↓e ⊆ E₁` by backward closure); re-associating (ACI;
   idempotence collapses the shared `σ(↓e) ⊔ σ(↓e)` in the shared
   case) and applying `M(n−1)` to `(E₁∖e, E₂)` gives
   `σ(E₁) ⊔ σ(E₂) = σ(U∖e) ⊔ σ(↓e)`. Subset/absorption cases
   (`E₁ ⊆ E₂`) reduce to the same statement plus `M(n−1)`; `E₁ = E₂`
   is idempotence. So everything reduces to
   **P(U, e):** `σ(U∖e) ⊔ σ(↓e) = update σ(U∖e) e` for `e`
   `loOn(U)`-maximal.
3. **P splits along the lattice order.** Let `A = σ(U∖e)`,
   `B = σ(↓e∖e)`; `M(n−1)` gives absorption `B ⊑ A`. From `lem_0op`,
   update is *monotone* (`a ⊑ b ⇒ update a e ⊑ update b e` — join
   `lem_0op` with the definition of `⊑`); with inflation this gives
   `A ⊔ update B e ⊑ update A e` by pure ACI algebra. The converse is
   the one open piece:

   > **(CD) causal-delta bound:** `update A e ⊑ A ⊔ update B e` —
   > in context (`e` union-maximal, `A = σ(U∖e)`, `B = σ(↓e∖e)`,
   > both backward-closed).

   I.e. *the effect of `e` on the full state is generated by its
   effect on its own causal past, modulo the state itself*. For
   `AWSet`, (CD) *is* the A7 trichotomy (`A₁ ⊆ A₂ ∪ B₁`: every add of
   `U∖e` is either dead in `U∖e` or in `e`'s past — maximality +
   backward closure). For the commuting class it is an equality via
   `merge_peel_comm` with `B = init`.

So modulo mechanizing the skeleton, `CoreVCs + ACI + inflation + (CD)
⇒ JoinLemma ⇒ RA-lin (A9)`, and (b″) is exactly the question whether
(CD) is derivable or must remain the (single, inequality-shaped)
per-CRDT VC. Note (CD) is strictly weaker-looking than the two peel
*equations* of `JoinPeelVCs`: the other direction of P comes for free
from the lattice laws. The `lem_0op`-forcing observed in A8 also
constrains candidate (b″)-separators severely: any extra component's
update-delta must be a join-homomorphism on synchronized pairs, and
every such homomorphic-delta model tried (dead-set copies, monotone
conflict levels) *satisfies* (CD) via the trichotomy — weak evidence
that (b″) may be TRUE.

## Consequences

1. The corrected metatheorem `CoreVCs → JoinPeelVCs → reachable →
   RA-lin` (A9) has **no VC-free or lattice-only discharge** of its
   per-CRDT hypothesis: not the paper's 24 VCs (A8's forcing analysis),
   not the semilattice laws (this finding). The per-CRDT obligation is
   real.
2. The demarcation line runs through **update-inflationarity** — i.e.
   through the very definition of a state-based CRDT (Shapiro et al.'s
   monotonic semilattice object), not through the merge algebra alone.
   A signature can have a perfect lattice merge and still not be a
   CRDT in the behavioral sense the metatheorem needs.
3. Candidate final form of the metatheorem: `CoreVCs + ACI + inflation
   + (CD) → RA-lin`, with (CD) the sharpened residual — either
   derivable (resolving (b″) positively, making the extra VCs
   per-CRDT-trivial: ACI + inflation hold definitionally for every
   real state-based RDT, and (CD) reduces to a trichotomy-style set
   lemma) or refutable by a model whose update-delta in context
   escapes its causal past (none found; the `lem_0op` forcing kills
   the natural candidates).

## Artifacts

| File | Content | `sorry` |
|---|---|---|
| `Sal/CRDTs/Metatheory/Assoc_CounterModel.lean` | `AWSetF`; `LatticeVCs`; `AWSetF_coreVCs`; `AWSetF_latticeVCs`; `AWSetF_not_joinPeelVCs`; `AWSetF_not_joinLemma`; `AWSetF_update_not_inflationary`; `coreVCs_lattice_insufficient` | 0 |
| `Sal/CRDTs/Metatheory/Assoc_CounterModel_Reachable.lean` | 5-step execution `initConfig → flagC5`; `flagC5_reachable`; `flagC5_not_ra_linearizable`; `ra_linearizability_fails_for_lattice_CRDTs` | 0 |

Both files build with `lake lean` on the pinned toolchain (Lean
v4.28.0). Axiom audit (`#print axioms`):
`coreVCs_lattice_insufficient`,
`ra_linearizability_fails_for_lattice_CRDTs`, `AWSetF_coreVCs`,
`AWSetF_update_not_inflationary` each depend only on
`[propext, Classical.choice, Quot.sound]` — in particular NOT on
`sorryAx` (the two legacy `sorry`s in the superseded
`Merge_Linearization.lean`, which sits in the import chain, are not
touched).

The (b″) reduction skeleton (§ above) is paper-level only —
deliberately not mechanized in this pass: with (b′) refuted, the
research-critical artifact was the counter-model, and the skeleton's
value is to pin (CD) as the precise open residual. Next mechanization
targets, in order: (i) `LatticeVCs⁺ := LatticeVCs + update_inflation`
and the derived monotonicity lemma (5 lines from `lem_0op`); (ii) the
downset `↓e` infrastructure and the `M/P` induction with (CD) as its
sole `sorry`/hypothesis; (iii) discharge (CD) for `AWSet` from the
A7 trichotomy (should be a re-packaging of
`awAdds_killed_of_rem_max`).
