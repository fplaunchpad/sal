# The simultaneous convergence∧faithfulness induction (update layer)

*2026-07-04. The architecture the three factored attempts proved is needed. Design-first, so the
mechanization transcribes a worked structure instead of relocating the same wall.*

## Why factoring failed (the established finding)

Three attempts (`RGA_ReachDischarge` rebundle; `RGA_GenDischarge` `accurate`-too-strong;
`RGA_GenDischarge2` `EligibleThread`) each tried to prove **Faithful-at-every-eligible-prefix** as a
*standalone* lemma, then feed it to the convergence engine. Each reduced to the same obstruction:

> To seat the dependency-prefix accuracy base at an *arbitrary* eligible prefix `pre`, you must
> reorder `pre` to `deps-first ++ concurrents` **up to `eq`** — and that reorder-invariance **is
> convergence**.

So Faithful and convergence are mutually dependent: the swap step of convergence needs Faithful; and
Faithful at an interleaved prefix needs convergence to relate it to the dependency-first fold. They
must be proved **together**, by one induction.

## The combined statement

Induct on `n = |E|` over backward-closed reachable event sets `E` (finite). Prove the conjunction
`P(E)`:

- **(Conv E):** for all `loOnA`-respecting `listPermOf` enumerations `π₁ π₂` of `E`,
  `applySeqR init_st π₁ ≈ applySeqR init_st π₂`.
- **(Faith E):** for every `o ∈ E` and every `loOnA`-respecting enumeration `π` of `E` with `o` last
  (`π = ρ ++ [o]`, `ρ` an enumeration of `E \ {o}`), `Faithful o (applySeqR init_st ρ)`.

`(Faith E)` is stated with `o` **last**, not at an arbitrary prefix — that is the key economy. An
arbitrary eligible prefix is reached *through* `(Conv)`, not by a separate quantifier. This is
exactly what the factored attempts lacked: they quantified Faithful over all prefixes and then needed
convergence to move between them; here convergence is in the same induction, so "`o` last" suffices.

## The induction

**Base** `|E| ≤ 1`: `(Conv)` trivial (≤1 enumeration up to the empty case); `(Faith)`: the single
event is applied to `init_st`, Faithful by `chainFaithful_init` / its own accuracy at `init_st`
(dependency prefix is empty, so `GenDisc2`'s base seats directly — `accurate o init_st`).

**Step** `|E| = n+1`. Pick a `loOnA`-**maximal** `m ∈ E` (exists, finite strict order; `m` has no
`loOnA`-successor in `E`). Let `E' = E \ {m}`. `E'` is backward-closed (removing a maximal element
removes no one's dependency) and reachable. IH gives `(Conv E')` and `(Faith E')`.

**(Faith E):** take `o ∈ E`, enumeration `ρ ++ [o]`.
- If `o = m`: `ρ` is an enumeration of `E'`. Need `Faithful m (applySeqR init_st ρ)`. `m`'s
  dependency prefix `d ⊆ ρ` (all `m`'s `loOnA`-predecessors precede it, and they are all of `E'` that
  are below `m`). By `GenDisc2`, `accurate m (applySeqR init_st d)`. `ρ` is a `loOnA`-respecting
  enumeration of `E'`; by **(Conv E')**, `applySeqR init_st ρ ≈ applySeqR init_st (d ++ c)` where `c`
  = `ρ` restricted to `m`-concurrent events (a `loOnA`-respecting reorder of `ρ` to deps-first —
  legitimate because `E'` events not below `m` are all `m`-incomparable, `m` being maximal so none is
  above `m`). Then thread `Faithful m` from `d` across `c` by the order layer
  (`chainFaithful_at_depPre` base + `chainFaithful_depPre_concTail`, whose `Del`-of-`target m` case is
  `goodStep_del_target`), and transport across `≈` by `Faithful`'s `eq`-congruence. **This is the step
  the factored attempts could not take — here (Conv E') supplies the reorder-invariance.**
- If `o ≠ m`: then `m ∈ ρ`. Reduce to `(Faith E')` for `o` plus the effect of the extra `m`. Since
  `m` is maximal and `o`-concurrent-or-below, and `o` is last, `m` sits in `ρ`; `Faithful o` at `ρ`
  follows from `Faithful o` at `ρ \ {m}` (IH, `(Faith E')`) threaded across the single `m`-step
  (an incomparable or dependency `Ins`/`Del` — order-layer step lemma), again transported via
  `(Conv E')` to align the prefixes.

**(Conv E):** take enumerations `π₁ π₂` of `E`. Reorder each to put `m` last: `π_i ≈ ρ_i ++ [m]`
via adjacent swaps of `m` past its `loOnA`-incomparable successors, each swap justified by the
**faithful swap** (`eqSwap_of_bothFaithful`) — whose two Faithful obligations are `(Faith E)` (just
proved for this `E`, both operands last-able because `m` is maximal and the other is concurrent).
Then `ρ₁, ρ₂` are enumerations of `E'`; `applySeqR init_st ρ₁ ≈ applySeqR init_st ρ₂` by **(Conv E')**;
applying the final `m` preserves `≈` by `do_`'s `eq`-congruence. Hence `π₁ ≈ π₂`.

Note the internal ordering: within the step, prove **(Faith E) first** (it uses only `(Conv E')`,
`(Faith E')`, `GenDisc2`, order layer), then **(Conv E)** (it uses `(Faith E)` + `(Conv E')`). No
circularity: both consume only the IH at `E'` plus the just-proved `(Faith E)`.

## What it rests on (all already kernel-clean)

- `eqSwap_of_bothFaithful` — the faithful swap (both operands merely Faithful).
- `chainFaithful_at_depPre`, `chainFaithful_depPre_concTail`, `goodStep_del_target`,
  `faithful_ins_depPre_concTail` — the depPre→concTail thread incl. target-deletion (RGA_GenDischarge2).
- `chainFaithful_incompFold`, `climbFaithful_of_chain`, `chainFaithful_doDel_faithful` — step lemmas.
- `do_`/`applySeqR` `eq`-congruence (`do_eq_congr`, `applySeqR_eq_congr`).
- `GenDisc2` — the satisfiable dependency-prefix accuracy (the per-event input; the honest residual
  hypothesis defining a real RGA execution's event set).

The only genuinely new mechanization is the **induction skeleton** (`P(E)` by strong induction on
`|E|`, maximal-element peel, the two internal steps). Every step case is an existing lemma. This is
the piece to build — as ONE simultaneous induction, not two factored lemmas.

## Residuals after this closes

- `ReachInv` (`wf ∧ id_mono ∧ contains 0=false` along the fold): routine `do_`-invariant preservation
  (`RgaInv_do*`, `id_mono_do*`); fold it into `P(E)` as a third conjunct or discharge separately.
- `NoFreshClash` for concurrent pairs: from `GenDisc2` freshness (recList entries older than a fresh
  concurrent id) — already isolated.
- Merge side `hBN`: the cross-forest anchor identity — independent of this induction (genuinely new
  two-sided content); handled separately.
- Generic `≈`-quotient (M5) + `app`-conditioning: separate, on the generic template.

## Output target

`RGA_update_convergence_final`: for a backward-closed reachable `E` with `GenDisc2 E` (+ `ReachInv E`
if not folded in), any two `loOnA`-respecting enumerations fold to `≈`-equal states — via `P(E)`, with
**no** `EligibleThread`/`hReach`/per-prefix-Faithful residual. `GenDisc2` is the honest irreducible
"E is a real RGA execution" hypothesis; everything per-prefix is derived.
