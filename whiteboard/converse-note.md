# The restricted converse of adequacy (task #114, phase 2)

## What this note settles

Adequacy of the flat conditioned-MRDT metatheory is the implication

    VC1 and ... and VC8   ==>   RA-linearizable.

The VC-minimality sweep (`whiteboard/vc-minimality-note.md`) settled the
*irredundancy* half: the eight conditions are a four-law core
{VC5-at-empty, VC6, VC7, VC8} plus a shell (VC1, VC2, VC3, VC4) that is stated
more strongly than adequacy needs. This note attacks the *converse*.

The full converse (RA-lin implies all eight VCs) is already refuted: the shell
VCs each have an RA-linearizable violator (spurious rc order for VC1, a chain
along a total order for VC2, and lift or symmetry failures at unreachable
states for VC3 and VC4). Those violators live off the reachable-canonical
domain, which is exactly why they cannot be certified by RA-lin. The open,
real completeness statement is the RESTRICTED converse, over the four core
laws and their reachable states only.

**Headline.** H-converse is VALIDATED. Every canonical RA-linearizable flat
MRDT satisfies VC5-at-empty, VC6, VC7, and VC8 on its reachable states. The
derivation is clean and short. Three of the four core laws (VC5-empty, VC6,
VC7) reduce on reachable canonical tuples to instances of the Join Lemma
(`mergeL(sig(E1 & E2), sig(E1), sig(E2)) = sig(E1 u E2)`), so they follow from
the *existence* half of canonical-RA-lin (the merge lands on the canonical
state of the union). VC8 needs one Join instance plus one further fact,
`sig(U) = e(sig(U-e))` for `loOn(U)`-maximal `e`, and that fact is forced by
the *convergence* half of canonical-RA-lin alone, independent of the merge.
So VC8 is the only core law whose derivation consumes convergence, and its
extra-over-the-Join content is exactly that convergence fact. The converse
therefore reduces to: canonical-RA-lin (existence plus convergence) forces the
four core laws, the Join giving three and the Join plus the fold-peel giving
the fourth.

Method (per project discipline): goal and falsifiable hypothesis first, then a
stdlib Python harness (`whiteboard/litmus/converse_check.py`) that reuses the
phase-1 loOn-fold oracle and the phase-1b synthesis enumerator unchanged. Every
verdict is hand-derived here and cross-checked against the harness; the harness
never supplies an expected value for the object it judges. No Lean this phase.

## Goal and the falsifiable hypothesis

* **H-converse.** Every canonical flat MRDT that is RA-linearizable satisfies
  VC5-at-empty, VC6, VC7, VC8 on its reachable states.

* **Refutation shape.** A canonical RA-linearizable datatype that reddens a
  core VC on a REACHABLE state / a canonical LCA triple. Such a hit would BOUND
  the framework: an RA-linearizable datatype the VC set cannot certify, a
  genuine negative result. It is spelled out as (datatype, reachable history,
  the triple, the violated VC, expected versus got).

* **Validation shape.** A clean sweep over the synthesis space, calibrated so
  it can both detect a core-VC violation and reject a non-RA-linearizable
  datatype, PINS H-converse for Lean and licenses the pen-and-paper derivation.

A violation on an unreachable or non-canonical input does NOT refute the
restricted converse. This domain discipline is what the whole exercise turns on.

## The definitional setup: canonical RA-linearizability

Fix a conditioned MRDT `<Sigma, sigma0, do, mergeL, rc>`. Write `comm(a,b)` for
`forall s, do(do(s,a),b) = do(do(s,b),a)`; `visNC(a,b)` for `vis a b and not
comm a b`; `down(e)` for the visNC-backward closure of `{e}`; a set `U` is
*weakly closed* when `visNC a b` and `b in U` force `a in U`. The linearization
order is

    loOn(ev, x, y)  :=  (vis x y and not comm x y)
                     or (x, y concurrent, rc x y = Fst,
                         and no e3 in ev with vis y e3 and not comm y e3).

`sig(ev)` is the fold from `init` of any `loOn(ev)`-respecting enumeration; it
is well defined exactly when the datatype converges on `ev` (all such folds
agree). Following `whiteboard/ra-lin-definition-note.md`, a datatype is
**canonical RA-linearizable** when, on every reachable weakly-closed event set:

1. **existence + convergence:** exactly one `loOn`-respecting fold exists, so
   `sig(.)` is a well-defined function (a cyclic `loOn` has none, a
   non-convergent set has several; both are excluded); and

2. **the merge is that fold (the Join):** for every mergeable pair of
   weakly-closed sets `E1, E2`,

       mergeL(sig(E1 & E2), sig(E1), sig(E2))  =  sig(E1 u E2).

The Join is the operational content: a merge version's state is the canonical
state of its event set. An apply version's state is automatically a fold. So
canonical-RA-lin is precisely convergence-everywhere plus Join-everywhere.

## The four core laws (restated)

* **VC5-empty** (`VC5°`, the nullary unit): `mergeL(init, init, init) = init`.
* **VC6** (feasible local-redistribute). Weakly-closed `E1, E2`, `e in E1`,
  `e not in E2`, `e` `loOn(E1 u E2)`-maximal; `s0 = sig(E1 & E2)`,
  `B = sig(down(e)-e)`, `t1 = sig(E1-e)`, `s2 = sig(E2)`, `u = e(B)`:

      mergeL(s0, mergeL(B, t1, u), s2) = mergeL(B, mergeL(s0, t1, s2), u).

* **VC7** (feasible redistribute). Same, but `e in E1` and `e in E2`;
  `t0 = sig((E1 & E2)-e)`, `t1 = sig(E1-e)`, `t2 = sig(E2-e)`, `u = e(B)`:

      mergeL(mergeL(B,t0,u), mergeL(B,t1,u), mergeL(B,t2,u))
          = mergeL(B, mergeL(t0,t1,t2), u).

* **VC8** (CDVC3, the causal-delta equation). Weakly-closed `U`, `e in U`
  `loOn(U)`-maximal, `A = sig(U-e)`, `B = sig(down(e)-e)`:

      mergeL(B, A, e(B)) = e(A).

## The domain analysis (each core VC, stated versus reachable-canonical)

A candidate violation only counts if it lands on a reachable-canonical input.
So the stated domain of each core VC must be compared to the reachable-canonical
domain, which is: direct arguments that are `sig`-folds of reachable
weakly-closed sets, or `do`-applications of them, and LCA triples of the shape
`(sig(E1 & E2), sig(E1), sig(E2))` for reachable weakly-closed `E1, E2`.

* **VC5-empty.** Stated domain is the single triple `(init, init, init)`. Since
  `init = sig(empty)` and the empty set is reachable and weakly closed (two
  fresh replicas merging), that triple IS the canonical LCA triple at
  `E1 = E2 = empty`. Stated domain equals reachable-canonical, no surplus.

* **VC5 in full (feasible_init).** The Lean `feasible_init` ranges over
  arbitrary `ev`, INCLUDING non-weakly-closed sets, and asks
  `mergeL(init, init, s) = s` for `s` a fold of `ev`. A fold of a
  non-causally-closed `ev` is not any version's state, so it is NOT a reachable
  canonical state. This surplus is outside the converse, and RA-linearizability
  does NOT force VC5 there. The hunt makes this concrete: on the S3 space it
  surfaces canonical-RA-lin specs whose `feasible_init` reddens on a
  non-weakly-closed `ev` (a fold of a non-closed set with `mergeL(init,init,s)
  != s`), and every one is excluded once the domain is restricted to
  weakly-closed `ev`. On the reachable-canonical domain (weakly-closed `ev`,
  where the state is a genuine version state), VC5 is the Join at `(empty, ev)`
  and holds. This is the operational form of the phase-1
  "stated-stronger-than-consumed" reading of `feasible_init`, and it is exactly
  the domain discipline the converse demands: a VC5 red on a non-closed `ev` is
  a red on a non-reachable state, not a converse counterexample.

* **VC6, VC7.** Stated over weakly-closed `E1, E2`, so the outer merge's LCA
  slot and outer branches are reachable-canonical. The one subtlety is the
  NESTED merge in a branch (`mergeL(B, t1, u)` for VC6). That inner value is a
  reachable-canonical state precisely WHEN the datatype is RA-linearizable
  (Section below shows it equals `sig(E1)` via the Join). On the reachable
  domain of the converse (RA-lin holds), every nested slot is canonical, so the
  whole tuple is reachable-canonical. For a non-RA-lin datatype the nested slot
  can be non-canonical, but such a datatype is not a converse candidate.

* **VC8.** Stated over weakly-closed `U` and `loOn(U)`-maximal `e`; every
  entry (`B`, `A`, `e(B)`, `e(A)`) is a `sig`-fold or a `do`-application of one,
  so the stated domain is reachable-canonical, no surplus.

**The core/shell split lines up with the reachable-canonical/universe split.**
The four SHELL VCs quantify over the whole op or state universe (VC1, VC2 over
event pools; VC3, VC4 over all states), far beyond reachable-canonical, which is
why the full converse fails for them: their unreachable surplus has
RA-linearizable violators. The four CORE VCs are config-driven, stated on
reachable weakly-closed sets and their canonical states, so their stated domain
is (up to the closed-versus-arbitrary `ev` surplus of VC5) the
reachable-canonical domain. The restricted converse is well posed for exactly
the core, and this is the mirror of the phase-1 shrink.

## Calibration (mandatory)

The harness confirms it can both DETECT a core-VC violation and REJECT a
non-RA-linearizable datatype. The four phase-1 separators each redden a core VC
on a reachable state, yet each is non-RA-linearizable, so none is a converse
counterexample; the oracle must reject all four. Two boundary datatypes pin the
positive side.

| datatype | oracle | core VC red (reachable) | converse counterexample? |
|----------|--------|-------------------------|---------------------------|
| ORSet (add-wins set)         | RA-lin | none    | no (positive anchor) |
| MVR (all-commuting)          | RA-lin | none    | no (positive anchor) |
| pure-or G-set (control)      | RA-lin | none    | no |
| delta counter mod 2 (a^b^l)  | RA-lin | none    | no |
| poisoned-empty G-set         | NOT RA-lin | VC5 at `ev = empty` | no (fails the Join at `(empty,empty)`) |
| change-wins flag             | NOT RA-lin | VC6 at the `(2,2)` countermodel | no (fails the Join) |
| double-counting counter      | NOT RA-lin | VC7 at `E1 = E2 = {e}` | no (fails the Join) |
| AWSetF3 (#57 separator)      | NOT RA-lin | VC8 at a maximal `rem`  | no (fails the Join) |

All eight verdicts match the hand-derivation with zero mismatches. Detection
and rejection both fire, so a null result in the hunt is meaningful.

## The hunt result

The hunt scans the phase-1b synthesis spaces (`space_s2x2`, `space_s2x3`, and
under `--full` also `space_s3`), deduplicates by signature, and for each spec
samples honest DAGs. For each config it computes the canonical-RA-lin oracle
verdict and the four core-VC verdicts on reachable-canonical inputs (VC6, VC7,
VC8, and VC5 restricted to weakly-closed `ev`), and records four things: (1) any
spec RA-linearizable across all sampled configs that nonetheless reddens a core
VC (a GLOBAL converse counterexample); (2) any single config where the oracle
passes yet a core VC reddens (a PER-CONFIG implication violation, the sharper
and sampling-insensitive test, since both predicates are exact on one fixed
config); (3) any convergent config where the VC8 causal clause
`sig(U) = e(sig(U-e))` fails; and (4), as a domain diagnostic, any RA-lin spec
with a VC5 violation on a NON-weakly-closed `ev` (the `feasible_init` surplus,
outside the converse domain, not a counterexample).

| space | visited | unique | canon-RA-lin | convergent | counterex. | per-config | causal | VC5-surplus |
|-------|--------:|-------:|-------------:|-----------:|-----------:|-----------:|-------:|------------:|
| S2x2 | 1408 | 832 | 106 | 704 | 0 | 0 | 0 | 0 |
| S2x3 | 6016 | 1792 | 146 | 1408 | 0 | 0 | 0 | 0 |
| S3   | 7600 | 5782 | 443 | 3968 | 0 | 0 | 0 | 8 |

Search bound: **15024 specs visited (8406 unique), of which 695 are canonical
RA-linearizable**, and ZERO counterexamples, ZERO per-config implication
violations, ZERO VC8 causal-clause violations. The per-config implication
`oracle-passes-on-C ==> core-VCs-green-on-C` (on the reachable-canonical domain)
held on every sampled config of every spec, which is the empirical form of the
per-config derivation below.

The eight VC5-surplus hits in S3 are the domain analysis in action, not
counterexamples. Each is a canonical-RA-lin spec whose `feasible_init` reddens
on a NON-weakly-closed `ev` (a `k=3` datatype whose `do` maps into an
unreachable state `2`, so a fold of a non-closed `ev` yields `s = 2` with
`mergeL(init, init, 2) != 2`). Since `s` is a fold of a non-causally-closed set,
it is not a reachable state, so the red does not refute the restricted converse.
Restricting VC5 to weakly-closed `ev` (the reachable-canonical domain), all
eight vanish and the sweep is clean. This is the concrete demonstration that
"every candidate violation must be checked for reachable-canonicity": here eight
candidates were checked and eight were off-domain. It also shows the searcher
CAN detect a VC5 red for an RA-lin datatype (the detection side is live), so the
zero on the reachable-canonical domain is meaningful.

## The derivation (H-converse validated)

Assume the datatype is canonical RA-linearizable. All merge and `sig` values
below are on reachable weakly-closed sets, so they are well defined and the Join
applies to every mergeable pair of them. Six structural facts, all standard:

* **(L1)** unions and intersections of weakly-closed sets are weakly closed.
* **(L2)** removing a `loOn(U)`-maximal `e` from a weakly-closed `U` keeps it
  weakly closed (the only worry is a `visNC`-predecessor edge `e -> b`, but
  `loOn`-maximality of `e` forbids a `visNC`-successor, and the vis arm of
  `loOn` is set-independent).
* **(L3)** if `e in E` and `E` is weakly closed then `down(e) subseteq E`; and
  `e` is `loOn(down(e))`-maximal.
* **(L4) antitonicity of loOn.** For weakly-closed `E' subseteq E`,
  `loOn(E)` restricted to `E'` is contained in `loOn(E')`. The vis arm is
  set-independent; the rc arm carries an absorber `not exists e3 in ev ...`
  whose candidate pool shrinks with the set, so the arm is easier to satisfy on
  the smaller `E'`. Growing the set only removes edges.
* **(L5) the fold-peel lemma.** For weakly-closed `U`, `e` `loOn(U)`-maximal,
  with the datatype convergent on `U` and on `U-e`:

      sig(U) = e(sig(U-e)).

  Proof: take a `loOn(U-e)`-respecting enumeration `p0` of `U-e`; by (L4) it is
  `loOn(U)`-respecting on `U-e`; `e` is `loOn(U)`-maximal, so `p0 ++ [e]` is a
  `loOn(U)`-respecting enumeration of `U`; convergence on `U` makes its fold
  `sig(U)`, and that fold is `e(fold(p0)) = e(sig(U-e))`. This uses convergence
  as an equation, not merely for well-definedness, and it needs no merge.
* **(L6)** `e(B) = e(sig(down(e)-e)) = sig(down(e))`, by (L5) at `U := down(e)`.

Each core law is now the Join rewritten on its merge nodes. Every auxiliary set
below is a weakly-closed subset of the same configuration (via L1, L2, L3), so
the Join applies to it under the RA-lin hypothesis.

**VC5-empty (and the full unit).** `mergeL(init, init, init) =
mergeL(sig(empty), sig(empty), sig(empty)) = sig(empty u empty) = sig(empty) =
init`, the Join at `(empty, empty)`. The full `feasible_init` on a reachable
canonical `s = sig(E)` is likewise the Join at `(empty, E)`:
`mergeL(init, init, s) = mergeL(sig(empty & E), sig(empty), sig(E)) = sig(E)`.
**Forced by the Join alone.**

**VC6.** Rewrite the three merge nodes:

* inner-left `mergeL(B, t1, u) = mergeL(sig(down(e)-e), sig(E1-e), sig(down(e)))`
  is the Join at `(E1-e, down(e))`: their intersection is `down(e)-e` (by L3
  `down(e) subseteq E1`, and `e not in E1-e`), their union is `E1`. So it equals
  `sig(E1)`.
* LHS `= mergeL(s0, sig(E1), s2) = mergeL(sig(E1 & E2), sig(E1), sig(E2)) =
  sig(E1 u E2)`, the Join at `(E1, E2)`.
* inner-right `mergeL(s0, t1, s2) = mergeL(sig(E1 & E2), sig(E1-e), sig(E2))` is
  the Join at `(E1-e, E2)`: intersection `(E1 & E2) - e = E1 & E2` (as
  `e not in E2`), union `(E1 u E2) - e`. So it equals `sig((E1 u E2)-e)`.
* RHS `= mergeL(B, sig((E1 u E2)-e), u) = mergeL(sig(down(e)-e),
  sig((E1 u E2)-e), sig(down(e)))` is the Join at `((E1 u E2)-e, down(e))`:
  intersection `down(e)-e`, union `E1 u E2`. So it equals `sig(E1 u E2)`.

Both sides equal `sig(E1 u E2)`. **Forced by the Join alone** (four instances).

**VC7.** The same rewriting with `e` shared:
`mergeL(B, t0, u) = sig(E1 & E2)` (Join at `((E1 & E2)-e, down(e))`, using
`down(e) subseteq E1 & E2`), `mergeL(B, t1, u) = sig(E1)`,
`mergeL(B, t2, u) = sig(E2)`, so LHS `= mergeL(sig(E1&E2), sig(E1), sig(E2)) =
sig(E1 u E2)`. And `mergeL(t0, t1, t2) = sig((E1 u E2)-e)` (Join at
`(E1-e, E2-e)`), so RHS `= mergeL(B, sig((E1 u E2)-e), u) = sig(E1 u E2)`.
**Forced by the Join alone** (five distinct instances).

**VC8.** The LHS `mergeL(B, A, e(B)) = mergeL(sig(down(e)-e), sig(U-e),
sig(down(e)))` is the Join at `(U-e, down(e))`: intersection `down(e)-e`, union
`U`. So LHS `= sig(U)`. The RHS `e(A) = e(sig(U-e)) = sig(U)` by the fold-peel
(L5). Both sides equal `sig(U)`. **Forced by the Join at `(U-e, down(e))`
together with convergence (the fold-peel).**

### Which of the four are forced by what, and where reachability enters

| core VC | forced by | Join instances | convergence used |
|---------|-----------|----------------|------------------|
| VC5-empty | the Join (existence) | 1 | only for `sig(empty)` well defined |
| VC6 | the Join (existence) | 4 | only for the `sig`s well defined |
| VC7 | the Join (existence) | 5 | only for the `sig`s well defined |
| VC8 | the Join AND convergence | 1 | crucially, via the fold-peel L5 |

VC5-empty, VC6, VC7 are pure Join reductions: each merge node is rewritten as
"the merge produces the canonical state of the union," and the two sides
collapse to `sig(E1 u E2)` (or `sig(E)`, or `init`). VC8 additionally invokes
the fold-peel identity `sig(U) = e(sig(U-e))`, whose proof consumes convergence
as an equation. So VC8 is the unique core law that reaches past the Join, and
what it reaches for is convergence. Reachability is used throughout to license
the Join at each auxiliary pair (every auxiliary set is a reachable
weakly-closed subset of the same configuration) and to license convergence at
`U` and `U-e`; on arbitrary (unreachable) states the merge nodes need not be
Join instances and the derivation breaks, which is why the converse is
genuinely restricted.

## The VC8-specific finding

The prior expectation was that VC8, being "more than merge produces
`sig(union)`," might carry content the converse cannot recover. It carries more,
and the harness confirms it: the extra is precisely the causal clause
`sig(U) = e(sig(U-e))` for `loOn(U)`-maximal `e`, the causal-order half of the
delta equation. But that clause is forced by convergence alone, independent of
the merge (L5), and the harness finds ZERO violations of it across every
convergent spec in every sampled config. VC8 therefore decomposes as

    VC8  =  [ Join at (U-e, down(e)) ]  and  [ sig(U) = e(sig(U-e)) ],

a merge half and a convergence half. The merge half fails exactly when the Join
fails (AWSetF3 is the witness, and it is non-RA-lin for that reason); the
convergence half never fails on a convergent datatype. Both halves are supplied
by canonical-RA-lin. So VC8 carries no content beyond canonical-RA-lin: it is
forced, just through both halves rather than the Join alone.

AWSetF3 pins the split concretely. It is convergent on every reachable set, so
its causal half `sig(U) = e(sig(U-e))` holds everywhere (the harness finds zero
causal-clause failures for it). Over sixty sampled honest DAGs its Join fails on
twenty-six configs, and its VC8 fails on exactly those same twenty-six. The
delta equation of AWSetF3 breaks through the merge half alone: the union merge
carries a `flag = true` from an add branch that the maximal `rem` should have
deflated, so `mergeL(B, A, rem(B))` overshoots `sig(U)`, while
`sig(U) = rem(sig(U-rem))` holds untouched. This is why AWSetF3 is a VC8
separator for adequacy (phase 1) yet not a converse counterexample: it is
non-RA-linearizable, its Join being the very thing that fails.

## Phase-3 Lean shapes

The derivation is Lean-shaped. The reachable-canonical layer is the existing
`sig` / `JoinLemma3` / `IsRALinearizable3` machinery; the converse adds no new
merge reasoning, only structural set lemmas and the fold-peel.

* `wc_union`, `wc_inter`, `wc_remove_maximal` (L1, L2): weak closure is
  preserved by union, intersection, and removing a `loOn`-maximal event.
* `down_subset_of_mem` and `mem_maximal_of_down` (L3).
* `loOn_antitone` (L4): already present as `loOn_mono` in
  `Merge_Linearization_Set.lean`; used the reachability-safe direction (edges
  only vanish as the set grows).
* `sig_peel_maximal` (L5): `Converges U -> Converges (U \ {e}) ->
  IsMaximal (loOn U) e -> sig U = do (sig (U \ {e})) e`. The one genuinely new
  lemma; its proof is the enumeration argument above (extend a respecting
  enumeration of `U-e` by `e`, use antitonicity and convergence).
* `converse_VC5_empty : IsRALinearizable3 D -> mergeL init init init = init`,
  the Join at `(empty, empty)`.
* `converse_VC6`, `converse_VC7`: from `JoinLemma3` at the four and five
  auxiliary pairs; the proof is the merge-node rewriting above, no new lemmas.
* `converse_VC8`: from `JoinLemma3` at `(U-e, down(e))` and `sig_peel_maximal`.
* `converse_core : IsRALinearizable3 D -> ReachableCoreVCs D`, packaging the
  four, reduces the restricted converse to two ingredients: `JoinLemma3` (all
  four consume it) and `sig_peel_maximal` (only VC8 consumes it).

**The completeness corollary.** Adequacy (`{VC1..VC8} -> RA-lin`, via
`JoinLemma3`) and this restricted converse (`RA-lin -> {VC5°, VC6, VC7, VC8}` on
reachable states) make the four core laws on reachable states and canonical-RA-
linearizability INTER-DERIVABLE, modulo the update layer's acyclicity and
convergence-on-reachable content (where the demoted shell VCs live). The two
task-#114 directions meet at the same four-law core: phase 1 shrank adequacy's
contract to it, phase 2 shows RA-lin recovers exactly it on reachable states.

## What is anchored and what is pen-and-paper

Anchored (machine-checked, PASS+FAIL, hand-derived expectations): the
calibration (four separators rejected by the oracle and detected by the
checkers, two anchors accepted clean); the clean sweep over 15024 synthesized
specs (8406 unique, 695 canonical-RA-lin) with zero counterexamples, zero
per-config implication violations, and zero VC8 causal-clause violations; the
domain diagnostic (eight VC5-surplus hits on non-weakly-closed `ev`, all off the
reachable-canonical domain and excluded by the weak-closure restriction); and,
as its own probe, the fold-peel identity holding on every convergent spec.

Pen-and-paper: the derivation of Section "The derivation," in particular the
fold-peel lemma L5 and the identification of each core VC's merge nodes as Join
instances. The bounded search is evidence for the general claim at the stated
bounds, never proof; the Lean shapes above are the phase-3 obligation that
turns the evidence into a theorem.
