# The VC minimality sweep (task #114, phases 1 and 1b)

## What this note settles

Adequacy of the flat conditioned-MRDT metatheory says: the eight verification
conditions imply RA-linearizability,

    VC1 and ... and VC8   ==>   RA-lin.

This note attacks the *irredundancy* half. For each verification condition we
ask whether it is load-bearing (dropping it breaks adequacy) or removable
(the others already give it, so the set shrinks). Task #57 settled VC8 (the
causal-delta equation CDVC3) as load-bearing, with the AWSetF3 separator. This
sweep does VC1 through VC7, and the result is not the expected "all eight are
irredundant."

**Headline (corrected in phase 1b).** The flat set is not irredundant as
stated, but the independent core is *larger* than phase 1's "dual pair"
reading. Four conditions carry irreplaceable adequacy content:

* **VC7 (redistribute)** and **VC8 (the causal-delta equation)**, the matched
  delta pair (phase 1, reconfirmed);
* **VC6 (feasible local-redistribute)**, witnessed independent in phase 1b by
  the **change-wins flag** (a real datatype design, not a mutation);
* **VC5 restricted to the empty event set** (the nullary unit
  `mergeL init init init = init`), witnessed independent by the
  **poisoned-empty-merge G-set**; VC5 on nonempty canonical states is
  derivable from {VC3/convergence, VC4, VC6, VC8}.

The other four split as phase 1 found: **VC1, VC2, VC4** are stated stronger
than adequacy requires (each has an RA-linearizable violator), and phase 1b
moves **VC3** into the same class (an RA-linearizable sentinel violator, no
reachable isolating witness up to the stated search bounds). The irreducible
core for adequacy is the four laws {VC5-at-empty, VC6, VC7, VC8} together
with the acyclicity and convergence content of the update layer, not the
update layer as literally stated. Phase 1's two-law headline was an artifact
of its method: mutating boundary datatypes cannot reach a *design* (the
change-wins flag) or a *corner* (the all-init merge) whose violation is
structurally entangled with the mutated component. Phase 1b replaces mutation
by synthesis over tiny tabulated specs and finds both inside an exhaustive
two-state space.

Method note (per the project discipline): goals and falsifiable hypotheses are
stated first, then a stdlib Python harness
(`whiteboard/litmus/vc_minimality_check.py`) that decides the eight VCs and a
loOn-fold RA-linearizability checker over honest three-way-merge DAGs. Every
verdict below is hand-derived and cross-checked against the harness; the harness
never supplies an expected value for the object it is judging. No Lean this
phase.

Phase 1b adds a second harness, `whiteboard/litmus/vc_synthesis_search.py`,
which imports the phase-1 checkers unchanged and *synthesizes* whole spaces
of tiny tabulated specs (finite state set, per-kind `do` tables, symmetric
`mergeL` tables, kind-pair `rc`), scanning for exactly-one-red vectors and
running the RA-lin oracle on the survivors. Its calibration is mandatory and
passes: the searcher re-finds, from scratch inside its exhaustive two-state
space, the VC8 separator (the enable-wins flag, the minimized AWSetF3) and a
VC7 separator (the mod-2 parity counter, the double-counting counter's
two-state shadow). Without that, "found nothing" for a target VC would be
meaningless. Search bounds are recorded per verdict; a bounded "no witness"
is evidence for derivability, never proof.

## Goals and the seven hypotheses

For verification condition `i` in 1..7:

* **H_i (independence).** There is a datatype that satisfies the other seven
  conditions, fails VC_i, and is not RA-linearizable. Such a datatype witnesses
  that VC_i is load-bearing: the reduced bundle `{VC_j : j != i}` no longer
  implies RA-lin.

* If H_i is refuted (no such isolating, non-RA-linearizable witness can be
  built), pursue **H_i' (derivability / weakenability).** Either `{VC_j : j !=
  i}` implies VC_i outright, or VC_i as stated is stronger than adequacy needs
  and can be replaced by a weaker condition that the others supply on reachable
  configurations. Both are shrink results.

An independence witness and a derivability result are different outcomes, both
first class. A failed independence is never relabelled as success, and a
mutation that stays RA-linearizable is never relabelled as a countermodel.

## The eight conditions (stated natively)

Write `Op = (ts, rep, appop)`; `comm(a,b)` for `forall s, do(do(s,a),b) =
do(do(s,b),a)`; `visNC(a,b)` for `vis a b and not comm a b`; `down(e)` for the
`visNC`-backward closure of `{e}`; a set `U` is *weakly closed* when `visNC a b`
and `b in U` force `a in U`. The set-relative order is

    loOn(ev, x, y)  :=  (vis x y and not comm x y)
                     or (x, y concurrent, rc x y = Fst,
                         and no e3 in ev with vis y e3 and not comm y e3).

`sigma(ev)` is the canonical state: the fold, from `init`, of any
`loOn(ev)`-respecting enumeration of `ev` (all such folds agree exactly when the
datatype *converges* on `ev`).

1. **rc-non-comm-directional** (`UpdateVCs.rc_non_comm_directional`, fvc:rcnc).
   For distinct cross-replica `o1, o2`:
   `not comm(o1,o2)  <->  (rc o1 o2 = Fst  or  rc o2 o1 = Fst)`.
2. **no-rc-chain** (`UpdateVCs.no_rc_chain`, fvc:chain). For `o1 != o2`,
   `o2 != o3`: `not (rc o1 o2 = Fst and rc o2 o3 = Fst)`.
3. **cond-comm-lift** (`UpdateVCs.cond_comm_lift`, fvc:condcomm). Distinct
   `e, e', e''`; if `rc e e' = Fst` and `not comm(e', e'')` then
   `e''(fold(e(e'(s)), pi)) = e''(fold(e'(e(s)), pi))` for every `s`, `pi`.
4. **merge symmetry** (`CoreVCs3CD.mergeL_comm`, fvc:sym).
   `mergeL l a b = mergeL l b a` for all states.
5. **feasible unit** (`FeasibleDeltaVCs3.feasible_init`, fvc:unit).
   For canonical `s`: `mergeL init init s = s`.
6. **feasible local-redistribute** (`FeasibleDeltaVCs3.feasible_local_redistribute`,
   fvc:lredist). For weakly-closed `E1, E2`, `e in E1`, `e not in E2`, `e`
   `loOn(E1 u E2)`-maximal, with `s0 = sigma(E1 & E2)`, `B = sigma(down(e)-e)`,
   `t1 = sigma(E1 - e)`, `s2 = sigma(E2)` and `u = e(B)`:
   `mergeL(s0, mergeL(B,t1,u), s2) = mergeL(B, mergeL(s0,t1,s2), u)`.
7. **feasible redistribute** (`FeasibleDeltaVCs3.feasible_redistribute`,
   fvc:redist). Same context with `e in E1` and `e in E2`, with `t0 =
   sigma((E1 & E2)-e)`, `B = sigma(down(e)-e)`, `t1 = sigma(E1-e)`,
   `t2 = sigma(E2-e)`, `u = e(B)`:
   `mergeL(mergeL(B,t0,u), mergeL(B,t1,u), mergeL(B,t2,u)) = mergeL(B, mergeL(t0,t1,t2), u)`.
8. **the causal-delta equation** (`CDVC3`, fvc:cd). For weakly-closed `U`,
   `e in U` `loOn(U)`-maximal, `A = sigma(U-e)`, `B = sigma(down(e)-e)`:
   `mergeL(B, A, e(B)) = e(A)`.

## Method: the loOn-fold RA-linearizability checker

The master theorem is `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3 => JoinLemma3 =>
RA-lin`, and #57 refutes RA-lin exactly by refuting the Join. The harness's
RA-linearizability oracle is therefore the Join lemma checked over honest
`vis`-DAGs: for every mergeable pair of weakly-closed sets `E1, E2`,

    mergeL( sigma(E1 & E2), sigma(E1), sigma(E2) )   must be a canonical state of E1 u E2.

`sigma(.)` is the loOn-fold canonical state. A single violation is a
non-RA-linearizable countermodel: the merged version's operational state is no
linearization-fold of its event set (the version has no witness permutation). Both
argument orientations `(E1,E2)` and `(E2,E1)` are checked, since honest
executions realize each. This reuses the litmus loOn-fold idiom
(`rga_byzantine_check.ra_linearizable`: causal fold, convergence, compare)
adapted to the conditioned three-way merge and the exact-intersection LCA of
`stability_vc_check.World`.

The eight VCs are decided as finite predicates: VC1 through VC4 over a
representative op / state universe (VC1, VC2 range over event pools; VC3 bounds
`pi` to length 2; VC4 over the full state universe), VC5 through VC8 over the
canonical (loOn-fold) tuples of random honest DAGs, exactly as the conditions
quantify. Convergence is tracked separately (a set with two disagreeing
respecting folds is non-convergent, so it has no unique canonical state).

Anchor validation: the boundary datatypes ORSet (LCA-sensitive, add-wins,
non-commuting) and MVR (all-commuting) both return eight greens and RA-lin, as
their Lean discharges require, so the engine agrees with the mechanized ground
truth before any mutation.

## Per-VC findings

Each phase-1 witness is a minimal mutation of a boundary datatype (or the
smallest separator in its family); the phase-1b witnesses (VC3, VC5, VC6
below) are synthesis finds or sentinel constructions, presented the same way.
The satisfaction vector is written `[reds]` with the RA-lin verdict; every
vector is reproduced by the harnesses across seeds 114, 7, 2026 with zero
mismatches against the hand-derived expectation.

### VC1 (rc-non-comm-directional): NOT independent; weakenable.

The condition is a biconditional. Break each direction.

* *Reverse direction* (rc orders a commuting pair). Take the grow-only set
  (add-only, every pair commutes) and set `rc(add 0, add 1) = Fst` spuriously.
  Vector `[VC1]`, **RA-linearizable**, convergent. Because the two ops commute,
  the spurious order changes no fold, so canonical states and the Join are
  untouched. This isolates VC1 with all other seven green, yet the datatype is
  RA-linearizable. H_1 is refuted by this witness.

* *Forward direction* (a non-commuting pair left unordered by rc). Take ORSet
  and set `rc := Either` everywhere. Vector `[VC1, VC6, VC8]`, **not
  RA-linearizable**, non-convergent. Dropping the add-wins arbitration is not
  isolating: it co-breaks CDVC3 (VC8) and feasible local-redistribute (VC6). A
  concurrent `add x / rem x` pair now has no loOn edge, so the two orders
  diverge (live vs dead), the set is non-convergent, and the add-wins union
  merge cannot reproduce the sequential effect of the maximal `rem`, which is
  exactly the CDVC3 failure.

**Reading.** The reverse direction of VC1 is redundant for adequacy: it never
affects folds. The forward direction is not independently witnessable, because
breaking it co-breaks VC8. So VC1 cannot be isolated to a non-RA-linearizable
datatype at all: the isolating mutant is RA-linearizable, the non-RA-linearizable
mutant is not isolating. Derivability sketch below.

### VC2 (no-rc-chain): NOT independent; sufficient-but-not-necessary.

Witness: a last-writer-wins register. State `(ts, val)`; `do` overwrites and
records the writer's timestamp; `mergeL` is max by timestamp (LCA slot dropped);
`rc(e1, e2) = Fst` iff `ts(e1) < ts(e2)`. This is a textbook LWW register whose
natural rc orders every pair by timestamp, so `t1 < t2 < t3` is an rc chain.
Vector `[VC2]`, **RA-linearizable**, convergent. The loOn relation is the
timestamp total order, which is acyclic; the register converges and max-ts merge
reproduces `sigma(union)`, the timestamp-latest write.

`no_rc_chain` is used in the metatheory only to prove loOn-acyclicity. It is a
sufficient condition for acyclicity, not a necessary one: a chain along a total
order induces no cycle. When a chain *does* close into a cycle (`a -> b -> c ->
a`, all Fst), the set has no canonical state and the datatype is not
RA-linearizable, but then CDVC3 also has no maximal `e` and co-fails, so that
variant is again not isolating. H_2 is refuted; VC2 can be weakened from
"no chain" to "loOn is acyclic on reachable event sets."

### VC3 (cond-comm-lift): RESOLVED (1b), NOT independent; weakenable to reachable states.

Phase-1 probe, retained: ORSet with the add-wins arbitration reversed,
`rc(add x, rem x) = Fst`. Vector `[VC3, VC6, VC8]`, **not RA-linearizable**,
not isolating. Phase 1b settles the two halves separately.

*The unconditional surplus is not load-bearing.* Sentinel witness, the exact
mirror of VC4's: states `{0, 1, 2}` with `2` unreachable (init `0`, both ops
fix `{0, 1}` pointwise and map `2` into `{0, 1}`). Ops `P = (0,1,0)`,
`Q = (0,1,1)`; they commute on `{0, 1}` but not at `2`, and `comm` is a
`forall` over the whole universe, so `not comm(P,Q)` holds and VC1 *forces*
`rc(P,Q) = Fst`. `mergeL = max(a,b)`. Vector `[VC3]`, **RA-linearizable**,
convergent: VC3 fails at `s = 2` with `pi = []` (`P(Q(2)) = 1` vs
`Q(P(2)) = 0`, and `e'' = P` preserves the difference), while the reachable
world is constantly `0` and every config-level condition is green. VC3's
quantifier ranges over the whole state universe; the content beyond reachable
states is invisible to adequacy. H_3 is refuted; same weakenability class as
VC4.

*No reachable isolating witness up to the search bounds.* The synthesis scan
finds no `[VC3]`-only spec at all: exhaustively at two states with two kinds
(1408 specs) and three kinds (6016 specs), and in the guided three-state
space (7600 specs). The co-breakage mechanism, hand-derived at the smallest
VC3-reddening skeleton: a reachable VC3 violation needs a non-constant `e''`
(a constant final op erases the swap), e.g. kinds `{not, c0}` with
`rc(not, c0) = Fst`. But that skeleton already forces a CD *cell collision*:
CDVC3 at `U = {not}` demands `mergeL(0, 0, 1) = 1`, while at
`U = {not, c0}` (the `c0` is loOn-maximal via the rc edge) it demands
`mergeL(0, 1, 0) = 0`; for a branch-symmetric merge these are the same cell,
so VC8 goes red for *every* merge table. The wrongly-ordered effect pair that
VC3-redness requires is exactly what CD prices, before the lift itself is
ever consulted. Consumption-side reading: the metatheory consumes VC3 only
through the swap-erasure lemma that powers convergence
(`applySeq_swap_via_cond_comm_lift_u`), so on reachable sets VC3 is part of
the convergence content already assigned to the core. Verdict: joins the
VC1/VC2/VC4 class (stated stronger than adequacy requires; reachable content
absorbed by convergence). The reachable half is bounded-search evidence plus
the collision mechanism, not a general proof; the sentinel half is a
machine-checked witness.

### VC4 (merge symmetry): NOT independent; weakenable to feasible tuples.

Witness: ORSet with `mergeL` biased toward the second argument exactly when that
argument carries a sentinel tag `(0, 9)`. Because `do` mints only timestamps `>=
1`, no canonical (reachable) state ever contains the sentinel, so the asymmetry
is invisible to every configuration-level condition and to the Join. Vector
`[VC4]`, **RA-linearizable**, convergent: VC4 is over the whole state universe
(which includes the sentinel) and sees the asymmetry, while VC5 through VC8 and
RA-lin only ever evaluate `mergeL` on canonical tuples and stay green. H_4 is
refuted.

Control: dropping the branch entirely, `mergeL(l,a,b) = (l & a & b) | (a - l)`
(drop `b`'s contribution), gives `[VC4, VC5, VC8]` and not RA-linearizable: a
merge asymmetry that *is* visible on reachable tuples co-breaks the feasible unit
(VC5) and CD (VC8). So the only isolating VC4 break is the unreachable one, which
is RA-linearizable. The unconditional statement of VC4 is stronger than needed:
on canonical tuples merge symmetry is forced by `sigma(E1 u E2) = sigma(E2 u
E1)`, so VC4 can be weakened to symmetry on canonical tuples.

### VC5 (feasible unit): RESOLVED (1b), SPLIT: independent at the empty set, derivable elsewhere.

`feasible_init`, `mergeL init init s = s`, is precisely the Join instance at
`E1 = empty`. Phase 1 probed it by losing a tag at `|s| >= 2` and watched the
break leak into VC4/VC6/VC7 (`[VC4, VC5, VC6, VC7]`, not RA-linearizable, not
isolating); it concluded "cannot be isolated". That conclusion is corrected:
it holds for nonempty `s` and fails at the one instance phase 1 never
poisoned, `s = init` itself. Write VC5° for the nullary unit
(`ev = empty`, `s = init`: `mergeL init init init = init`) and VC5+ for the
law at nonempty canonical `s`.

**VC5° is INDEPENDENT.** Witness (found by the exhaustive S2x2 scan, then
hand-derived): the **poisoned-empty-merge G-set**.

* State `{0, 1}`, init `0`; one op kind `set` with `do = const 1`;
  `rc = Either`.
* `mergeL(l, a, b) = a | b`, EXCEPT `mergeL(0, 0, 0) := 1`.

Vector `[VC5]`, **not RA-linearizable**, convergent. Hand-derivation: the
poisoned cell `(0, 0, 0)` is evaluated by no other condition. VC8's delta
slot is always `u = set(B) = 1`, so the CD tuple `(B, A, 1)` misses it and
`mergeL(B, A, 1) = 1 = set(A)`; VC6/VC7's inner merges carry the same
`u = 1` and both sides saturate to `1`; the table is symmetric (VC4); VC1
through VC3 are vacuous (one commuting kind). VC5 is red at exactly
`ev = empty` (`mergeL(0,0,0) = 1 != 0 = sigma(empty)`) and green at every
nonempty canonical `s = 1`. The unique Join failure is the merge of two
fresh replicas: `mergeL(init, init, init) = 1` is no fold of the empty event
set; every other pair has a nonempty side and lands on `sigma(union) = 1`.
All nine `[VC5]`-only synthesis finds (four at two states/two kinds, four at
two states/three kinds, one at three states) violate the Join *only* at the
`(0, 0)` shape: the empty corner is the entire independent content.

**VC5+ is DERIVABLE** from {VC4, VC6, VC8} plus the update core (the
convergence content, where VC3 lives), unconditionally on canonical states
of weakly-closed sets, by strong induction on `|E|`:

* Base `|E| = 1`: CDVC3 at `U = {e}` has `A = B = init` (canonical of the
  empty set), and reads `mergeL(init, init, e(init)) = e(init)`: the unit
  law at every one-event state comes from VC8 alone. The induction floor is
  `|E| = 1`; the empty set sits *below* the floor, which is exactly why VC5°
  is independent while VC5+ is not.
* Step: `s` canonical of nonempty `E`; pick `e` loOn(E)-maximal (the last
  element of a respecting enumeration), `t1` canonical of `E - e`, `B`
  canonical of `down(e) - e`, `u = e(B)`. (i) `s = e(t1)`: convergence
  content; the rc arm of `loOn` is antitone in the event set, so a canonical
  enumeration of `E - e` extended by `e` still respects `loOn(E)`, and
  cond-comm-lift is the swap-erasure that reconciles it with the original
  enumeration. (ii) Instantiate VC6 at `(E1, E2) := (E, empty)` with this
  `e`: every premise is available (the empty set is weakly closed;
  `s0 = s2 = init` are canonical of it). The RHS inner merge is
  `mergeL(init, t1, init) = mergeL(init, init, t1)` (VC4) `= t1` (induction
  hypothesis; the base at `|E| = 2`), so RHS `= mergeL(B, t1, u) = e(t1) = s`
  by CDVC3 at `U = E`. (iii) LHS `= mergeL(init, mergeL(B, t1, u), init)
  = mergeL(init, s, init) = mergeL(init, init, s)` (VC4). VC6 equates LHS
  and RHS: `mergeL(init, init, s) = s`.

Premise audit: the derivation needs `E` weakly closed (VC6 and CD demand
closure). The Lean `feasible_init` quantifies over arbitrary `ev` inside the
configuration, but the adequacy induction invokes it only at closed sides,
so the non-closed surplus is stated-stronger-than-consumed, the VC1/VC4
flavor again. The machine cross-check matches the derivation exactly: no
synthesis find breaks VC5 at a nonempty canonical state while keeping
{VC4, VC6, VC8} green, across all three spaces.

### VC6 (feasible local-redistribute): RESOLVED (1b), INDEPENDENT.

Local-redistribute is the law "a delta applied through the middle branch
commutes past the outer merge." Phase 1 observed that every linear or
pointwise-set merge satisfies it identically and guessed "leaning derivable";
that guess was wrong. The separator, found by the exhaustive S2x2 scan and
then hand-derived in full (it is the *only* `[VC6]`-only family in all three
spaces, recurring at both two and three states), is a real design, the
**change-wins flag**:

* **Type.** `Sigma = {0, 1}`, `init = 0`.
* **do.** `set` (writes `1`), `clear` (writes `0`); both constants.
* **merge.** `mergeL(l, a, b) = a | b` if `l = 0`, else `a & b`: "whoever
  changed the flag relative to the LCA wins."
* **rc.** `rc(clear, set) = Fst` (set wins concurrent races: add-wins).

Vector `[VC6]`, **not RA-linearizable**, convergent. Vector hand-derivation:
VC1 (set/clear non-commuting, rc directional), VC2 (single Fst edge), VC3
(constant kinds: the final `e''` erases any swap), VC4 (both rows symmetric),
VC5 (the `l = 0` row is `a | b`) green. VC8 green, the load-bearing case: for
`e = set`, every element of `down(e) - e` reaches `e` through a clear, so
every loOn-maximal element there is a clear, `B = 0`, and
`mergeL(0, A, 1) = A | 1 = 1 = set(A)`; for `e = clear`, either
`down(e) - e` is nonempty, so `B = 1` and `mergeL(1, A, 0) = A & 0 = 0 =
clear(A)`, or it is empty, and maximality of `e` forces every concurrent set
in `U` to be visNC-followed by a clear, so `A = 0` and the equation reads
`0 = 0`. VC7 green: `e = set` saturates every slot to `1`; `e = clear` with
`B = 1, u = 0` collapses both sides to `0`; `e = clear` with `B = u = 0`
makes the inner merges identities.

**The countermodel** (the minimal one; the oracle confirms no Join violation
with any side under two events). Events: `a = set`, `b = clear` with
`vis a -> b`, and `e = set` concurrent with `b`. Take `E1 = {a, e}`,
`E2 = {a, b}`, LCA `{a}`. Canonical states: `s0 = 1`, `t1 = sigma({a}) = 1`,
`s2 = set;clear = 0`, `B = sigma(empty) = 0`, `u = set(0) = 1`; `e` is
loOn-maximal in the union (the rc edge `b -> e` orders the concurrent clear
before it). VC6:

    LHS = mergeL(1, mergeL(0,1,1), 0) = mergeL(1, 1, 0) = 1 & 0 = 0
    RHS = mergeL(0, mergeL(1,1,0), 1) = mergeL(0, 0, 1) = 0 | 1 = 1.

The same instance is the RA-lin failure: `sigma(E1 u E2) = 1` (the add-wins
`rc` orders `b` before the concurrent `e`, so the re-assertion wins the
fold), but the operational merge of `s1 = 1` with `s2 = 0` over `s0 = 1` is
`1 & 0 = 0`. The semantic failure mode: `e` *re-asserts the LCA value*, and
state-level change-detection cannot distinguish "changed to the same value"
from "unchanged", while `rc` has promised that the set wins. VC6 is
precisely the law that prices delta application past an enclosing merge, and
it is the only one of the eight that sees this.

**Why the derivation from VC7 dies** (the promised premise audit). The only
instantiation of VC7 that reuses VC6's maximal `e` is `E2' := E2 u down(e)`
(making `e` shared while preserving the union, hence `e`'s maximality). But
then VC7's slots are `t0' = sigma((E1 n E2) u (down(e)-e))` and
`t2' = sigma(E2 u (down(e)-e))`, and its conclusion only ever mentions the
delta-saturated merges `mergeL(B, t, u)`. VC6's outer slots `s0, s2` are
delta-*free*; no instance of VC7 produces a delta-free slot. The witness
lives exactly in that gap: at the countermodel, VC7 at `(E1, E2 u {e})`
evaluates both sides to `1` (green) while VC6's delta-free `s2 = 0` under
the `l = 1` branch yields the `0` vs `1` split. Local-redistribute is not a
`b := l` instance or a two-application consequence of redistribute; it is
the unique condition governing a delta whose causal past the other side has
not seen.

**Negative companion** (the isolation is rc-direction-specific). The same
merge with the arbitration flipped, `rc(set, clear) = Fst` (clear wins),
gives `[VC6, VC8]`, not RA-linearizable, not isolating: now CD sees the
mismatch too, at `U = {set, clear}` concurrent with the clear maximal:
`A = 1`, `B = 0`, and CD demands `mergeL(0, 1, 0) = clear(1) = 0`, but
change-wins reads the clear-at-init as no change and gives `1`. Add-wins
arbitration is what hides the flag's blindness from CD (for `e = set`,
`B = 0` always and `mergeL(0, A, 1) = 1 = set(A)` regardless) and exposes it
to VC6 alone.

### VC7 (feasible redistribute): INDEPENDENT.

Witness: the **double-counting counter**. State a count in the naturals;
`do(s, inc) = s + 1` (every `inc` commutes, `rc = Either`); `mergeL(l, a, b) = a
+ b`, dropping the LCA slot instead of subtracting it. Vector `[VC7]`,
**not RA-linearizable**, convergent.

Hand-derivation of the vector: VC1, VC2, VC3 are vacuous (all ops commute, no
`rc = Fst`); VC4 holds (`a + b` is symmetric); VC5 holds (`0 + s = s`); VC6 holds
because the merge is linear, `mergeL(s0, mergeL(B,t1,u), s2) = t1 + u + s2 =
mergeL(B, mergeL(s0,t1,s2), u)`; VC8 (CD) holds because all ops commute, so every
punctured downset is empty, `B = 0`, and `mergeL(0, A, do(0,e)) = A + 1 =
do(A, e)`. But VC7 fails: with `Xi = mergeL(B, ti, u) = ti + u`, the left side is
`X1 + X2 = t1 + t2 + 2u`, while the right side `mergeL(B, t0+..., u) = t1 + t2 +
u`; the duplicated delta `u = e(B)` is counted twice because the merge never
cancels the LCA slot. The RA-lin failure is the same double count: at a merge
whose sides share history (`E1 & E2` nonempty), `mergeL(sigma(E1&E2), sigma(E1),
sigma(E2)) = |E1| + |E2| = |E1 u E2| + |E1 & E2| != sigma(E1 u E2)`, so the
merged version's count is not any linearization-fold of its event set.

This is the exact dual of the AWSetF3 separator for VC8: there the delta laws
hold and CD fails; here CD holds and the redistribute delta law fails. Neither is
derivable from the other plus the core. **H_7 confirmed.**

### VC8 (the causal-delta equation): INDEPENDENT (recalled from #57, reproduced).

Witness: AWSetF3, reproduced faithfully from
`Sal/CRDTs/Metatheory/Assoc_CounterModel.lean` (single implicit key; state
`(added, dead, flag)`; `add` inserts a timestamp and writes `flag := true`;
`rem` moves `added` into `dead` and writes `flag := false`; `mergeL` drops the
LCA slot and takes the pairwise union with `flag_a or flag_b`; `rc(rem, add) =
Fst`). Vector `[VC8]`, **not RA-linearizable**, convergent. The union merge is a
bounded ACI semilattice, so VC1 through VC7 hold, but `rem` deflates the flag
while the merge keeps it: at a `loOn`-maximal `rem` the merge carries `flag =
true` (from an `add` on the other branch) while `do(A, rem)` carries `flag =
false`, so CDVC3 fails. This is the mechanized result of #57
(`cdvc3_not_derivable_from_core_delta`); the harness matches it.

## The derivability algebra for the refuted conditions

Independence was refuted for VC1, VC2, VC4 (phase 1); phase 1b adds VC3 to
this class and splits VC5, with their algebra recorded in the per-VC sections
above. Here is why each of the phase-1 three is removable or weakenable,
pinned as far as pen and paper carry it (a full re-derivation of the
metatheory without these conditions is the phase-2 Lean obligation).

**VC1.** Split the biconditional. The reverse direction (rc orders a commuting
pair) never affects a fold, so it is inert for adequacy; the grow-only-set
witness satisfies VC2 through VC8 and is RA-linearizable with it broken. The
forward direction (a non-commuting concurrent pair `a, b` with `rc a b = rc b a =
Either`) is enforced by VC8 on reachable configurations. At the weakly-closed
two-element set `U = {a, b}`, both `a` and `b` are `loOn(U)`-maximal (no rc edge,
no vis edge). CDVC3 at `e = a` demands `mergeL(init, sigma{b}, a(init)) =
a(sigma{b})`; at `e = b` it demands `mergeL(init, sigma{a}, b(init)) =
b(sigma{a})`. With merge symmetry (VC4) fixing one function and `a, b`
non-commuting, these two equations cannot both hold unless one order's fold
equals the other's, which would make `a` and `b` commute. Hence a forward-VC1
violation on a reachable concurrent pair forces a VC8 (or VC4) failure. Among
datatypes satisfying VC2 through VC8, the forward direction of VC1 holds
automatically. So `{VC2..VC8} => RA-lin`, and VC1 is redundant for adequacy
(the harness shows both halves: `rc := Either` reddens VC8; the spurious-order
witness stays green and RA-linearizable).

**VC2.** `no_rc_chain` is consumed only in the acyclicity lemma
(`loOnNe_acyclic`). The true requirement is that `loOn` be acyclic on the
reachable event sets. A chain that lies along a total order (the LWW register,
`rc` = timestamp order) is acyclic and RA-linearizable, so `no_rc_chain` is
strictly stronger than needed. Replace it by "loOn acyclic on reachable sets":
adequacy survives, and the chain-into-cycle case (which does break RA-lin) is
excluded by that weaker condition while co-failing VC8, so it never threatened
isolation.

**VC4.** The metatheory evaluates `mergeL` only on canonical tuples. On those,
symmetry is a theorem, not an axiom: `mergeL(sigma(E1&E2), sigma(E1), sigma(E2))`
and `mergeL(sigma(E1&E2), sigma(E2), sigma(E1))` both equal `sigma(E1 u E2) =
sigma(E2 u E1)` once the Join holds (which needs VC5, VC6, VC7, VC8 but not
the unconditional VC4). So VC4 can be weakened to "symmetric on canonical tuples,"
supplied by the others. The sentinel witness (asymmetry confined to an
unreachable state) satisfies VC5 through VC8 and is RA-linearizable, confirming
the unconditional strength is unused.

## Synthesis (corrected in 1b): a four-law core, not a dual pair

| VC | condition | verdict | witness / evidence |
|----|-----------|---------|--------------------|
| VC1 | rc-non-comm-directional | NOT independent (redundant for adequacy) | G-set spurious `rc` `[VC1]` RA-lin; `rc:=Either` `[1,6,8]` co-fails VC8 |
| VC2 | no-rc-chain | NOT independent (sufficient not necessary) | LWW register `[VC2]` RA-lin; cycle co-fails VC8 |
| VC3 | cond-comm-lift | NOT independent (weakenable to reachable states) | sentinel `[VC3]` RA-lin; no reachable witness in 15024 synthesized specs; CD-cell collision mechanism |
| VC4 | merge symmetry | NOT independent (weakenable to canonical tuples) | sentinel asymmetry `[VC4]` RA-lin; drop-b `[4,5,8]` co-fails |
| **VC5** | feasible unit | **SPLIT: INDEPENDENT at `ev = empty`** (VC5°); derivable at nonempty `s` from {VC4, VC6, VC8}+core | poisoned-empty G-set `[VC5]` not RA-lin, Join fails only at `(0,0)`; the VC5+ induction |
| **VC6** | feasible local-redistribute | **INDEPENDENT** | change-wins flag `[VC6]` not RA-lin; rc-flip companion `[6,8]` |
| **VC7** | feasible redistribute | **INDEPENDENT** | double-counting counter `[VC7]` not RA-lin; two-state shadow: parity counter |
| **VC8** | causal-delta equation | **INDEPENDENT** (#57) | AWSetF3 `[VC8]` not RA-lin; two-state shadow: enable-wins flag |

The irreducible, genuinely independent core is **four laws**: the delta pair
**VC7** and **VC8** (phase 1's dual pair, each satisfiable while the other
fails), plus **VC6** (the change-wins flag satisfies the other seven and is
not RA-linearizable) and **VC5°**, the nullary unit (the poisoned-empty
G-set likewise). Each of the four has a separator with the other seven
green; none is derivable from the rest.

The remaining four are not independent as stated.

* The update-layer conditions VC1, VC2, VC3 and the merge-symmetry VC4 are
  stated more strongly than adequacy requires. Each has an RA-linearizable
  violator (spurious order; a chain along a total order; a lift failure at an
  unreachable state; asymmetry at an unreachable state). Their true content
  is: rc must order non-commuting *reachable concurrent* pairs (subsumed by
  VC8), loOn must be *acyclic on reachable sets*, the fold must *converge on
  reachable sets* (where reachable VC3 content lives), and merge must be
  symmetric *on canonical tuples*. They remain load-bearing for the *proof*,
  where they drive the convergence and acyclicity machinery, but they are
  not part of the minimal adequacy contract in their unconditional forms.

* VC5's nonempty half (VC5+) is genuinely derivable: the empty corner is the
  floor of the Join induction, below the reach of CDVC3's one-event base,
  and that floor is the entire independent content of `feasible_init`.

Search bounds for the 1b verdicts: 1408 specs (two states, two kinds,
exhaustive over all symmetric merge tables and admissible rc), 6016 (two
states, three kinds, exhaustive), 7600 (three states, two kinds: all
structured merges, all 27 unital commutative magmas, 4000 seeded random
tables), each filtered through 12 four-event honest DAGs and every survivor
confirmed over seeds 114, 7, 2026 with four- and five-event DAGs. The
searcher's calibration re-finds the enable-wins flag (`[VC8]`) and the
parity counter (`[VC7]`) from scratch in the exhaustive space, so its
negative verdicts (notably: no reachable `[VC3]`-only spec, and no
`[VC6]`-only family other than change-wins) are searches that could have
succeeded.

Contrast with the pre-sweep expectation that all eight were irredundant (the
"tight-set" reading of #57), and with phase 1's own headline that only VC7
and VC8 survive. Both were wrong in opposite directions. The flat set
shrinks, but to a four-law contract: {VC5°, VC6, VC7, VC8} plus the weakened
acyclicity and convergence content of the update layer.

## What this feeds (phase 2, not done here)

* **The restricted converse.** Does a canonical flat MRDT that is
  RA-linearizable satisfy the VCs on its reachable states? The shrink here is its
  mirror: the update-layer VCs are exactly the parts whose *unconditional* form
  exceeds what reachable states witness, so the converse should recover only
  their reachable-state restrictions. This is where conditioning enters as the
  completion.

* **The Lean shrink.** The claims "`{VC2..VC8} => RA-lin`" (VC1 redundant),
  "no-rc-chain weakens to reachable-set acyclicity" (VC2), "cond-comm-lift
  weakens to reachable states" (VC3), and "merge symmetry weakens to
  canonical tuples" (VC4) are evidence-level here (bounded search, hand
  algebra). Each is a metatheory re-derivation: re-close `JoinLemma3`
  without the dropped or weakened field. The corrected minimal core to
  target: `{acyclicity, convergence-on-reachable, VC5-at-empty,
  feasible-local-redistribute, feasible-redistribute, CDVC3}`.

* **Two new refutation mechanizations** (the phase-2 Lean targets this note
  creates, both finite and #57-shaped):
  `local_redistribute_not_derivable`, discharging the change-wins flag's
  seven green VCs over `Bool` and refuting the Join at the four-event
  countermodel; and `feasible_init_not_derivable_at_empty`, the same for
  the poisoned-empty G-set at the two-fresh-replica merge. Beside them, the
  positive half: mechanize the VC5+ induction (`feasible_init` off the
  empty set follows from {VC4, VC6, VC8} + the update core; the proof
  sketch in the VC5 section is Lean-shaped, needing the loOn rc-arm
  antitonicity lemma and the existing swap-erasure).

* **The change-wins flag as a catalogue item.** The VC6 separator is not a
  pathology: it is the natural state-based flag design ("changed-from-LCA
  wins" plus add-wins arbitration), and it is exactly the flag whose merge
  cannot see a concurrent re-assertion of the LCA value. Worth recording
  next to the enable-wins flag in the MRDT catalogue as a boundary
  non-example, the flag analogue of the ORSet-without-tags.
