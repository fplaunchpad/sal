# The VC minimality sweep (task #114, phase 1)

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

**Headline.** The flat set is not irredundant as stated. Exactly two of the
eight are genuinely independent: **VC7 (redistribute)** and **VC8 (the
causal-delta equation)**, a matched pair of delta laws. The other six split
into two groups. Three (**VC1, VC2, VC4**) are stated *stronger than adequacy
requires*: there are RA-linearizable datatypes that violate them, so each can
be weakened without losing adequacy. Three (**VC3, VC5, VC6**) resist isolation
because every mutation that breaks them co-breaks a core law (VC8 or VC7): their
content overlaps the delta core rather than adding to it. The irreducible core
for adequacy is the two delta laws VC7 and VC8 together with the acyclicity and
convergence content of the update layer, not the update layer as literally
stated.

Method note (per the project discipline): goals and falsifiable hypotheses are
stated first, then a stdlib Python harness
(`whiteboard/litmus/vc_minimality_check.py`) that decides the eight VCs and a
loOn-fold RA-linearizability checker over honest three-way-merge DAGs. Every
verdict below is hand-derived and cross-checked against the harness; the harness
never supplies an expected value for the object it is judging. No Lean this
phase.

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

Each witness is a minimal mutation of a boundary datatype (or the smallest
separator in its family). The satisfaction vector is written `[reds]` with the
RA-lin verdict; every vector is reproduced by the harness across seeds 114, 7,
2026 with zero mismatches against the hand-derived expectation.

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

### VC3 (cond-comm-lift): resists isolation; co-dependent with VC8.

Probe: ORSet with the add-wins arbitration reversed, `rc(add x, rem x) = Fst`.
Vector `[VC3, VC6, VC8]`, **not RA-linearizable**. Every attempt to break
cond-comm-lift for these datatypes forces a non-commuting pair to be ordered the
wrong way, which co-breaks CDVC3 (VC8) and local-redistribute (VC6). For
overwrite-shaped ops cond-comm-lift holds automatically (the final `e''`
overwrites, so the swap of `e, e'` is invisible), so a genuine VC3 violation
needs an rc direction that contradicts the effect order, and that contradiction
is exactly what CD detects. No isolating witness was constructed; VC3's content
overlaps VC8 rather than adding to it. Unresolved as a clean independence, with
strong co-dependence evidence.

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

### VC5 (feasible unit): co-load-bearing; the shared empty-side base case.

`feasible_init`, `mergeL init init s = s`, is precisely the Join instance at
`E1 = empty`: `mergeL(sigma(empty), sigma(empty), sigma(E2)) = sigma(E2)`.
Breaking it therefore breaks the Join at every empty-LCA merge, which is a real
non-RA-linearizable failure. But it cannot be isolated. Perturbing the
`(init, init, s)` corner is either asymmetric (co-breaks VC4) or, made symmetric,
leaks into the degenerate empty-side instances of the redistribute laws (`E2 =
empty` is a legal weakly-closed premise of both VC6 and VC7). The probe (ORSet
losing a tag when merging over `init` with `init` and a two-tag branch) gives
`[VC4, VC5, VC6, VC7]`, not RA-linearizable. So `feasible_init` is not an
independent obligation but the shared base case of the merge-symmetry and
redistribute laws; the harness confirms it cannot be moved without moving them.

### VC6 (feasible local-redistribute): resists isolation; holds for linear merges.

Local-redistribute is the law "a delta applied through the middle branch
commutes past the outer merge." For every linear or pointwise-set merge it holds
identically (it is a rearrangement, not a cancellation), so a datatype that
breaks it while keeping CD and redistribute is hard to exhibit. The candidate
tried (ORSet with `b`'s new tags gated by membership in `a`) satisfies VC6 and
VC7 but breaks VC4, VC5, VC8: vector `[VC4, VC5, VC8]`, not RA-linearizable, not
isolating. No isolating witness found. The evidence points to VC6 being either
derivable from VC7 plus the core or co-load-bearing with it; a clean separator,
if one exists, needs a non-linear merge whose local and global redistributions
genuinely diverge. Unresolved, leaning derivable.

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

Independence was refuted for VC1, VC2, VC4. Here is why each is removable or
weakenable, pinned as far as pen and paper carry it (a full re-derivation of the
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
sigma(E2 u E1)` once the Join holds (which needs VC5, VC7, VC8 but not the
unconditional VC4). So VC4 can be weakened to "symmetric on canonical tuples,"
supplied by the others. The sentinel witness (asymmetry confined to an
unreachable state) satisfies VC5 through VC8 and is RA-linearizable, confirming
the unconditional strength is unused.

## Synthesis: the set is not irredundant; it shrinks

| VC | condition | verdict | witness / evidence |
|----|-----------|---------|--------------------|
| VC1 | rc-non-comm-directional | NOT independent (redundant for adequacy) | G-set spurious `rc` `[VC1]` RA-lin; `rc:=Either` `[1,6,8]` co-fails VC8 |
| VC2 | no-rc-chain | NOT independent (sufficient not necessary) | LWW register `[VC2]` RA-lin; cycle co-fails VC8 |
| VC3 | cond-comm-lift | UNRESOLVED (co-dependent with VC8) | reversed `rc` `[3,6,8]` not RA-lin; no isolating witness |
| VC4 | merge symmetry | NOT independent (weakenable to canonical tuples) | sentinel asymmetry `[VC4]` RA-lin; drop-b `[4,5,8]` co-fails |
| VC5 | feasible unit | co-load-bearing (shared empty-side base case) | lossy-init `[4,5,6,7]` not RA-lin; not isolable |
| VC6 | feasible local-redistribute | UNRESOLVED (holds for all linear merges, leans derivable) | a-gated probe `[4,5,8]`; no isolating witness |
| **VC7** | feasible redistribute | **INDEPENDENT** | double-counting counter `[VC7]` not RA-lin |
| **VC8** | causal-delta equation | **INDEPENDENT** (#57) | AWSetF3 `[VC8]` not RA-lin |

The irreducible, genuinely independent core is the two delta laws **VC7
(redistribute)** and **VC8 (CDVC3)**, a dual pair: VC8's separator satisfies the
delta laws and fails CD; VC7's separator satisfies CD and fails the delta law.
Neither is derivable from the other plus the rest.

The remaining six are not independent as stated.

* The update-layer conditions VC1 and VC2 and the merge-symmetry VC4 are stated
  more strongly than adequacy requires. Each has an RA-linearizable violator
  (spurious order; a chain along a total order; asymmetry on an unreachable
  state), so none is load-bearing for adequacy. Their true content is: rc must
  order non-commuting *reachable concurrent* pairs (subsumed by VC8), loOn must
  be *acyclic on reachable sets* (a weakening of no-rc-chain), and merge must be
  symmetric *on canonical tuples* (a consequence of the Join). They remain
  load-bearing for the *proof*, where they drive the convergence and acyclicity
  machinery, but they are not part of the minimal adequacy contract.

* VC3, VC5, VC6 resist isolation because their content overlaps the core: every
  break of VC3 co-breaks VC8, every break of VC5 co-breaks VC4 or the
  redistribute laws (VC5 is literally the empty-side base case of the Join that
  VC6 and VC7 also invoke), and VC6 holds for every linear merge and leans derivable from
  VC7.

Contrast with the pre-sweep expectation that all eight were irredundant (the
"tight-set" reading of #57). That reading holds only for VC7 and VC8. The flat
set shrinks: the adequacy contract is carried by the two delta laws plus the
weakened acyclicity and convergence content of the update layer.

## What this feeds (phase 2, not done here)

* **The restricted converse.** Does a canonical flat MRDT that is
  RA-linearizable satisfy the VCs on its reachable states? The shrink here is its
  mirror: the update-layer VCs are exactly the parts whose *unconditional* form
  exceeds what reachable states witness, so the converse should recover only
  their reachable-state restrictions. This is where conditioning enters as the
  completion.

* **The Lean shrink.** The claims "`{VC2..VC8} => RA-lin`" (VC1 redundant),
  "no-rc-chain weakens to reachable-set acyclicity" (VC2), and "merge symmetry
  weakens to canonical tuples" (VC4) are evidence-level here (bounded search,
  hand algebra). Each is a metatheory re-derivation: re-close `JoinLemma3`
  without the dropped or weakened field. VC7-vs-VC8 duality suggests the natural
  minimal core to target first: `{acyclicity, convergence, feasible-redistribute,
  CDVC3}`.

* **VC6.** Settle whether local-redistribute is derivable from redistribute plus
  the core, or genuinely independent via a non-linear merge. That every linear
  and pointwise-set merge satisfies it is the reason no set or counter separator
  isolates it here.
