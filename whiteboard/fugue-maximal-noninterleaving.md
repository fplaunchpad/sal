# The Weidner-Kleppmann maximal non-interleaving statement for the sided embed under the Fugue policy

*Task #84 research residue. Written 2026-07-16, before the Lean work, per
the standing protocol (pen and paper, then Python, then Lean). The
executable check is `whiteboard/litmus/fugue_noninterleave_check.py`; the
mechanization is
`Sal/ConditionedMRDTs/MRDT_Instances/SidedRGA/SidedRGA_Fugue.lean`. The
paper is Weidner and Kleppmann, "The Art of the Fugue: Minimizing
Interleaving in Collaborative Text Editing", arXiv:2305.00583v3 (also IEEE
TPDS 36(11), 2025). All quotes below were extracted from v3 of the arXiv
PDF on 2026-07-16.*

**Headline results.** The repo's Fugue policy over the sided embed
satisfies forward non-interleaving (condition 1: 1500 randomized cases and
every directed case clean) and the two-concurrent-runs property (candidate
(a): clean everywhere, and the kernel half is now a Lean theorem). The
FULL maximal non-interleaving statement is REFUTED for this policy, twice
over: condition (3) fails on a two-operation trace (the repo's newest-first
sibling order reverses the paper's lowest-ID-first tiebreak), and condition
(2) fails on the paper's own Figure-7 execution (the repo's policy is
Fugue, not FugueMax, and this is exactly the gap the paper proves between
them). Both refutations are machine-witnessed in Python and in Lean. A
formalization finding along the way: Definition 4's comparison quantifier
must range over all elements including tombstones, or the definition is
unsatisfiable for the whole Fugue family (countermodel below).

## 1. The paper's definitions, verbatim

Section 5.1 defines the origins:

> "In an execution using a replicated list, the *left origin* of an
> element is the element directly preceding its insertion position at the
> time of insertion. Specifically, if the element was inserted by an
> insert(i, x) call, then its left origin was at index i - 1 at the time
> of the call. If there was no such element (i = 0), then its left origin
> is a special symbol *start*."

> "Dually to the definition of left origin, we define the *right origin*
> of an element to be the element directly following its insertion
> position at the time of insertion, or the special symbol *end* if no
> following element exists. Specifically, the right origin is the element
> directly following the left origin in *the list including tombstones
> (deleted elements)*, like the rightOrigin variable in Algorithm 1."

Definition 2 (forward non-interleaving):

> "A replicated list algorithm is **forward non-interleaving** if it
> satisfies the strong list specification [4] and the following holds for
> all list elements A and B in all possible list states: if A is the left
> origin of B, and B appears earlier in the list than any other element
> that has A as left origin, then A and B are consecutive list elements."

Definition 4 (maximal non-interleaving):

> "A replicated list algorithm is **maximally non-interleaving** if it
> satisfies the strong list specification [4] and the following holds for
> all list elements A and B in all possible list states:
>
> (1) (Forward non-interleaving) If A is the left origin of B, and B
> appears earlier in the list than any other element that has A as left
> origin, then A and B are consecutive list elements.
>
> (2) (Backward non-interleaving, with exceptions) If B is the right
> origin of A, and A appears later in the list than any other element
> that has B as right origin, then A and B are consecutive list elements,
> unless Theorem 5 below says otherwise.
>
> (3) If A and B have the same left origin and the same right origin,
> then the element with the lower ID appears earlier in the list."

Lemma 5 (the exception referenced by condition (2)):

> "Given a replicated list algorithm that satisfies the strong list
> specification and forward non-interleaving (condition (1)). Suppose B is
> the right origin of A, and A appears later in the list than any other
> element that has B as right origin, but:
>
> i. A and B have different left origins; and
>
> ii. there is a C in the current list state such that A.leftOrigin < C <
> B and C is not a descendant of A.leftOrigin in the left-origin tree.
>
> Then A < C < B, so A and B are not consecutive list elements."

Theorem 9: "FugueMax satisfies conditions (1), (2), and (3) of [Definition
4]. Hence FugueMax is maximally non-interleaving." Theorem 10: "Let L be a
replicated list algorithm that is maximally non-interleaving. Then L is
semantically equivalent to FugueMax." The paper also proves (Section 5.3)
that plain **Fugue is not maximally non-interleaving**: in the Figure-7
execution, the two elements X and Y are same-side siblings, Fugue traverses
them in lexicographic ID order, and if that order is Y < X then condition
(2) is violated for the pair (Y, B). "The advantage of FugueMax is only
that it backward-interleaves one fewer pair of characters (here YB)."
Condition (3) is, in the authors' words, "an arbitrary choice", but by
Theorem 10 it is not optional: maximal non-interleaving pins the entire
list order to FugueMax's.

The paper's "left-origin tree" (Section 5.1) is the tree in which each
element's parent is its left origin, rooted at *start*; "descendant" in
Lemma 5(ii) refers to this tree, not to the algorithm's own tree.

## 2. The repo's model, and the restatement

The datatype is the sided embedded-chain RGA
(`MRDT_Instances/SidedRGA/SidedRGA.lean` over the kernel
`Sal/MRDTs/RGA_Embed/Sided_ChainLex.lean`):

- Ops are `(ts, replica, ins e π a sd | del x)`. The timestamp doubles as
  the element identity; ids are ℕ with Lamport discipline (fresh, larger
  than everything the generator has seen).
- An insert's coordinate is `sCoord Γ o = π ++ sBlock Γ (sd, o.1 - a)`:
  the anchor's stored coordinate plus one sided block. Semantically the
  element's position is a birth chain (a `SChain`, a list of
  `(Side, delta)` entries telescoping to the id), immutable forever.
- Display is the descending `sKey` order of the canonical sorted state:
  L-descendants, then the node, then R-descendants; among R-siblings the
  NEWER (larger ts) displays first, adjacent to the node from below; among
  L-siblings the newer sits adjacent to the node from above. This is the
  RGA recency order on both sides.
- Concurrency is the framework's `vis`: neither op in the other's causal
  past.
- Side selection is a generation-time policy. The Fugue policy
  (`embed_sided.py`, `choose`): for intent "insert after a" (a = 0 means
  the front), compute the successor n of a in the local order over ALL
  minted nodes, dead included; if a has never had an R-child (again dead
  included) or n does not exist, mint `(R, a)`; else mint `(L, n)`.

The origin mapping is exact, not analogical: the intent anchor a IS the
paper's left origin (the element at index i - 1 of the live view, or
start), and the policy's computed successor n IS the paper's right origin
(the next node after the left origin in the traversal including
tombstones, matching Algorithm 1 lines 22-28 of the paper). So the
statement can be adapted with no modeling slack: record `(lo, ro) = (a, n)`
per insert at generation time and quantify over final states.

### Adaptation decisions

1. **Elements** are insert ops; the id is the timestamp. "All possible
   list states" becomes: every replica's state in every configuration
   reachable by the generation layer (local Fugue-policy inserts, local
   deletes, pairwise knowledge sync; causal delivery is automatic because
   whole knowledge sets transfer).
2. **The list order <** (the strong list specification's total order over
   elements including tombstones) is the descending key order over minted
   coordinates. This exists here by construction: coordinates are
   immutable and totally ordered (`schainBefore_total` plus the marker
   theorem), which is exactly why the strong-list clause of Definition 4
   needs no separate treatment; the capstone
   `sided_embed_ra_linearizable3` covers the convergence half.
3. **"Appears earlier in the list than any other element that has A as
   left origin"**: the quantifier ranges over ALL elements with left
   origin A, tombstones included, compared in the total order <. Call
   this the strict reading. The lenient reading (quantify over live
   elements only) is FALSE for every algorithm of this family: LCA
   `[ins 1]`, replica A `ins 5 after 1`, replica B `ins 8 after 1; ins 9
   after 8; del 8` merges to display `[1, 9, 5]`; the only live element
   with left origin 1 is 5, yet 9 (left origin 8, dead) sits between.
   Under the strict reading the premise selects the dead 8, not 5, and
   nothing is violated. The paper's Theorem-9 proof implicitly uses the
   strict reading (it identifies B with the first node of A's right
   subtrees in the tombstone-including traversal). Machine check:
   `lenient-C1 countermodel` in the script, strict clean, lenient fires.
4. **Consecutive list elements**: A before B in < and no LIVE element
   strictly between (tombstones are skipped by the visible list).
5. **ID order** for condition (3) is the total order on timestamps. The
   paper's IDs are (replicaID, counter) pairs under lexicographic order;
   the repo has a single ℕ. Both are arbitrary total orders on elements,
   which is the role condition (3) needs.
6. **start** is the empty chain (the virtual root, key `[3]`). Under the
   Fugue policy every minted element sits below the root key (the policy
   never mints an L-child of the root: the L branch always targets a real
   successor node), so "start before everything" holds literally in the
   key order and needs no special casing.
7. **The left-origin tree** is the graph of the recorded `lo` fields;
   descendant means some iterate of `lo` reaches the given ancestor.
8. **An insertion run** (for candidate (a)): consecutive inserts by one
   replica with no interleaved delivery, either forward (each op's intent
   anchor is the previous op's element) or backward (each op's intent
   anchor is the same element, repeatedly inserting at one position).
   Under the Fugue policy both shapes CHAIN: each new element is minted as
   a child of the previous run element (R-child for forward; for backward
   the successor of the fixed anchor is always the previously minted run
   element, so each mint is an L-child of the previous). A run is
   therefore a birth-chain-nested family, hence inside one subtree.

### What the repo's policy is, precisely

The paper fixes THREE things: the tree-position rule (Fugue's insert
cases), the sibling order, and (for FugueMax) the reverse-right-origin
right-sibling order. The repo takes Fugue's tree-position rule verbatim,
but the kernel's sibling order is RGA recency (newest adjacent to the
node on both sides), where paper-Fugue uses ascending ID on both sides.
On the L side these agree in spirit (newest adjacent to the node is
ascending ts among L-siblings, which matches lowest-ID-first in the
display). On the R side they are REVERSED: the repo displays the newest
R-sibling first, paper-Fugue the lowest ID first. So the repo policy is
"Fugue side selection + RGA tiebreak", a third point in the family, and
neither Fugue's nor FugueMax's tiebreak claims transfer.

## 3. Statement candidates, and what happened to each

**(a) Two concurrent runs at one position never interleave.** Both
directions and mixed. Expected true; validated (section 4); the kernel
half is now a Lean theorem (`fugue_two_runs_no_interleave` via
`sided_fold_subtree_convex`), with the policy half split into a proved
forward-run lemma and one identified gap (section 5).

**(b) Full W-K maximal non-interleaving (Definition 4, all three
conditions, strict reading).** REFUTED for the repo policy, on two
independent axes, both expected in advance and both machine-witnessed:

- **Condition (3) fails on the smallest possible trace.** Two concurrent
  front inserts x=1, x=2 merge to display `[2, 1]`: same left origin
  (start), same right origin (end), and the LOWER id displays LATER. This
  is not an interleaving anomaly; it is the tiebreak clause, and the
  repo's newest-first R-sibling order is its exact reverse. Note the
  asymmetry: for L-siblings (backward runs) the repo's order MATCHES
  condition (3), so no fixed-direction rewrite of (3) is satisfied either.
  By Theorem 10 this alone already denies maximal non-interleaving
  (which pins the whole order to FugueMax's).
- **Condition (2) fails on the paper's Figure-7 execution.** Three
  concurrent front inserts A=5, B=4, C=3; replica 1 (knowing 5, 3)
  inserts X=6 between 5 and 3; replica 2 (knowing 5, 4) inserts Y=7
  between 5 and 4. Merged display: `[5, 7, 6, 4, 3]` (X and Y are
  R-siblings under 5; the newer Y displays first). Y=7 is the only
  element with right origin B=4, yet 6 sits between 7 and 4; the Lemma-5
  exception does not apply (everything between is a descendant of
  Y.leftOrigin = 5 in the left-origin tree). This is precisely the
  Fugue-vs-FugueMax gap of the paper's Section 5.3, reproduced with the
  recency tiebreak playing the role of the adverse ID order. FugueMax's
  repair (right siblings in reverse right-origin order) is a different
  policy-plus-tiebreak; it is not what task #83 built and validated.

**(1) alone (forward non-interleaving, Definition 2, strict reading).**
Expected true, and every check agrees (zero violations in 1500 randomized
final states plus all directed cases). Believed true for the same
structural reason as the paper's Lemma 7/8 argument: the walk-up
characterization of left origins holds for ANY sibling order, and the
first traversal node after A always has left origin A. Not proved in Lean
(the proof needs the full traversal theory relating the sorted display to
tree walks, which the kernel does not yet have); stated as a `def`.

### Proof-obligation map (candidate (a))

- Display half: `schain_subtree_convex` (kernel) and its fold form
  `sided_fold_subtree_convex` (already proved, task #84 first half):
  anything displayed between two members of a subtree is in the subtree.
- Policy half: "a Fugue run chains". Forward runs: the anchor is the
  freshly minted previous element, which has never had an R-child, so the
  policy returns `(R, previous)`; proved (`fugue_forward_run_chains`).
  Backward runs: the policy returns `(L, succ(a))` and the successor of
  the fixed anchor is the previously minted run element; this
  "newest-mint adjacency" fact is the one identified gap (section 5).
- Concurrency half: two concurrent runs' head chains are
  prefix-incomparable (a concurrent replica has not seen the head, and a
  chain can only extend chains its minter has seen; by telescoping, a
  chain extending the head would sum through the head's id). Taken as a
  hypothesis of the Lean theorem; the discharge route is the `GInv`
  invariant already proved (`fugueReach_inv`).

## 4. Worked examples (all machine-checked in Python and as Lean SPOTs)

**L19 backward (the validated trace).** LCA `[ins 1 at front]`; replica A
backward-types 10, 30, 50 at the front; replica B backward-types 21, 41,
61 at the front. Policy: 10 becomes `(L, 1)` (1 is the front element and
has an R-history at the root... precisely: anchor is start, successor is
1, start "has an R-child" since 1 was minted `(R, root)`), 30 becomes
`(L, 10)`, 50 `(L, 30)`; symmetrically 21 `(L, 1)`, 41 `(L, 21)`, 61
`(L, 41)`. Merged display `[50, 30, 10, 61, 41, 21, 1]`: blocks
contiguous, in text order, A's block first because 10 is an OLDER
L-sibling of 1 than 21 (L-siblings display oldest first, newest adjacent
to the node). W-K check: all three conditions CLEAN on this state
(backward runs record `ro` chains, and the latest-with-ro premises select
exactly the adjacent pairs; the same-origin pairs are L-siblings, where
the repo order matches condition (3)).

**Forward twin.** LCA `[ins 1]`; A forward-types 10, 30, 50 after 1; B
forward-types 21, 41, 61 after 1. Policy: run heads 10 and 21 both
`(R, 1)`, tails chain as R-children. Merged display
`[1, 21, 41, 61, 10, 30, 50]`: blocks contiguous, B first (newer head
adjacent to 1). W-K check: conditions (1) and (2) clean; condition (3)
fires on the head pair (10, 21): same origins `(1, end)`, lower id 10
displays later. The tiebreak decides which BLOCK comes first, nothing
else.

**Mixed.** Same LCA; A backward-types 10, 30, 50 after 1 (fixed intent
anchor 1); B forward-types 21, 41, 61. Policy: 10 `(R, 1)`; then hasR(1)
holds so 30 becomes `(L, succ(1)) = (L, 10)` and 50 `(L, 30)`; B chains
`(R, 1)`, `(R, 21)`, `(R, 41)`. Merged display
`[1, 21, 41, 61, 50, 30, 10]`: both blocks contiguous in text order, no
interleaving; condition (3) fires on (10, 21) again, conditions (1), (2)
clean. Note the backward block reads 50, 30, 10 which IS backward-typed
text in document order.

## 5. Python validation results

`whiteboard/litmus/fugue_noninterleave_check.py` (new file; it subclasses
`embed_sided.SidedChain` to capture origins at generation time and
implements the strict and lenient checkers plus the concurrency-aware run
check). Run of record: `python3 fugue_noninterleave_check.py 500`,
deterministic seeds.

Directed cases (every display matched its hand-derived expectation):

| case | display | strict verdict |
|---|---|---|
| two-front-inserts | `[2, 1]` | C3 violated: (2, 1) |
| L19 backward | `[50, 30, 10, 61, 41, 21, 1]` | CLEAN |
| forward twin | `[1, 21, 41, 61, 10, 30, 50]` | C3 violated: (21, 10) |
| mixed fwd/bwd | `[1, 21, 41, 61, 50, 30, 10]` | C3 violated: (21, 10) |
| lenient-C1 countermodel | `[1, 9, 5]` | strict CLEAN; lenient C1 violated: (1, 5) |
| figure 7 (W-K) | `[5, 7, 6, 4, 3]` | C2 violated: (7, 4); C3 violated: root siblings |

Randomized sweeps (Fugue policy, strict reading, violations counted per
offending pair; RUN is the concurrency-aware candidate-(a) check):

| shape | n | C1 | C2 | C3 | RUN | lenient C1 |
|---|---|---|---|---|---|---|
| 2-branch runs | 500 | 0 | 0 | 198 | 0 | 0 |
| 3-branch runs | 500 | 0 | 0 | 515 | 0 | 0 |
| 3-branch two-epoch (fig-7 shaped) | 500 | 0 | 2 | 564 | 0 | 0 |

The two organic C2 hits (first: seed-3 case 404, pair (15, 6)) are
Figure-7-shaped executions found by the sweep itself, confirming the
directed analysis. C1 and RUN never fired anywhere: forward
non-interleaving and the two-concurrent-runs property survived 1500
randomized final states. One earlier checker bug is worth recording: a
naive run-contiguity check flags epoch-2 runs that INSERT INTO an epoch-1
block they have already received; that is user intent, not interleaving,
so the run check must exempt elements causally after the run (the fixed
check does).

## 6. The Lean mechanization: what is proved, stated, and open

File `Sal/ConditionedMRDTs/MRDT_Instances/SidedRGA/SidedRGA_Fugue.lean`
(namespace `Sal.ConditionedMRDTs`), wired into the umbrella. Contents:

- **The intent layer**: `GRec` (op + generation-time `lo`, `ro`, birth
  chain), knowledge lists, `gView` (the live display), `succOf` (the
  tombstone-visible successor), `hasRChild`, and `fugueChoose` mirroring
  the Python `choose` exactly; positional intent `genInsAt` via
  `anchorAt`; `genDelAt`; knowledge sync `syncK`; the reachability
  inductive `FugueReach` (local Fugue inserts with Lamport-fresh ids,
  local deletes, pairwise sync).
- **The statement** (the core deliverable): `ForwardNI`, `BackwardNIExc`
  (with `BackwardException` = Lemma 5), `SameOriginLowFirst`, bundled as
  `MaxNonInterleaving Γ K` per state, and
  `FugueMaximallyNonInterleaving Γ` / `FugueForwardNonInterleaving Γ`
  quantified over `FugueReach`-reachable configurations. Strict reading
  throughout, per adaptation decision 3.
- **Proved, kernel-clean**:
  - `fugue_not_maximally_noninterleaving`: the condition-(3) refutation
    on the two-front-inserts trace, as a reachable-configuration
    counterexample (`¬ FugueMaximallyNonInterleaving unaryCode`).
  - `fugue_backward_gap`: the Figure-7 trace violates condition (2) with
    the Lemma-5 exception refuted pointwise, so the refutation is not an
    artifact of the tiebreak clause.
  - `fugue_two_runs_no_interleave`, its run corollary
    `fugue_concurrent_runs_no_interleave`, and the reachable-configuration
    instantiation `fugue_reachable_runs_no_interleave`: candidate (a)'s
    kernel half, from `sided_fold_subtree_convex` plus prefix
    incomparability of the run heads.
  - `fugue_forward_run_chains`: forward Fugue runs chain (the policy
    half, forward case).
  - `fugueReach_inv` / `fugueReach_chain_gen`: reachable knowledge is
    chain-generated in exactly the honesty layer's `chain_gen` shape, so
    the fold theorems apply to every reachable state.
  - `schainBefore_snoc_newest`: the kernel lemma for the backward gap
    (extending a chain by a newest R-entry preserves display precedence).
- **Stated but not proved** (as `def`s, no sorries):
  `FugueForwardNonInterleaving` (condition (1); Python-clean, believed
  true; a proof needs the display-to-tree-traversal theory, see gap G2).
- **Gaps, honestly**:
  - G1 (backward-run chaining): "the successor of the fixed anchor is the
    previously minted run element" (newest-mint adjacency). The kernel
    piece is proved (`schainBefore_snoc_newest`); what remains is the
    bridge from `succOf`'s fold-of-keys argmax to `schainBefore` facts
    over the minted log, an invariant-threading development estimated at
    200-300 lines. Until then, backward runs enter
    `fugue_concurrent_runs_no_interleave` through the `RunChains`
    hypothesis, which the SPOT traces discharge concretely.
  - G2 (condition (1) as a theorem): needs a characterization of "the
    first display element after A" as a tree walk (the paper's Lemma 7/8
    layer). This is new kernel theory, orthogonal to the refuted full
    statement.
  - G3 (concurrency to prefix-incomparability): concurrent run heads have
    prefix-incomparable chains. The telescoping argument is in section 3;
    `fugueReach_inv` provides the invariants; the remaining glue is a
    per-trace fact in the current SPOTs.

## 7. Verdict for task #84

The right positive statement for THIS policy is candidate (a) plus
condition (1), not full W-K maximal non-interleaving: the full statement
is FugueMax-specific (Theorem 10 makes it a unique-order pin), and the
sided embed's validated policy is Fugue-with-recency-tiebreak. If maximal
non-interleaving is ever wanted as a theorem here, the policy AND the
kernel's R-sibling order both change (reverse right-origin order with
lowest-ID ties), which is a new design to take through the battery first;
nothing in the present kernel obstructs it, since sides and order carry
through one `sEntryBefore` table.

## 8. The FugueMax variant: the positive twin (task #87a)

*Written 2026-07-17, after the section-7 verdict. The executable check is
`whiteboard/litmus/fuguemax_check.py`; the mechanization is
`Sal/MRDTs/RGA_Embed/SidedMax_ChainLex.lean` (the kernel variant) and
`Sal/ConditionedMRDTs/MRDT_Instances/SidedRGA/SidedRGA_FugueMax.lean`
(the policy, the adapted statement, the proofs). Paper reference:
Definition 6 and Theorem 9 of arXiv:2305.00583v3, re-extracted from the
paper on 2026-07-17.*

**Headline.** FugueMax is realized on the embedded-chain family as a
kernel VARIANT alphabet whose R entries carry an immutable right-origin
tag. The realization is machine-validated in Python (the gauntlet, seven
directed cases, 1500 randomized final states, all three W-K conditions
clean everywhere) and mechanized in Lean: the variant kernel's marker
theorem, unique decodability, and subtree convexity are kernel-clean, and
**condition (3) of Definition 4 is a THEOREM** at every replica of every
reachable FugueMax configuration
(`fuguemax_same_origin_low_first`, axioms {propext, Classical.choice,
Quot.sound}). This is the positive twin of section 3's first refutation:
the trace that refuted condition (3) for the Fugue-with-recency policy
(`[2, 1]`) displays `[1, 2]` under the variant, as a checked SPOT.
Conditions (1) and (2) are stated over the same reachability and remain
open in Lean (the section-6 gap G2, the display-to-traversal theory);
`fuguemax_max_noninterleaving_of_gaps` records that the full Theorem-9
statement reduces to exactly those two gaps plus the proved condition
(3).

### 8.1 What the paper's FugueMax is, precisely

Definition 6: FugueMax is identical to Fugue except that its tree
traversal visits right-side siblings in the REVERSE order of their right
origins, breaking ties by the lexicographic order of their IDs. The
insert rule is Fugue's (right child of the left origin when it has never
had a right child or there is no successor, else left child of the right
origin), but a right child additionally stores its right origin. Left
siblings keep Fugue's ascending-ID order. On Figure 7 the traversal must
produce the unique maximally non-interleaving order A X Y B C: X (right
origin C) precedes Y (right origin B) because C displays after B, whatever
the IDs of X and Y are.

### 8.2 The realization decision, settled on paper first

In this family the same-anchor sibling order is decided by the coordinate
alphabet, not by the generation policy. The candidate "mirror the R band
the way the L band already is" (same-anchor R-siblings oldest first,
lowest stamp first) realizes exactly the PAPER'S PLAIN FUGUE, ascending
IDs on both sides, and plain Fugue is what the paper proves is not
maximally non-interleaving. Concretely: mint Figure 7 in the adverse
order (Y before X, so Y gets the smaller stamp) and the mirrored band
displays A Y X B C, violating condition (2) at the pair (Y, B). The
`mirror` control in `fuguemax_check.py` witnesses this: output
`[3, 6, 7, 4, 5]` with the C2 violation `(6, 4)`. The conclusion is
forced: the R-sibling order depends on the right origin, which is not a
function of `(side, delta)`, so NO re-banding of the delta alphabet
realizes FugueMax. The entry itself must carry right-origin information,
and since coordinates are immutable at mint, the information is captured
at mint time and never consulted again.

The variant entry type (`FMEntry`): an L entry is `(L, delta)` as before;
an R entry is `(R, tag, delta)` where `tag` is the sort key of the
tombstone-visible successor at mint time, or `[0]` for the `end` origin.
The divergence order (`fmEntryBefore`): among R-siblings, smaller tag
first (a display-later right origin has a smaller key, so this is the
paper's reverse right-origin order; `end` is display-last, and `[0]` is
the least tag), ties by ascending delta (the paper's ascending-ID
tiebreak, since same-anchor deltas order as stamps); among L-siblings
ascending delta, unchanged; L before the node before R, unchanged.

### 8.3 The flat realization

The variant stays a one-comparison lexicographic order over a marker
alphabet. Bands: R-block symbols {0,1,2} < marker 3 < L band {4,5}. An
L block is the sided kernel's, unchanged: `(compl (enc d)).map symL`. An
R block is `fwTag tag ++ (compl (enc d)).map symR` where

    fw k = [(8 - k) / 3, (8 - k) % 3]

embeds each tag symbol as two R-band symbols, order-REVERSING on the tag
alphabet {0..5} (so a smaller tag yields a larger block, i.e. an earlier
display), and the delta code is complemented into the R band (so a
smaller delta yields a larger block: ascending IDs). Wellformedness of
tags (`TagOK`: the end tag `[0]`, or a real key, nonzero non-marker head,
marker-free bounded body, marker terminator) gives prefix-freedom of
distinct tags, which keeps the first difference of two R blocks inside
the tag region; block heads stay in {1,2}, coordinates never contain the
marker, and the whole `keyLt` machinery is reused unchanged. Closure
(`tagOK_key`): the key of any wellformed nonempty variant coordinate is
itself a wellformed tag, which is what lets minted keys feed back in as
the tags of later mints.

### 8.4 Hand-derived displays (all Python-checked and Lean SPOTs)

IDs are chosen ascending for the Figure-7 letters (A=3 < B=4 < C=5), so
the paper's target order is ID-compatible; the adverse twin then swaps
the mint order of X and Y to decouple the right-origin order from both
recency and IDs.

| case | FugueMax display | Fugue (section 4) display |
|---|---|---|
| two front inserts 1, 2 | `[1, 2]` (C3 holds) | `[2, 1]` (C3 refuted) |
| L19 backward | `[50, 30, 10, 61, 41, 21, 1]` | same (L band unchanged) |
| forward twin | `[1, 10, 30, 50, 21, 41, 61]` | `[1, 21, 41, 61, 10, 30, 50]` |
| mixed fwd/bwd | `[1, 50, 30, 10, 21, 41, 61]` | `[1, 21, 41, 61, 50, 30, 10]` |
| figure 7 (X=6, Y=7) | `[3, 6, 7, 4, 5]` = A X Y B C | Y-block first (C2 refuted) |
| figure 7 adverse (Y=6, X=7) | `[3, 7, 6, 4, 5]` = A X Y B C | not applicable |

The adverse Figure 7 is the decisive row: X displays first although Y has
both the smaller stamp and the smaller ID, because X's right origin C
displays after Y's right origin B. The strict-vs-lenient countermodel of
section 2 adapts by making the dead sibling the OLDER one (branch
`ins 2 after 1; ins 9 after 2; del 2` against `ins 5 after 1`): display
`[1, 9, 5]`, strict clean, lenient C1 fires.

### 8.5 Python results (run of record: `python3 fuguemax_check.py 500`)

* The embed_sided gauntlet: CLEAN (S1/S2 sequential rows included:
  sequentially the tombstone-visible successor rule never creates
  same-side siblings, so FugueMax = Fugue = the naive buffer on
  single-replica histories).
* NOT RGA-ordered, as expected by design: the forward twin gives
  `[1, 21, 41, 61, 10, 30, 50]` on the one-sided embed and
  `[1, 10, 30, 50, 21, 41, 61]` on FugueMax, so the all-R lockstep with
  the one-sided embed fails; this is the point, not a bug.
* All seven directed cases: displays match the hand derivations; strict
  C1/C2/C3 CLEAN on every one; the lenient reading fires only on the
  countermodel built for it.
* The mirror control: adverse Figure 7 violates C2, as derived.
* Randomized sweeps, strict reading, 3 shapes x 500 states (2-branch,
  3-branch, 3-branch two-epoch Figure-7 shaped): C1 = C2 = C3 = RUN = 0
  everywhere. The extra MIX statistic (0 everywhere) checks the
  structural lemma behind the Lean proof of condition (3): two minted
  elements with the same recorded (lo, ro) always sit in the same policy
  branch (same side, same tree parent).
* DAG PBT 120: convergence CLEAN.

### 8.6 The Lean mechanization

Kernel (`SidedMax_ChainLex.lean`, all kernel-clean): `fmEntryBefore` /
`fmChainBefore` with totality, inversion, strip, and asymmetry;
`fmChainBefore_display` and the variant marker theorem
`fmdisplay_iff_fmChainBefore` (the flat key comparison of wellformed
variant coordinates is exactly the FugueMax chain order); unique
decodability `fmCoordOf_inj`; subtree convexity `fm_subtree_convex`; the
tag-closure lemma `tagOK_key`; `fm_ext_after_is_R` (a subtree member
after the node extends it on the R side).

Policy (`SidedRGA_FugueMax.lean`): the generation layer (records with
mint-time lo, ro, and FugueMax chain; the display fold over the sided
instance's sorted-insert; `succOfM` as the argmax over all minted keys;
`mGenInsAfter` with the three mint branches; `MaxReach` with Lamport
inserts, deletes, pairwise sync). The reachability invariant
`maxReach_inv` (kernel-clean) carries, besides positivity, uniqueness,
and chain wellformedness, the two LINK clauses that decide condition (3):

* an R mint records `ro`, and its right origin is NOT an R-descendant of
  its left origin. Proved at the mint step from `hasRChildM = false` by a
  closure walk: knowledges are ancestor-closed (`chain_prefix_minted`),
  so an R-descendant of the anchor would exhibit a minted R-child of the
  anchor (`hasR_of_R_descendant`, with the parent pinned by the
  telescoping sums, no injectivity needed).
* an L mint's parent (= its recorded right origin) IS an R-descendant of
  its left origin. Proved at the mint step from `hasRChildM = true`: the
  witness R-child is a successor candidate displaying after the anchor,
  the argmax successor is therefore pinned between the anchor and that
  child (`foldl_maxKey_not_beaten`), and `fm_subtree_convex` plus
  `fm_ext_after_is_R` land it in the anchor's R-subtree
  (`succ_R_descendant`); the equal-key corner collapses by
  `fmCoordOf_inj`.

Condition (3) (`fuguemax_same_origin_low_first`, kernel-clean): same
recorded (lo, ro) forces the same mint branch, because an R record's
negative geometry clause contradicts an L record's positive one on the
same pair; same-branch records are siblings under one parent chain, and
the kernel divergence order puts the smaller stamp first (equal tags for
R-siblings since the recorded ro is equal; L-siblings by delta). Run
contiguity transports as in section 4:
`fuguemax_reachable_runs_no_interleave` via `fm_fold_subtree_convex`.
SPOTs (PASS and FAIL shaped, `native_decide`): every row of the 8.4
table, including both Figure-7 mint orders.

### 8.7 Honest gaps, and what moved on G1/G2/G3

Conditions (1) and (2) are `def`s over `MaxReach`
(`FugueMaxForwardNonInterleaving`, `FugueMaxBackwardNonInterleaving`),
Python-clean over 1500 randomized states, unproved in Lean: both need the
display-to-tree-traversal characterization (the paper's Lemma 7 and 8
layer), which is section 6's gap G2 and is not built here.
`fuguemax_max_noninterleaving_of_gaps` fixes the remaining obligation
exactly: those two statements imply the full adapted Theorem 9, with
condition (3) already discharged. What DID move on the G1/G3 front is the
technique: the `succOfM` argmax-to-chain-geometry bridge
(`foldl_maxKey_not_beaten` + convexity + `fm_ext_after_is_R` inside a
reachability invariant) is precisely the shape section 6's G1 asked for
at the Fugue file's `succOf`, executed here at the variant; porting it
back to the recency kernel's backward-run adjacency is now a transcription
job rather than an open design question. G2 remains the substantive open
item for both policies.

## 9. The traversal theory and the forward discharge (task #88)

*Written 2026-07-18. Executable check: `whiteboard/litmus/traversal_check.py`.
Mechanization: `Sal/MRDTs/RGA_Embed/Sided_Traversal.lean` (the kernel
interval form) and
`Sal/ConditionedMRDTs/MRDT_Instances/SidedRGA/SidedRGA_NonInterleaving.lean`
(the FugueMax condition-(1) discharge). Paper reference: Lemma 7, Lemma 8,
and the Theorem 9 proof of arXiv:2305.00583v3, re-read from the PDF on
2026-07-18, not from memory.*

### 9.1 The traversal, in two forms

The paper's Lemma 7 layer says: the list order of a forward
non-interleaving algorithm is a depth-first pre-order traversal of the
left-origin tree; Lemma 8(a) computes left origins by a walk up the
algorithm's own tree. On the embedded-chain family the algorithm's tree is
implicit in the chains, and the marker theorems
(`sdisplay_iff_schainBefore`, `fmdisplay_iff_fmChainBefore`) already state
that the display order IS the in-order rule on chains: L-subtrees, node,
R-subtrees, siblings by the kernel's entry order. So the traversal theorem
splits into two deliverables with different natural homes.

**The executable form** lives in Python (`traversal_check.py`): build the
tree from the minted chains (each node's parent is its chain minus the
last entry), emit the recursive in-order traversal with the kernel's
sibling orders (plain sided: L ascending stamp then node then R descending
stamp; FugueMax: L ascending stamp then node then R by reverse right
origin, ties ascending stamp), and check that the emission equals the
descending-key sort of all minted elements, dead included, on the directed
cases and randomized sweeps of both policies.

**The interval form** lives in Lean and is what the discharges consume.
For a prefix p, the subtree of p is the display interval around p:
`schain_subtree_convex` / `fm_subtree_convex` give contiguity (already in
the kernels), and the new `Sided_Traversal.lean` lemmas pin the sides:
an extension displays after the node iff it is R-headed and before iff it
is L-headed (`schain_ext_after_is_R`, `schain_ext_before_is_L`,
`schain_ext_side`), shared prefixes strip and lift
(`schainBefore_append_strip`, `schainBefore_append_lift`), and the chain
order is transitive on positive chains (`schainBefore_trans`, via the
marker theorem and `keyLt_trans`). A recursive emission function in Lean
was designed and deliberately not built: every consumer below needs only
the interval lemmas, and the emission adds a fueled recursion over the
chain set with no downstream client. The Python twin carries the
executable statement instead.

### 9.2 Lemma 8(a) in chain form: the loShape invariant

The bridge from recorded left origins to chain geometry is the paper's
walk-up rule, which in chain form is a single shape statement.

**loShape**: every minted element x satisfies
`chain(x) = chain(lo(x)) ++ (R-entry) :: ls` with `ls` all-L.

R mints satisfy it with `ls = []` (the existing LinkR clause). L mints
need the new content: the tombstone-visible successor n of an anchor a
with an R-child satisfies `chain(n) = chain(a) ++ (R-entry) :: all-L`.
The existing `succ_R_descendant` gives the decomposition with an
unconstrained rest; the all-L upgrade is an argmax argument: if the rest
contained an R entry, the node just above that entry (minted, by
ancestor closure `chain_prefix_minted`) would display after a and before
n, beating the argmax (`succOfM_max`). Contradiction. The L mint then
extends n by one L entry, preserving the shape. Under the Fugue policy
the same statement holds by the same argument (the sibling order is
never consulted), but the Fugue file's `GInv` carries no link clauses at
all, so the entire link layer would have to be built there first; see
9.5.

### 9.3 The first-after descent, and the forward discharge

The paper's condition-(1) proof identifies B with the first node the
traversal visits among A's right descendants. The chain replay avoids
naming that node: it is a descent on the left-origin walk.

**Descent lemma**: if c is minted and `chain(c) = chain(A) ++ (R-entry)
:: ext`, then some minted D has `lo(D) = A` and displays before or equal
to c. Proof by strong induction on chain length: loShape(c) writes
`chain(c) = chain(lo(c)) ++ (R-entry) :: all-L`. Both `chain(A)` and
`chain(lo(c))` are prefixes of `chain(c)`, hence comparable. Equal:
telescoping sums force `lo(c) = A`, take D = c. `chain(lo(c))` shorter
than `chain(A)`: then the R entry that A's decomposition places inside
the all-L tail of lo(c)'s decomposition is an L entry, contradiction, so
this case is vacuous. Longer: `chain(lo(c))` extends `chain(A)`
R-headedly, lo(c) displays before c (it is an R-ancestor), recurse on
lo(c).

**Forward non-interleaving** (`forwardNIM_of_inv`): given lo(B) = A with
B display-earliest among elements with left origin A (strict reading),
loShape(B) makes B an R-extension of A, so A displays before B. Any live
c strictly between lands in A's subtree by convexity, is R-headed by the
side lemma, and the descent produces a minted D with lo(D) = A
displaying before or equal to c, hence strictly before B; minimality
says B displays before D; `keyLt_trans` plus `keyLt_irrefl` close the
cycle. Nothing else is needed: no traversal emission, no causal
reasoning, no liveness of the in-between witness beyond mintedness.

Mechanized as `fuguemax_forward_ni : FugueMaxForwardNonInterleaving Γ`,
concluding the stated def, with the supplementary reachability invariant
`maxReach_inv2` carrying exactly the one new clause (the all-L successor
shape for L mints, `SLC`), transported through inserts, deletes, and
syncs the same way the main bundle is. Full Theorem 9 for the variant
now reduces to the backward condition alone
(`fuguemax_theorem9_of_backward`).

### 9.4 What breaks on dishonest states

loShape is a generation-discipline fact. A state that stores an L entry
whose parent is not the anchor's successor, or an R entry minted while
the anchor already had an R-child, displays fine (the kernel total order
does not care) but breaks the walk-up rule: the descent then produces a
D whose recorded lo is wrong, and condition (1) genuinely fails (mint
c as a deep L-descendant with a forged lo and it sits between A and its
first child with no element with lo = A before it). The honesty clause
that excludes this is precisely the MaxReach mint rule: side and parent
come from `mGenInsAfter`, never from the op payload.

### 9.5 The Fugue-policy forward condition: deferred, with the cost known

`FugueForwardNonInterleaving` (the plain sided kernel, recency
tiebreak) is believed true with the SAME proof: the argmax argument,
the descent, and the discharge never consult the sibling order. What is
missing is infrastructure, not mathematics: the Fugue file's `GInv` has
no link clauses, so the LinkR/LinkL layer, the closure walk
(`chain_prefix_minted`), `chain_head_R`, and the transports would all
have to be rebuilt over `FugueReach` (roughly the 900-line §2 of the
FugueMax file) before the ~350 lines above replay. Deferred as a
transcription job; no open design question remains for it.

### 9.6 The backward condition: design state, honest

Condition (2) for FugueMax remains open. The design so far, validated on
paper against the paper's own proof:

* Case lo(A) = lo(B), A an L mint: LinkL makes A a child of B, so A
  displays before B, and the in-between analysis splits by convexity at
  B. Later L-siblings of A are refuted by A-latest (the sibling's parent
  is B by chain cancellation, so it too has right origin B and displays
  after A, contradiction). In-betweens inside A's own R-subtree need the
  paper's first-R-child argument, which needs TWO further mint-time
  clauses not yet carried: (NR) an R mint with recorded end origin has an
  all-R chain (else its parent's ancestors, minted by closure, would have
  been successor candidates); and a stable form of "the first R-child of
  A saw B as its successor". Both are provable at the mint step by the
  same closure technique; neither is in the tree yet.
* Case lo(A) = lo(B), A an R mint: impossible. The existing LinkR
  geometry clause says B is not an R-descendant of lo(A); loShape(B)
  says it is.
* Case lo(A) ≠ lo(B): A is an R mint (an L mint forces equal left
  origins: both loShape(B) and the strengthened LinkL decompose
  chain(B) at its LAST R entry, so the two lo's chains coincide and
  telescoping sums equate them). The tag of A's R entry is B's full key,
  which yields a kernel-level fact with no analogue in the paper: B
  cannot lie in A's subtree, because the tag embeds B's key in two
  symbols per symbol and lengths collapse. The exception witness
  construction (the paper picks a causally minimal in-between element)
  is the genuinely open part: causal minimality has no invariant-level
  replay yet, and the candidate replacement (walk to the subtree root of
  the in-between element below lo(A)) is designed but not validated.

The two-clause extension plus the exception construction is the honest
residue of Theorem 9. Everything else (condition 3, condition 1, the
reduction) is kernel-clean.

### 9.7 The backward condition: a refutation of the live-witness reading, and the exception-witness construction (task #92 item 1)

*Written 2026-07-18, design phase only (pen and paper, then Python; no
Lean here). Executable check: `whiteboard/litmus/fuguemax_backward_check.py`
(run of record: `python3 fuguemax_backward_check.py 1000`). The paper's
Definition 4, Lemma 5, and the Theorem 9 Condition (2) proof were
re-extracted from the arXiv:2305.00583v3 PDF on 2026-07-18, not from
memory.*

**Headline.** Two results. First, a refutation: the Lean statement
`BackwardExceptionM` as it stands requires the Lemma-5 exception witness
C to be LIVE, and that reading is FALSE on this realization. The paper's
own Figure-7 execution followed by one delete is a countermodel, and the
randomized sweeps confirm it on three further states once branches are
allowed to delete (the section-8.5 sweeps never were: their branches are
insert-only, which is why this survived until now). The corrected
statement lets C range over all minted elements, tombstones included,
which is the paper's own quantification. Second, the construction: for
the corrected statement, the causal-minimality step of the paper's proof
is replaced by a state-definable exception witness, backed by three new
mint-time invariant clauses (sharpening the two forecast in 9.6). The
construction is validated on 12 directed cases and 4500 randomized
states: the corrected condition, the witness, and the clauses are clean
everywhere, and the witness function reproduces the paper's own C on the
Figure-7 family.

#### 9.7.1 The paper's condition, and the exact step being replaced

Definition 4, condition (2), verbatim:

> "(Backward non-interleaving, with exceptions) If B is the right origin
> of A, and A appears later in the list than any other element that has
> B as right origin, then A and B are consecutive list elements, unless
> Theorem 5 below says otherwise."

The exception (the paper's Lemma 5, quoted in full in section 1): A and
B have different left origins, and there is a C in the current list
state with A.leftOrigin < C < B such that C is not a descendant of
A.leftOrigin in the left-origin tree.

The Theorem 9 Condition (2) proof splits on whether the left origins are
equal. The equal case is closed by tree geometry. The unequal case must
EXHIBIT the C of the exception, and the paper does it causally:

> "Since A and B are not consecutive, there exist one or more elements
> in between A and B; take C to be an in-between element that is not
> causally later than any other element between A and B."

Causal minimality is then consumed three times: a descendant of a
sibling is excluded ("otherwise the sibling would be a causally prior
element between A and B"), a descendant of A is excluded ("C's right
origin is an in-between element that is causally prior to C,
contradicting our choice of C"), and a sibling of A with a different
right origin is excluded ("C's right origin is a causally prior
in-between element, again contradicting our choice of C"). This
minimal-element selection is the step our reachability formulation
cannot replay: the invariant carries per-record facts about the current
knowledge, not a well-founded causal order to minimize over. The
replacement below selects the witness by chain geometry instead, and the
three new invariant clauses are exactly the mint-time facts the paper's
three exclusions extracted from causal priority.

#### 9.7.2 The refutation: the witness must be allowed to be dead

The current Lean definition (`SidedRGA_FugueMax.lean`):

    def BackwardExceptionM Γ K A B : Prop :=
      mLoOf K A ≠ mLoOf K B ∧
      ∃ C ∈ mMintedIds K, mLive Γ K C ∧
        mBefore Γ K (mLoOf K A) C ∧ mBefore Γ K C B ∧
        ¬ mLoDesc K C (mLoOf K A)

The `mLive` conjunct was our adaptation decision, made when everything
in the harness happened to be alive. It does not survive deletes.
Countermodel: run the paper's Figure-7 execution exactly as in 8.4 (the
paper's letters map to ids 3, 4, 5 for the three roots and X = 6 with
recorded origins (lo, ro) = (3, 5), Y = 7 with (3, 4); display
`[3, 6, 7, 4, 5]`), then delete 4. The visible document is
`[3, 6, 7, 5]`. Take the condition-(2) pair (A, B) = (6, 5), the
paper's (X, C):

* the premises hold: 6 and 5 are live, `ro(6) = 5`, and 6 is the ONLY
  minted element with right origin 5, so it is trivially display-last
  among them (strict reading, tombstones included);
* they are not consecutive: 7 is live and sits between;
* the exception's first half holds: `lo(6) = 3 ≠ 0 = lo(5)`;
* but no LIVE witness exists: the only elements strictly between
  `lo(6) = 3` and 5 in the full order are 6, 7 (both have recorded left
  origin 3, hence are descendants of 3 in the left-origin tree) and the
  dead 4.

So `BackwardNIExcM` as stated is false at this reachable configuration.
The witness the situation wants is the tombstone 4: it is exactly the C
the paper's proof produces for this execution. The paper's Lemma 5
quantifies C over "the current list state", and its list state contains
every inserted element (deletion only overwrites the value with a
tombstone marker; right origins are even defined via "the list including
tombstones"). The corrected definition therefore drops the one conjunct
`mLive Γ K C`, and nothing else:

    def BackwardExceptionM Γ K A B : Prop :=
      mLoOf K A ≠ mLoOf K B ∧
      ∃ C ∈ mMintedIds K,
        mBefore Γ K (mLoOf K A) C ∧ mBefore Γ K C B ∧
        ¬ mLoDesc K C (mLoOf K A)

Two remarks on the corrected reading. First, it is strictly
paper-faithful and strictly weaker as a non-interleaving guarantee: a
pair excused by a dead witness is a pair the visible document may
interleave. That is forced, not chosen: the countermodel shows the live
reading is simply not a theorem of this algorithm (and, since the
realization is the paper's algorithm on these traces, of FugueMax
itself; the paper never claimed it, its C was never required visible).
Second, the conclusion `mConsecutive` KEEPS its live reading (no live
element strictly between): that is the visible-document property and it
is the one the corrected statement proves. The refutation is
machine-checked in the new harness on both Figure-7 mint orders plus two
further directed families (the beta0 cases below, where the dead witness
is not a root sibling but a concurrent run element), and fired on 3 of
4500 randomized states once branch deletes were enabled. The historical
`check_wk` in `fugue_noninterleave_check.py` implements the live reading
and is left untouched; its section-8.5 verdicts stand for the states it
saw, but its C2 clause should not be quoted for delete-bearing traces.

#### 9.7.3 The mint-time invariant clauses, sharpened

Notation, all native to `SidedRGA_FugueMax.lean`: ch(x) = `mChainOf K x`
(the immutable birth chain; ch(0) = []), key(x) = `mKey Γ K x`, x < y is
the strong-list display order `mBefore Γ K x y` (tombstones included; 0
= start is before every minted element because every minted chain is
R-headed, see (RHead) below), lo/ro are the recorded origins, and
Subtree(p) = the minted x with ch(p) a prefix of ch(x). An R mint is a
record with op `ins a Side.R` (its chain is ch(a) plus one tagged R
entry, and a = lo); an L mint has op `ins n Side.L` (chain ch(n) plus
one L entry, n = the parent = the recorded ro). The chain shape
determines the branch: the last entry's side is the op's side, so a
minted element whose chain is ch(P) plus one L entry has a record with
op `ins P Side.L` and hence ro = some P (LinkL), and dually for R. This
record-shape inversion is used silently below.

Section 9.6 forecast two further clauses: (NR), the all-R chain of an
end-origin R mint, and a stable form of "the first R-child of A saw B as
its successor". The construction actually needs THREE clauses, all on R
mints, and (NR) turns out to be unnecessary. For every R-mint record g
with anchor a = g.lo:

* **(R0)** if a = 0 then g.ro = none. (A root-anchored R mint happens
  only in a knowledge with no minted elements: any minted element's
  chain is R-headed, so by ancestor closure the root would have a minted
  R-child and the policy would take the L branch. Hence there was no
  successor to record.)
* **(RSA)** if g.ro = some n then a < n in display. (The successor
  candidates are filtered by "displays after the anchor" at mint time;
  keys are immutable, so the comparison persists verbatim.)
* **(RSuccL)** if a ≠ 0 and a's record is an L mint with parent P: then
  g.ro = some n, and either n = P, or there is a minted s with ch(s) =
  ch(P) ++ [L entry], a < s in display, and ch(s) a prefix of ch(n).
  (In words: an R mint under an L-minted anchor records, as successor,
  the anchor's parent or an element inside the subtree of a LATER
  L-sibling of the anchor; that sibling s is the stable witness.)
* **(RSuccR)** if a ≠ 0 and a's record is an R mint with recorded
  ro = some m: then g.ro = some n with key(n) ≥ key(m), that is, n = m
  or n displays before m. (The anchor's own recorded successor m was
  minted in the minter's knowledge, by the anchor's LinkR clause
  holding there, and displayed after a; the argmax successor therefore
  displays no later than m.)

Two derived facts, no new clauses: **(RHead)** every minted chain is
R-headed (strong induction on chain length through loShape: the bottom
block extends ch(0) = [] by an R entry, and higher chains inherit their
head), and the L-mint counterpart of (RSA) (an L mint's parent displays
after its left origin) is already a consequence of LinkL + SLC via the
kernel's extR display lemma.

Why these are provable AT THE MINT STEP, over the minter's knowledge
K_D, in Lean-ready detail. (R0): as in the parenthesis, from
`hasRChildM K_D 0 = false` plus (RHead) plus `chain_prefix_minted`.
(RSA): unfold `succCandM`; the a ≠ 0 branch filters by
`keyLt (key n) (key a)`; the a = 0 branch is (R0)-vacuous. (RSuccR): m
is minted in K_D by the anchor's LinkR clause there, a < m by the
anchor's (RSA) there, so (m, key m) is a successor candidate and
`foldl_maxKey_not_beaten` pins key(n) ≥ key(m). (RSuccL): P is minted in
K_D with a < P (LinkL of the anchor plus extR), so the candidate set is
nonempty and n exists; if n ≠ P then key(n) > key(P) by the argmax
against candidate P plus key injectivity (`fmCoordOf_inj`), so
a < n < P; convexity of Subtree(P) (`fm_subtree_convex`, corners a and
P) puts n in Subtree(P), the before-side lemma makes its extension
L-headed, and the L-child of P on n's path (minted by
`chain_prefix_minted`) is the witness s; s ≠ a because s = a would put
n inside Subtree(a) after a, exhibiting by closure a minted R-child of
a, against the R branch's `hasRChildM K_D a = false`; a < s because
s < a would trap a inside Subtree(s) by convexity and force s = a by
chain lengths and telescoping sums. Every ingredient is a fact about K_D, which satisfies
the full invariant bundle by induction, so no appeal to "what the minter
had seen" beyond the knowledge itself is ever made. This is the
invariant-level replacement for causal minimality: a universal fact
about the mint-time knowledge does not transport, but an EXISTENTIAL
witness (the sibling s, the origin m) does, because minted records,
chains, and keys are stable under knowledge growth.

#### 9.7.4 Step 0 and the case dichotomy

Fix K with the invariant bundles and a premise pair: A, B minted and
live, ro(A) = some B, and LAST(A, B): every minted D ≠ A with ro(D) =
some B has D < A (the strict reading, tombstones included).

**Step 0: A < B, always.** If A is an L mint, its parent is B (LinkL, ro
= parent) and an L extension displays before its node. If A is an R mint
with anchor a: a ≠ 0 by (R0), a < B by (RSA); if B < A held, then a < B
< A with a and A in Subtree(a) would trap B in Subtree(a) by convexity,
R-headedly by the after-side lemma since a < B, contradicting the LinkR
geometry clause (the recorded successor is not an R-descendant of the
anchor; B = A itself is the degenerate instance of the same
contradiction). So A < B, and B is not in Subtree(a) at all (an L-headed
extension would put B before a), hence B displays after EVERYTHING in
Subtree(a): x in Subtree(a) with B < x would trap B by convexity between
a and x.

**Dichotomy: A is an L mint iff lo(A) = lo(B).** If A is an L mint, SLC
gives ch(B) = ch(lo A) ++ R entry :: all-L, and loShape(B) gives ch(B) =
ch(lo B) ++ R entry :: all-L; both decompositions cut ch(B) at its LAST
R entry, so the prefixes coincide and telescoping sums give lo(A) =
lo(B). If A is an R mint: loShape(B) makes B an R-descendant of lo(B),
and LinkR(A) says B is NOT an R-descendant of lo(A); so lo(A) ≠ lo(B).
This dichotomy is exactly the paper's split "(i) false / (i) true", and
it delivers the exception's first conjunct for free in the R case.

#### 9.7.5 The construction

**The L case: consecutive outright.** Let A be an L mint (parent B) and
suppose some live c has A < c < B; derive a contradiction. c is minted
(live implies minted). A and B are in Subtree(B), so convexity puts c in
Subtree(B), before B, hence with an L-headed extension (before-side
lemma). Let S be the L-child of B on c's path (ch(S) = ch(B) ++ [first
entry of the extension], minted by ancestor closure). Three subcases.
If S < A: convexity (S < A < c, with S and c in Subtree(S)) traps A in
Subtree(S), so ch(S) is a prefix of ch(A); both are ch(B) plus one L
entry, so S = A, contradiction. If S ≠ A and not S < A: totality gives
A < S; S is an L mint with parent B by record-shape inversion, so ro(S)
= some B, and LAST forces S < A, contradiction. So S = A, c is a proper
R-descendant of A (its extension over A is R-headed by the after-side
lemma since A < c), and the R-child D of A on c's path is minted, an R
mint with anchor A. Now consume **(RSuccL)** at D (anchor A is an L
mint with parent B): ro(D) = some n, and either n = B, in which case D
is a minted element ≠ A with right origin B and A < D (extR),
contradicting LAST; or a witness s exists with ch(s) = ch(B) + one L
entry and A < s, in which case s is an L mint with parent B (inversion
again), ro(s) = some B, s ≠ A, A < s, contradicting LAST. So no live
in-between exists: A and B are consecutive. Note what happened: the
paper's "let D be a right child of A such that A did not have any other
right child when D was inserted" became a clause about EVERY R-child of
A, so the concurrent-first-children subtlety (several D each minted
believing A childless) never arises.

**The R case: the witness.** Let A be an R mint, a = lo(A) ≠ 0 (by (R0)
plus ro(A) = some B), lo(A) ≠ lo(B) by the dichotomy, and let c be live
with A < c < B. The witness function, deterministic in the state:

1. **(alpha)** If ch(a) is NOT a prefix of ch(c): C := c.
2. Otherwise c is in Subtree(a), after a, so the entry of ch(c) at
   position |ch(a)| is an R entry; let E be the minted node at ch(a) ++
   [that entry] (an R mint with anchor a, sibling of A or A itself).
   * **(beta1)** If E ≠ A: C := the recorded ro(E).
   * **(beta0)** If E = A: c is a proper R-descendant of A; let D be
     the R-child of A on c's path and n_D its recorded ro (some, by
     (RSuccR) at D, since D's anchor A is an R mint with a recorded
     successor).
     * **(beta0-direct)** If ch(a) is not a prefix of ch(n_D): C := n_D.
     * **(beta0-ladder)** Else let E' be the R-child of a on n_D's
       path; C := the recorded ro(E').

Correctness, case by case, with the consumed clauses.

*(alpha)*: lo(A) < C: a < A < c. C < B: given. Not a lo-descendant:
loShape makes ch(lo x) a prefix of ch(x) for every minted x, so
lo-iteration only visits prefixes; if some iterate of c reached a, ch(a)
would be a prefix of ch(c), excluded. (This prefix lemma, loDesc to
prefix, is the only fact about `mLoDesc` the whole proof needs.)

*(beta1)*: E ≠ A, and A < E: otherwise E < A < c with E, c in
Subtree(E) traps A, forcing ch(E) prefix of ch(A) and E = A. A and E are
R-siblings under a, so the kernel divergence order at their R entries
gives: tag(A) < tag(E) lexicographically, or equal tags with a smaller
delta on A's side. The tags are, by LinkR at each record, tagK of the
recorded origins: tag(A) = key(B) (a real key, B minted), tag(E) = [0]
if ro(E) = none, else key(ro E). The end tag [0] is lexicographically
below every real key (real tags have a nonzero, non-marker head), so
tag(A) ≤ tag(E) rules ro(E) = none out: ro(E) = some n_E, tag(E) =
key(n_E). If the tags are EQUAL: key(n_E) = key(B) forces n_E = B (key
injectivity), so E is a minted element ≠ A with right origin B and
A < E, contradicting LAST; the tie case is vacuous. So key(n_E) >
key(B) strictly, i.e. n_E displays before B and n_E ≠ B. Now place n_E:
a < n_E by (RSA) at E; n_E is not an R-descendant of a by LinkR at E,
and not an L-descendant (those display before a), so n_E is outside
Subtree(a) and hence displays after all of it, in particular A < n_E.
Summary: C = n_E is minted (LinkR at E), a < C, C < B, and ¬loDesc by
the prefix lemma since ch(a) is not a prefix of ch(n_E).

*(beta0)*: D is an R mint with anchor A, and A is itself an R mint with
ro(A) = some B, so **(RSuccR)** applies at D: ro(D) = some n_D with
key(n_D) ≥ key(B). Equality would give n_D = B, making D a minted
element ≠ A (a proper descendant) with right origin B and A < D,
against LAST; so key(n_D) > key(B), n_D displays before B, n_D ≠ B. By
(RSA) at D: A = lo(D) < n_D. By LinkR at D, n_D is not an R-descendant
of A, and A < n_D rules out L-descendants, so n_D is outside
Subtree(A). If n_D is also outside Subtree(a) *(beta0-direct)*: C = n_D
is minted, a < A < n_D < B, ¬loDesc by the prefix lemma. If n_D is
inside Subtree(a) *(beta0-ladder)*: its entry above ch(a) is R (n_D is
after a), the R-child E' of a on its path is minted, E' ≠ A (else n_D
would be in Subtree(A)), and E' with n_D in its subtree is EXACTLY the
beta1 configuration with n_D in place of c; note beta1 nowhere used
liveness of c. Replaying it: A < E', the tie tag(E') = key(B) is a LAST
contradiction, and otherwise C = ro(E') is minted, a < C < B, outside
Subtree(a), ¬loDesc. The construction terminates in at most two
unfoldings; there is no recursion.

Why a witness EXISTS at every reachable violating configuration, in one
sentence: the R-children of lo(A) at or after A, and the R-children of A
itself, all carry recorded right origins whose keys are pinned at or
above key(B) by the sibling order and the two RSucc clauses, and the
first such origin that escapes Subtree(lo A) (at worst two steps out) is
an element strictly between lo(A) and B that the left-origin walk from
anywhere inside Subtree(lo A) can never reach.

#### 9.7.6 The induction through ins, del, sync

The three clauses are per-record predicates over (K, g), exactly the
shape of `SLC`, and the supplementary reachability theorem (call it
`maxReach_inv3`, carrying `RBk Γ K g` = (R0) ∧ (RSA) ∧ (RSuccL) ∧
(RSuccR) for every g in every G q) transports the same way
`maxReach_inv2` does:

* **ins**: old records keep their clauses by a `slc_transport`-style
  lemma: every ingredient (mintedness of n, m, s; chains; keys; the
  display comparisons; the prefix conditions) is stated about ids that
  are 0 or minted in the old knowledge, so `mChainOf_append_stable`
  rewrites them across the append. The FRESH record is the real work:
  the four mint-step proofs of 9.7.3, each over the pre-step knowledge
  G r, which satisfies KInv (`maxReach_inv`) and SLC (`maxReach_inv2`)
  by the outer induction. The (RSuccL)/(RSuccR) hypotheses refer to the
  ANCHOR's record, which lives in G r, so its LinkR/LinkL/SLC clauses
  are available there directly.
* **del**: the appended record is not a mint, every clause is vacuous
  on it, and chains are untouched (`mChainOf_snoc_del`).
* **sync**: records come from one of the two sides; transport with the
  `hchainL`/`hchainR` chain-agreement facts, which rest on cross-replica
  uniqueness (`MInv.cross`), verbatim as in `maxReach_inv2`'s sync case.

The discharge theorem then reads: for K with KInv, the SLC bundle, and
the RBk bundle, `BackwardNIM Γ K` holds (the corrected `BackwardNIExcM`
of 9.7.2), by the case tree of 9.7.4 and 9.7.5; and
`fuguemax_backward_ni : FugueMaxBackwardNonInterleaving Γ` follows at
every replica of every reachable configuration, closing Theorem 9 via
the existing reduction `fuguemax_theorem9_of_backward`.

#### 9.7.7 Python validation (run of record: `python3 fuguemax_backward_check.py 1000`)

The harness checks, per state: (a) the backward condition under BOTH
witness readings; (b) the witness function of 9.7.5 on EVERY premise
pair that is not live-consecutive and EVERY live in-between c of that
pair, verifying the returned C is minted, strictly between lo(A) and B,
and not a left-origin-tree descendant of lo(A), and additionally that
the pair has an R-mint A with distinct left origins (the L case must
never be non-consecutive); (c) the clauses (R0), (RSA), (RSuccL),
(RSuccR) on every minted record, plus the loShape re-check imported from
`traversal_check.py`.

* Directed, 12 cases: Figure 7 in both mint orders, each also with the
  element 4 deleted; L19 backward; the forward twin; the dead-sibling
  pair from 8.4 and its del-9 variant; the beta0-direct and beta0-ladder
  constructions (three concurrent root inserts 1, 2, 3; A = 4 an R-child
  of 1 minted in view {1, 3} so ro(4) = 3; then an R-child of 4 minted
  in a wider view, whose recorded origin either escapes Subtree(1)
  directly, display `[1, 4, 5, 2, 3]`, or lands in the subtree of the
  later sibling 6, display `[1, 4, 7, 6, 2, 3]`), each also with the
  witness 2 deleted. All 12: corrected reading, witness, and clauses
  CLEAN; the live reading fires on exactly the four delete variants
  built to refute it (fig7 + del 4 twice, beta0 + del 2 twice) and
  nowhere else.
* Randomized: 3000 delete-enabled states (2-branch, 3-branch, and
  Figure-7-shaped two-epoch, deletes at rate 0.35 inside concurrent
  branches; this is the shape 8.5's sweeps lacked) plus 1500 insert-only
  states re-using `fuguemax_check.random_run_scenario`. Hard failures:
  0 of 4500. Live-reading violations: 3 states, all in the two-epoch
  delete shape.
* Witness routes exercised: alpha 253, beta1 22, beta0-direct 2,
  beta0-ladder 2, dead witness 8 (the five directed pair-instances plus
  the three randomized states). The beta0 routes were reached only by
  the directed constructions; random sweeps of this size never produce
  them, which is why they were built by hand.
* Oracle self-test (scratchpad, PASS+FAIL discipline): corrupting
  ro(7) to none on the beta0 ladder trips both (RSuccR) and the witness
  function; forging ro(6) = 3 does NOT trip anything because it breaks
  the LAST premise instead, which is precisely the tie-case reasoning
  of beta1; forging A's side to L trips the L-case check; removing the
  witness 2 from the record set trips the corrected backward check
  itself.

#### 9.7.8 Lean-readiness, and the honest bill

What the mechanization needs, in dependency order:

1. **The definition edit**: drop `mLive Γ K C` from
   `BackwardExceptionM`. One line; `BackwardNIExcM`,
   `FugueMaxBackwardNonInterleaving`, and the reduction re-elaborate
   unchanged. Widening the witness domain weakens the overall backward
   statement (more pairs are excused); the change is forced by the
   9.7.2 countermodel and matches the paper's quantification, so this
   is a corrected goal, not a silently renamed one.
2. **Kernel additions** (`SidedMax_ChainLex.lean` consumers, likely one
   small file): the before-side lemma (`fm_ext_before_is_L`, the L twin
   of `fm_ext_after_is_R`), and a divergence inversion for same-parent
   R-siblings (from `fmChainBefore (p ++ [R t d]) (p ++ [R t' d'] ++ u)`
   read off tag-lex-or-tie-delta; the pieces exist as `fmEntryBefore`
   inversion + strip). Both are marker-theorem bookkeeping, no new
   ideas.
3. **Record-shape inversion**: a minted x with ch(x) = ch(P) ++ [one
   entry] has op `ins P side-of-that-entry`, hence the matching
   LinkR/LinkL clause; provable from `mRecOfId` + the wf sum + the two
   link clauses (the wrong side gives the wrong last entry). Used five
   times; worth a lemma.
4. **The supplementary bundle** `RBk` + `maxReach_inv3`, structured
   exactly like `SLC` + `maxReach_inv2` (transport lemma + three-case
   induction; the mint case proves (R0), (RSA), (RSuccR) cheaply and
   (RSuccL) by the 9.7.3 argument, which is `succ_R_desc_allL`-grade
   work: argmax + convexity + closure). This is the right home; folding
   the clauses into `LinkR`/`KInv` would touch every existing transport
   and re-open the proved bundle for no benefit (the 24-VC lesson: do
   not edit clauses that are already load-bearing).
5. **The prefix lemma** loDesc-implies-chain-prefix (induction on the
   iterate count through loShape; only this direction is needed).
6. **The discharge** `backwardNIM_of_inv`: the 9.7.4/9.7.5 case tree.
   Comparable in size to `forwardNIM_of_inv` plus its two helper
   sections; the L case and beta1 are the bulk; beta0 reuses beta1 as a
   lemma on a minted (not necessarily live) in-between, so state beta1
   accordingly.

Expected hard points: the (RSuccL) mint-step proof (the successor
argmax against a candidate it did not pick, plus the two convexity
traps; everything else in the file has a template); the record-shape
inversion's uniqueness bookkeeping; and keeping the beta1 lemma stated
over minted in-betweens so beta0-ladder can call it. Nothing here needs
the traversal emission, causal pasts, or any history-indexed structure:
the paper's causal minimality is fully absorbed by three existential
mint-time clauses and a two-step chain walk, which was the design
question this section set out to answer. Estimated size: kernel ~150
lines, bundle ~400, discharge ~450, SPOTs (the four delete variants of
9.7.7 as PASS+FAIL pairs, witness values pinned) ~120.

### 9.7.9 Errata from the mechanization pass

Two corrections to the design record, found while executing the bill of
9.7.8 (the mechanization is `SidedRGA_Backward.lean`; recorded here so
this note stays the source of truth):

1. Section 9.7.3 cites "(RSA) at the anchor" for a < m in the (RSuccR)
   case. The anchor's (RSA) instance yields only P < m, for the anchor's
   own anchor P. The mechanized proof derives a < m by the full Step-0
   argument (lemma `rmint_ro_after`: (RSA) plus the convexity trap plus
   the (LinkR) geometry), which section 9.7.4 already supplies. The
   construction is sound; only the citation line was wrong.

2. The transport bill in section 9.7.6 is incomplete: besides chain
   stability, transporting the RBk clauses across sync needs
   record-lookup stability (`mRecOfId_append_left` plus a new
   `mRecOfId_agree`, obtained from `MInv.cross`) and positivity of the
   grown knowledge (`mRecOfId_zero` vacuates the transported clauses at
   a = 0). A completeness gap, not an error.

For the record, two simplifications: the mint-step RBk preservation
needs no Lamport or freshness hypotheses (the clauses never mention the
minted stamp), and two case analyses forecast in 9.7.4 (the full "after
everything in Subtree(a)" form of Step 0, and the L-descendant sub-case
of beta1) turned out unnecessary.
