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
