# Shesha — sequential soundness and causal pairwise display stability: pen-and-paper proofs

*KC + Claude, 2026-07-11/12. Companion: `sibling-linked-rga-notes.md` (design record,
litmus results, PBT verdict), boards `rga-tombstone-free.excalidraw`,
`fooling-pair.excalidraw`, harness `sl_pbt.py`. This note is self-contained: all
definitions restated. Status markers: **[proved]** = full argument here; **[sketch]** =
routine induction, spelled to the case split; **[owed]** = named obligation for Lean.*

## 0. Name

RATIFIED (KC, 2026-07-12): **Shesha** (शेष, Ananta-Shesha) — "the remainder": what persists when all else dissolves, holding the worlds steady, unbroken; the serpent as the mythic linked list. Earlier proposal Mneme superseded.

Originally proposed: **Mneme** (the Muse of memory; in the rite of Trophonius, initiates drank from
two springs — Lethe, to forget, and Mnemosyne, to remember). The datatype does exactly
that: it *forgets its dead completely* (tombstone-free in the strictest sense — a deleted
element leaves no record in any field of any replica) and *never contradicts what was
remembered* (no order any replica ever displayed is later reversed). The name also pairs
with this repo's Lethe calculus. Pending KC's ratification; "sibling-linked list" remains
the descriptive fallback. It is deliberately **not** called an RGA: the state (explicit
sibling links, no tombstones), the delete (splice), the merge (three-way pointer-case
analysis), and above all the *contract* (§5, §7) differ from RGA's.

## 1. The datatype

Ids are Lamport timestamps: unique, and a replica's fresh id exceeds every id it has seen
**(M1)**. A state is

```
σ = ( V : set of ids,  par : V → V ∪ {⌂},  sib : V ⇀ V )
```

with invariants: `par` a forest rooted at ⌂; each parent's children form one chain under
`sib` (the *row*); a row's head is the unique child no sibling points to (derived, never
stored); `sib` relates siblings only.

- **read(σ)**: depth-first from ⌂; at each node, walk its row from the head, emitting
  each child then recursing into it.
- **insert(x after a)**: `par(x):=a; sib(x):=` old head of a's row (if any). Nothing else
  changes.
- **delete(d)**, parent p, child chain c₁⤍…⤍cₘ: `par(cᵢ):=p`; the pointer into d (left
  sibling's `sib`, if d wasn't head) is redirected to c₁ (or to `sib(d)` if m=0);
  `sib(cₘ):=sib(d)`; then d is erased from V, par, sib. **After this line the state
  contains no trace of d.**

**Display relation.** `D(σ) = {(x,y) : x precedes y in read(σ)}`. An execution is a
version DAG: states evolve by local ops and by ternary merges `merge(L, A, B)` where L is
the LCA version; model assumption **(M2)**: every event common to A's and B's past is in
L. The *display log* of an execution is the union of `D(σ)` over all states σ it produces.

## 2. Sequential soundness — the obvious spec is a linked list

**Sequential spec (naive list).** A sequence `s` of elements; `ins(x after a)` places x
*immediately after* a (at the front for a=⌂); `del(x)` removes x; read = the sequence.

**Theorem S (sequential soundness) [proved].** For any single-replica op sequence,
`read(σ)` equals the naive-list fold of the same ops.

*Proof.* Induction on ops. *Insert:* x becomes the head of a's row, with empty subtree;
in the preorder, a is emitted, then its row head — so x is emitted immediately after a,
and no other node's emission position changes (no other pointer changed; x's row is
empty). For a=⌂, x heads the root row = front. This matches the naive list. *Delete:*
the splice substitutes d's child chain for d inside p's row, in place; preorder emission
of every survivor is unchanged except d's disappearance: the walk that formerly went
"…, d, d's subtree, sib(d), …" now goes "…, d's subtree, sib(d), …" — the same sequence
minus d. So `read(delete(σ,d)) = read(σ) ∖ d`, order intact — which is the naive-list
delete. ∎

**Corollary S1 (sequential delete-order preservation).** A single-replica delete never
reorders survivors. — This is the property the flat tombstone-free RGA *fails*
(machine-checked: `tombstone_free_violates_delete_order`, its witness `b a c → del a →
c b`), and the original motivation for this design: the flat design derives sibling
order from ranks, so rehomed children re-sort; here order is *stored in the links*, and
the splice preserves it by construction.

**Corollary S2 (session coherence).** Along any single replica's op sequence, the display
order of any pair, while both elements live, is constant; hence a branch's *final state
carries the display order of every pair it ever showed and still holds*: for u,v live in
σ_final, `(u,v) ∈ D(σ_final)` iff every earlier state of the session that contained both
displayed u before v. *(Directly from Theorem S: each op preserves survivor order.)*

## 3. Branch agreement

**Lemma B [proved].** If u,v are live in both branches A and B (both forked from L),
then u,v ∈ L (by (M1)/(M2): a node present in both branches is common past), and
`ord_A(u,v) = ord_L(u,v) = ord_B(u,v)`.

*Proof.* Branch-born ids are exclusive to their branch, so u,v ∈ L. Each branch evolves
from L by local ops, which preserve survivor order (Theorem S); u,v survive in both. ∎

Hence the three inputs of any merge never disagree on the order of a co-live pair: the
union of their display orders on live pairs is **conflict-free**.

## 4. The merge

With `live(M) = (V_A∩V_B) ∪ (V_A∖V_L) ∪ (V_B∖V_L)` and *markers* = L-nodes live in
exactly one branch (deleted by the other; still live in one *input*, so no tombstone
exists in any state):

1. **Skeleton.** L-nodes of `live(M) ∪ markers`, grouped under their deepest surviving
   L-ancestor (markers count as surviving hosts — *attach-deep*), each group ordered by
   **L's document order**.
2. **Branch-born rows.** A branch-born node with a branch-born parent keeps its branch's
   row wholesale.
3. **Runs.** In each branch row hosted by an L-node or ⌂, the maximal runs of branch-born
   nodes are placed: **(a) predecessor-riding** — a run with an L-predecessor `pre` (the
   last L-node before it in its branch's row) goes immediately after `pre`'s final
   position; **(b) head jump-back** — a run at its row head goes before its L-successor,
   jumped back over any markers *its own branch deleted*; **(c)** a run with neither
   goes to the end of its host's row. Runs landing at the same position: each stays
   contiguous; newest head first.
4. **Splice.** Markers are spliced out (the same splice as delete), leaving live nodes
   only.

**Lemma M0 (well-formedness) [sketch].** Every live node is placed exactly once (L-nodes
via their unique skeleton group; branch-born nodes belong to exactly one branch and there
to exactly one row, hence one run or one wholesale row), so the output rows are chains
and the invariants hold.

**Lemma M1 (symmetry) [sketch].** The construction is symmetric in A,B: every rule is
branch-agnostic except the newest-first tiebreak, which is symmetric.

**Lemma M2 (L-extension) [proved].** `D(merge)` restricted to surviving L-pairs equals
L's order. *Proof:* survivors' relative order is fixed by the skeleton (L-document order
within groups; group nesting follows L's tree with attach-deep keeping a dead host's
group in the host's own position), and the splice preserves order (Theorem S argument).
Runs only insert *between* skeleton elements. ∎

**Lemma M3 (branch-extension) [proved for the case split; the two subtle cases in
full].** `D(merge)` restricted to the live pairs of branch X equals `D(X)`.

*Proof.* Take u before v in X's read, both surviving. Cases:
- *Both ∈ L*: by Lemma B, X's order is L's; by M2 the merge agrees.
- *Both branch-born, same row and run, or in wholesale rows*: runs and wholesale rows are
  copied in X's order, and DFS nesting of branch-born subtrees follows X's `par`.
- *Both branch-born, different runs of one row*: distinct runs are separated in X's row
  by at least one L-node w. u's run sits (weakly) before w's final position and v's run
  (weakly) after: u's run either rides an L-predecessor ≤ w or jumps to a successor ≤ w;
  v's run rides a predecessor ≥ w. Since skeleton positions respect L-document order and
  Lemma M2 places w consistently, u precedes v. **The subtle case is a head run (b) vs
  the jump:** jumping back over marker m (own-deleted) cannot cross an L-node the run was
  displayed after, because any L-node displayed before the run in X's history either
  survives in X's row before the run — contradicting "run is at its row head" — or was
  deleted *by X*, and then it is itself a jumpable marker or dead-dead (not in the
  skeleton). So the jump crosses only nodes X never displayed before the run, or
  displayed *after* it (a fresh insert at a row head was displayed before everything then
  in the row, including m while it lived). Either way `D(X)` is respected.
- *One ∈ L (w), one branch-born (u)*: if u's run rides predecessor `pre`: X displayed
  `pre` immediately before the run; w is either ≤ pre (then merge places u after pre ≥
  after w, matching X) or ≥ the run's successor (merge places u before it, matching X).
  If u's run is a head run: X displays u before every L-node of that row that it ever
  co-displayed (head position + Theorem S), and the merge places the run before its
  successor and after nothing X displayed before it (previous case). ∎

**Lemma M4 (fresh pairs).** Pairs not co-live in any input (one A-born and one B-born;
or separated by the other branch's delete) were, by (M1)/(M2), **never co-displayed by
any state in the merge's causal past** — the deciding context never crossed a replica
boundary. The merge's choice on them (newest-first among same-slot runs; skeleton
positions otherwise) is therefore unconstrained by the display log. *(This is where the
tombstoned oracle and the strong-list spec demand more — provably unattainable, §7.)*

## 5. Headline theorem — causal pairwise display stability

**Definition.** An execution satisfies *causal pairwise display stability* if for any two
produced states with a common causal upper bound (some state descending from both), their
display relations agree on common pairs. Equivalently: no user, and no future merged
document, ever witnesses an order reversal.

**Lemma J (join uniqueness) [proved].** Under (M2), for any pair {u,v}, any state
containing both is a descendant of a *unique-up-to-descent first join* within its
causally-connected component: two independent first-joins can never both lie in the past
of a later state (their LCA would already contain both u and v, contradicting
first-join-ness). ∎

**Theorem P (headline) [proved from the lemmas].** Every execution of Mneme under
(M1),(M2) satisfies causal pairwise display stability.

*Proof.* Induction over the version DAG, maintaining: the display log restricted to any
causally-connected set of states is antisymmetric. Local ops preserve displayed orders
(Theorem S / S2). A merge's output agrees with L, A, B on all their live pairs (M2, M3)
— which by S2 and Lemma B carry exactly the orders previously displayed in the merge's
past — and decides only pairs never displayed in its past (M4), consistently with Lemma J
(any other state showing that pair shares this join in its past, or is causally
unrelated forever). ∎

**Theorem D (licensed divergence) [sketch].** Where `read(merge)` differs from the
tombstoned-RGA oracle, the differing pairs were never co-displayed in the oracle's
direction by any state: first displays in op-states follow the oracle (Theorem S gives
naive-list = oracle semantics on live anchors), and merges preserve first displays
(Theorem P), so a displayed oracle-direction pair can never be output reversed.
*(Empirically: 0 exceptions in ~16,000 merges.)*

## 6. Necessity of the three merge refinements

Each refinement is forced — dropping it admits a machine-validated counterexample
(harness trials, reproduced in `sl_pbt.py`'s lineage):

| refinement dropped | witness | violated |
|---|---|---|
| attach-deep (children split across host rows) | trial-19 class: dead node's children routed both to root (via B's promotion) and to the marker | pair flip of an A-displayed order |
| predecessor-riding (successor-keyed placement) | trial-251 class: run jumped a marker whose live content its own branch displayed before it | pair flip |
| head jump-back (runs placed after own-deleted markers) | trial-43 class: `x<g` (A), `g<y` (B), merge `y<x` | strong-list cycle through a dead node's displays |

## 7. Impossibility appendix — why the spec stops here

**(I1) Tombstoned-oracle fidelity is unattainable** (4-node pair): L empty; A: `ins
p·5←⌂`; B: `ins g·2←⌂, ins k·10←g, del g` — vs the same with `g·6`. B's final states are
bit-identical ({k at root}); the oracle demands `p k` in world 1 and `k p` in world 2.
Any state-function merge is wrong in one world.

**(I2) Strong-list (one global order over all displays, including those of the dead) is
unattainable** (5-node pair): L: `m·1←⌂, g·2←⌂`; B: `ins y·9←g` (displays g<y, y<m).
World 1: A `ins x·5←⌂` (displays x<g), `del g, del m` — forces x<y transitively. World
2: A `ins x·5←m` (displays m<x), `del m, del g` — forces y<x. A's final state is `{x at
root}` in both. Identical inputs, contradictory requirements. Constraints chain through
*dead nodes' past displays*; a tombstone-free state cannot remember which side of a dead
node its survivors were shown on. **Auditing through the dead is remembering the dead** —
the strong-list auditor is a tombstone in disguise, which is precisely why pairwise
display stability (quantifying only over what states actually show) is the right spec
under the no-tombstones-in-any-encoding constraint.

## 8. Anomaly comparison table (DRAFT — cells to be machine-verified)

*Cell legend: ✓ = excluded / property holds; ✗ = permitted (anomaly possible); markers:
**[R]** proved or witnessed in this repo; **[L]** literature recall — to be re-verified;
**[?]** open. KC's directive: every cell must ultimately be backed by a witness execution
or a PBT/proof against an actual implementation — competitor rows to be implemented
minimally in the harness.*

| design | tombstone-free | bounded per-node metadata | sequential = naive list | pairwise display stability | strong list | RGA-oracle fidelity | non-interleaving (fwd) |
|---|---|---|---|---|---|---|---|
| RGA (tombstoned) | ✗ (graves forever) | ✓ | ✓ [R] | ✓ [L] | ✓ [L: Attiya+ PODC'16] | ✓ (is the oracle) | ✓ [L] |
| flat TF-RGA (repo) | ✓ | ✓ | **✗ [R]** (del reorders: `b a c→c b`) | **✗ [R]** (flip is sequential!) | ✗ [R] | ✗ [R] | ✓ [?] |
| Logoot / LSEQ | ✓ | ✗ (dense ids grow) | ✓ [L] | ✓ [L?] | ✓ [L?] | ✗ (different order) | **✗ [L: PaPoC'19]** |
| WOOT / Yjs-YATA / Fugue | ✗ (tombstones) | ✓ | ✓ [L] | ✓ [L?] | ✓ [L?] | ✗/≈ | ✓ [L; Fugue: maximal] |
| stored-path (phase 1, repo) | ✓ | ✗ (path grows w/ depth) | ✓ [R] | ✓ [R?] | ✓ [R?] (immutable positions ⟹ one global order) | ✗ | ✓ [?] |
| **Shesha (this)** | **✓ [R]** | **✓ [R]** | **✓ [Thm S]** | **✓ [Thm P + 16k merges]** | ✗ **forced** [I2] | ✗ **forced** [I1], licensed & measured | ✓ segments-contiguous [?backward] |

Two literature notes (recall — verify in a related-work pass): the *interleaving* anomaly
is well known (Kleppmann et al., PaPoC'19; Fugue = Weidner & Kleppmann 2023 as the
non-interleaving frontier), and the strong/weak *list specifications* are Attiya,
Burckhardt, Gotsman, Morrison, Yang, Zawirski (PODC'16), who prove RGA satisfies the
strong spec. The **delete-reorder-of-survivors anomaly appears not to be named in the
literature** — published designs avoid it by keeping tombstones or immutable positions —
and the explicit separation of *pairwise display stability* from the strong list spec
(with I2 showing the gap is exactly "memory of the dead") appears new. Both claims need
the verification pass before being asserted in print.

## 9. Lean obligations (the port plan)

1. State + WF invariant; `read`; `insert`/`delete`; **Theorem S** (sequential soundness
   vs a naive `List` model) and S1 — the per-datatype "obvious spec" theorem KC mandates
   for all conditioned RDTs.
2. The merge as specified; M0 (WF), M1 (symmetry).
3. M2, M3 (order extension) — the main inductive work; L-document-order machinery.
4. Lemma J + Theorem P over the framework's version-DAG reachability ((M2) is exactly the
   store's LCA discipline — a *conditioned* hypothesis, sibling to HonestDelivery).
5. Theorem D (licensed divergence) — relative to the repo's tombstoned RGA as oracle.
6. I1, I2 as machine-checked impossibilities (`native_decide` on the two fooling pairs,
   quantified over merge functions of bounded state — statement engineering needed).
7. Convergence/RA-linearizability packaging as a Sal conditioned instance.
