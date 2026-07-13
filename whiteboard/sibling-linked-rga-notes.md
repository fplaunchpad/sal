# The sibling-linked tombstone-free RGA — design record

*Working notes, KC + Claude, 2026-07-11. Companion boards: `rga-tombstone-free.excalidraw`
(the full exploration trail), `fooling-pair.excalidraw` (the impossibility witness).
Prototype/PBT scripts from the session live in the scratchpad, not the repo; the Lean
port has not started. Drawing conventions: solid arrow = parent pointer, dotted arrow =
sibling pointer; parent above its children; siblings share a horizontal row; merge
scenarios drawn as diamonds (LCA top, versions below left/right, merged state at the
bottom, double-overlapping arrows for the version DAG).*

## 1. The problem

The flat tombstone-free RGA's delete reorders survivors: `ins a·1←⌂; ins b·2←⌂;
ins c·3←a` reads `b a c`; deleting `a` rehomes `c` to the root where its own timestamp
out-ranks `b` — read `c b`, not `b c`. Machine-checked
(`tombstone_free_violates_delete_order`, RGA SPOT). The tombstoned RGA avoids this by
keeping every deleted node as a position-holder, forever. Question of the exploration:
can a **tombstone-free** sequence MRDT preserve order — and at what price?

Intermediate attempts (rational position keys Q with within-bounds reprojection;
frozen coordinates; rebuild-with-carried-graves) are recorded on the big board with
their counterexamples (CX-P "puncture", CX-F "frame mismatch", the stale-LCA loss).
Their common failure: they compare **numbers born in different computations**. The
design below replaces numbers with structure.

## 2. The design

**State** (per replica, live nodes only):

```
σ = ( V : set of ids,  par : V → V ∪ {⌂},  sib : V ⇀ V )
```

- ids are timestamps (Lamport); `sib(u)` = u's immediate next (older-side) sibling in
  its parent's row, undefined for the last.
- Invariants: `par` is a forest rooted at ⌂; each parent's children form one chain
  under `sib`; **sibling pointers connect siblings only** (a parent never points into
  its children's row); the row head is *derived* — the unique child no sibling points
  to — never stored.

**Operations**

- `read`: DFS from ⌂; per node, start at the row head, walk `sib`, emit each child
  then recurse into it. Siblings effectively newest-first.
- `insert(x after a)`: `V += x; par(x) := a; sib(x) := old head of a's row` (if any).
  Nothing else changes. Sibling order among concurrent same-anchor inserts is decided
  at insertion time and stays stable.
- `delete(d)`: splice. With parent p and child chain `c₁ ⤍ … ⤍ cₘ`:
  `par(cᵢ) := p`; the pointer into d (`sib(s) = d` for the left sibling s, if any)
  is redirected to `c₁` (or to `sib(d)` if m = 0); `sib(cₘ) := sib(d)`; then **erase d
  from V, par, sib** — the state never mentions a dead id. Deleting a row head touches
  no sibling pointer at all. Locally order-preserving by construction (linked-list
  splice).

## 3. The merge — membership analysis first

`merge(L, A, B)`. Model invariant (supplied by the framework's LCA discipline, an
explicit hypothesis for mechanization): **every event common to A's and B's past is
in L.** Membership patterns for an id across (L, A, B):

| # | ∈L | ∈A | ∈B | verdict | role |
|---|----|----|----|---------|------|
| 1 | – | – | – | never existed, **or born-and-deleted inside one branch** | invisible; the fooling class lives here |
| 2 | ✓ | ✓ | ✓ | live — L-survivor | full three-way value analysis |
| 3 | ✓ | ✓ | – | dead (B deleted) | **marker**: its L/A entries still position things |
| 4 | ✓ | – | ✓ | dead (A deleted) | marker, symmetric |
| 5 | ✓ | – | – | dead (both) | provably never surfaces (can't be a sib target; can't be an unchanged sib value) |
| 6 | – | ✓ | – | live — A-born | only A has opinions |
| 7 | – | – | ✓ | live — B-born | only B has opinions |
| 8 | – | ✓ | ✓ | **impossible** by the model invariant | — |

`live(M) = pattern 2 ∪ patterns 6/7`. Within live(M), "present in exactly one branch"
⟺ **branch-born**. Every id the merge ever consults is live in at least one input —
the state genuinely carries no graves.

## 4. The merge — value cases for `sib(u)` (and `par(u)` analogously)

Only deletes mutate existing entries. `vL, vA, vB` = stored values (id or ⊥).

- **Case 0** — u branch-born (6/7): take the owner branch's value.
- **Case 1** — `vL = vA = vB`: retain.
- **Case 2** — `vA = vB ≠ vL`: take the common changed value.
- **Case 3** — exactly one branch changed: take the changed value.
- **Case 4** — `vA ≠ vB`, both `≠ vL`:
  - **4a, both candidates ∈ L**: *forced* — take the **L-document-later** one. Proof:
    the branch pointing at the later candidate deleted everything between, including
    the other candidate (deleting its ancestors would only promote it into the gap),
    so the L-earlier candidate is always pattern 3/4 (merge-dead) and the later one
    is always pattern 2 (merge-live). "L order decides" and "take the live one"
    coincide.
  - **4b, one branch-born, one ∈ L**: *forced* — branch-born first; its own branch
    already displays it before that L-continuation, so any other order flips a
    co-observed pair. The L-candidate becomes the segment's continuation.
  - **4c, both branch-born**: **the only free case.** Greater timestamp first; the
    loser's segment attaches after the winner's whole segment, then the common
    continuation.

**Row repair** (assembling each row into one chain):
- *Dead target*: chosen `sib(u)` is merge-dead → contract through the **killer
  branch's row** (what it spliced into that position), recursively. Legitimate: the
  dead node is live in the other input (pattern 3/4).
- *Competing segments* (same target, or multiple row heads): order the segments by the
  **L-document position of their continuations** — different continuations = different
  slots, L decides, no timestamp. Same or absent continuation = genuinely the same
  slot → timestamp (case 4c again).

Equivalent global formulation (the "skeleton algorithm"): per row, take the L-nodes
present in either branch row ordered by **L's document order** (the skeleton; dead
ones act as markers and are dropped from the output), attach each branch's maximal
runs of branch-born nodes (segments) at the gap before their L-successor, order
same-gap segments newest-head-first (blocks stay contiguous → non-interleaving).
The greedy head-to-head weave is **wrong** (w-slot case below); L-document order for
the skeleton is essential.

## 5. Litmus results (hand-run)

| test | what it killed previously | this design |
|---|---|---|
| sequential `b a c`, del a | flat RGA | ✓ (splice) |
| T2: shared siblings P·3/Q·2, A: +x·10 under P, del P ∥ B: +y·20 under Q, del Q | flat seq-merge (phase 2) | ✓ — P, Q act as markers (each still live in one input) |
| CX-P puncture | unclipped rationals | ✓ |
| CX-F frame mismatch (B idle) | every numeric scheme | ✓ — pure Case 1/3, structural |
| stale-LCA late merge (idle fork) | rebuild-with-carried-graves (node vanished) | ✓ — post-splice state is order-self-contained |
| leapfrog `m·3` vs collapsed chain | own-timestamp placement | ✓ |
| both delete same x, fresh u·10 ∥ v·9 under it | — | ✓ — 4c benign: fresh-vs-fresh, ts is the *right* datum |
| w-slot (`p·4` fresh ∥ `k·6` occupying dead `w·3`'s slot before `c`) | the greedy two-pointer weave (session bug, caught by writing it down) | ✓ via skeleton/continuation rule, no ts |
| **fooling pair** | — | ✗ **provably, for any rule** |

## 6. The fooling pair (impossibility for the tombstoned-oracle spec)

Plain form (drawn on `fooling-pair.excalidraw`):

- **LCA**: empty. **A**: `ins p·5 ← ⌂` → document `p`.
- **B**: `ins g·2 ← ⌂; ins k·10 ← g; del g` → document `k`; state = just k
  (par ⌂, no sib entries) — g appears nowhere.
- **World 2**: identical script with `g·6`. B's final state is **bit-identical**.
- Tombstoned RGA expects: world 1 `p k` (p·5 out-ranks the grave g·2); world 2 `k p`
  (g·6 out-ranks p·5). Identical merge inputs ⟹ identical output ⟹ **any**
  deterministic merge is wrong in one world. The ts-rule returns `k p`: right in
  world 2, fooled in world 1.
- If the state kept each node's original insert-anchor, use a two-node dead chain
  (`g`, then `h` under it, `k` under `h`; vary g's timestamp): k's stored anchor is
  `h` in both worlds. Bounded fields push the pair one level deeper; per-node state
  must grow with deleted-path depth to win. This is the information-theoretic form of
  "the deleted path ≡ the tombstones."

## 7. The spec fork — where the exploration landed

**Both worlds converge** (deterministic merge of identical states); the fooling pair
is *not* a convergence bug. What fails is fidelity to the **tombstoned oracle** — a
history-relative spec that demands consistency with comparisons **no replica ever
observed**: in both worlds, no state ever contained p and k (or p and g) together.

- Fooling ⟹ never co-observed: the deciding timestamp must be absent from all inputs
  ⟹ the decider died inside one branch ⟹ the mis-ordered pair spans the branches.
- Co-observed ⟹ never flipped: the only free rule is 4c (same-gap, cross-branch);
  L-pairs are pinned by the skeleton, same-branch pairs by their branch's row.

So the two-theorem shape:

1. **Impossibility**: no bounded, tombstone-free state reproduces the tombstoned RGA's
   order — that spec prices out to remembering dead ranks (deleted path ≡ tombstones).
2. **Possibility (conjecture, single-merge case argued)**: this design satisfies the
   **observable spec** — convergence, local delete-order-preservation,
   non-interleaving, and observed-order stability (never flip an order any replica's
   causal past displayed) ≈ Attiya et al.'s strong list specification — with **zero
   graves and bounded per-node state**.

Why no graves at all: tombstones bundle two jobs. Remove-detection is the **LCA's**
job in the ternary MRDT model (pattern table above); position-holding is needed only
by the unobservable spec. Drop that spec and the rent stops. (In a binary/state-based
model without LCAs, remove-detection returns and graves with it — the honest boundary
of the claim.)

## 7½. PBT postscript (2026-07-11 evening): the impossibility ladder

The PBT harness (`scratchpad/sl_pbt.py`, three-verdict scheme vs the tombstoned oracle +
strong-list check over all displayed orders) found three counterexample classes; each was
extracted, minimized, and validated:

1. **Implementation bug 1** (pairwise flip): a dead node's children split across two rows
   (one routed by B's promotion, one kept with the marker), losing A's displayed order.
   Fix: *attach deep* — children of a marker stay with the marker; the terminal splice
   repositions. After the fix, pairwise violations = 0 at single-epoch volume.
2. **Implementation bug 2** (cycle, no pair flipped): a branch-born run keyed to its
   successor in the branch's *final* row landed after a marker the branch itself deleted,
   though the branch had displayed the run *before* it. Fix: runs jump back over
   own-deleted markers. Both bugs are machine-found counterexamples to plausible weaker
   merges — illustrative for the writeup.
3. **NOT a bug — a theorem.** Residual cycles are genuine. Minimal validated witness
   (5 nodes, two worlds, machine-checked identical inputs):
   L: `m·1←⌂, g·2←⌂` (row g, m). B: `ins y·9←g` (displays g<y, y<m). A world 1:
   `ins x·5←⌂` (displays x<g), `del g`, `del m`. A world 2: `ins x·5←m` (displays m<x),
   `del m`, `del g`. Both worlds: A-state = {x at root}, bit-identical; B, L identical.
   World-1 displays force x<y (x<g<y); world-2 displays force y<x (y<m<x). Identical
   inputs ⟹ same merge output ⟹ **no tombstone-free state-function merge satisfies the
   strong-list spec** (a global order consistent with all displays, including displays
   that involved since-deleted nodes). Constraints chain transitively *through dead
   nodes' past displays*, and the state cannot remember which side of a dead node new
   content was displayed on.

**The ladder** (all: tombstone-free state, merge = f(L,A,B)):
- tombstoned-oracle fidelity — impossible (4-node pair, §6);
- strong-list / transitive observed order — impossible (5-node pair above);
- **pairwise display stability — ACHIEVED (empirically closed, 2026-07-11 night).**
  Three merge-rule refinements were needed, each driven by an extracted-and-validated
  counterexample: (i) *attach deep* — a dead-but-marked node's children stay with the
  marker until the final splice (children split across rows had flipped a displayed
  order); (ii) *predecessor-riding* — a branch-born run is placed immediately after the
  last L-node preceding it in its own branch's row (successor-keying had let a run
  drift to the wrong side of content its branch displayed before it); (iii) *head
  jump-back* — only a run at its row head (no predecessor) jumps back over markers its
  own branch deleted. One further failure was a HARNESS id-collision (stale replica's
  fixed id band colliding with epoch bands — violating global id uniqueness, on which
  the whole membership analysis rests), not a merge bug.
  Final sweep: ~16,000 merges (banded + interleaved Lamport ids × epoch depths 1–4 ×
  stale-replica topologies): **0 displayed-pair flips, 0 divergences whose tombstoned
  direction was ever displayed, 0 assertion failures**; 14–23% of merges diverge from
  the tombstoned oracle (licensed, workload-dependent — generators are ~30% deletes);
  strong-list cycles at ~4% of trials, exactly as the impossibility requires.
  The boundary is confirmed AT pairwise stability: below it impossible, at it achieved.

## 7¾. SPEC DECISION (KC, 2026-07-11)

**Adopted spec: pairwise display stability** — if any state anywhere ever displayed x
before y, no state ever displays y before x. Rationale: the strong-list auditor detects
"violations" no user can witness — it aggregates read logs across replicas and reasons
transitively through *dead nodes'* past appearances, i.e. it remembers the dead, which
is a tombstone in disguise; the theorem in §7½ makes that precise. Per user session no
pair ever flips. For live pairs the state *is* the history (splice preserves survivor
order, so a branch's final state carries the displayed order of every live pair), so
this rung is conjecturally achievable with zero tombstones.

**Additionally: record the divergences with respect to the tombstoned RGA.** The
licensed-divergence set (pairs ordered differently from the tombstoned oracle — always
never-co-displayed pairs) is part of the datatype's published contract, not something
to hide: SL = tombstoned-RGA order on every pair any replica ever displayed, timestamp
order on the rest, and the PBT reports divergence incidence per workload.

## 8. Open items

1. **PBT** the full construction (cases + repairs) against the observable spec —
   track every pair co-displayed in any causal-past state; assert no later state flips
   one — over multi-epoch executions (merge outputs become inputs) and stale-LCA
   topologies. The single-merge argument is done on paper; **stability propagation
   across epochs is claimed, not proved**. This is the step that can still kill the
   design.
2. Non-interleaving at volume (segments-stay-blocks argued, not proved).
3. The pattern-8 exclusion ("common past ⊆ LCA") as an explicit hypothesis — check
   what Sal's version-DAG model guarantees under criss-cross merges.
4. If PBT survives: paper-style note (theorem pair, this case analysis as the core),
   then the Lean port as a conditioned instance; `oq:linspec` gets its answer — the
   intent spec of a sequence MRDT should be the *observable* order relation, not the
   datatype's private tree.

## 9. Postscript (2026-07-13): the successor design, and a refuted simplification

The rose-tree merge above was later machine-checked **non-RA-linearizable**
(`Shesha_Rows_Refuted.lean`: an honest 5-event config where the merge splits a
dead node's cross-branch children around a concurrent sibling, `[3,4,2]`, which
is no fold). The successor is the **sibling-edge / between-origins design**
(`sibling-edge-design.pdf`, `sibling-origin-pbt.py`): each node carries
immutable `after` (= `anc`) **and** `before` origins plus their spines; delete =
pure remove; read/merge = global integration with deleted ids participating as
**ghosts**. Python-validated: 0 anomalies / ~37k merges (single + multi epoch),
RA-linearizable, delete-order-preserving, non-interleaving.

**Refuted simplification — the symmetric splice** (`new_proposal.excalidraw`):
view the state as two mirrored RGA trees (`after` rooted at `s`, `before` rooted
at `e`) and let delete *splice in both trees* (after-children climb to
`after(d)`, before-children to `before(d)`), eliminating ghosts. This fails
**sequentially**, by a 3-node fooling pair:

    W1: ins a·1(s,e); ins b·2(s,a); ins c·3(a,e) → [b,a,c]; del a ⇒ must read [b,c]
    W2: ins a·1(s,e); ins b·2(a,e); ins c·3(s,a) → [c,a,b]; del a ⇒ must read [c,b]

Both worlds splice to the **bit-identical** state `{b:(s,e), c:(s,e)}`, so no
read/tie-break preserves delete-order. The splice erases *which side of the dead
node each survivor was on* — exactly the bit the ghost reference keeps (under
pure remove the two worlds' states differ and read correctly; machine-checked).
Consequence: the ghost id on survivors is the **irreducible** per-deletion
memory of an order-preserving tombstone-free list; any "fix" that keeps the
distinguishing bit is a ghost by another name. (W1 is the classic `[b,a,c] del
a` case: older-first ties fix it, and then W2 — its mirror — breaks; the
tie-break incoherence is the symptom of the lost bit.)

The two-tree *frame* itself remains the right presentation of the validated
design (sib = explicit `before`; `s`/`e` duals) — only the spliced delete is
dead. Next step stays: the Lean port of the ghost-ref design (§8.4).
