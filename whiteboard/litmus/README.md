# The sequence-RDT litmus suite

One executable battery containing **every anomaly that has driven a design
decision or refutation in this project**, runnable against any sequence-RDT
implementation in one command. This is the executable half of the
specification: designs are judged against named, provenanced tests — not
against sweep percentages.

```
python3 litmus.py        # matrix to stdout, markdown to litmus_matrix.md
```

The tests are defined over **histories** — scripts of user intentions
(`insert x after element a`, `delete d`) executed against a live local
replica — never over state encodings. An implementation plugs in by
providing `{init, apply, read, merge}` (see the `Design` classes in
`litmus.py`); the whole battery then runs unchanged. Ids are Lamport-plausible
integers and double as timestamps.

## The spec clauses (the observable ladder)

Letters in the last column map to the anomaly-matrix report's columns
(`whiteboard/anomaly-matrix/anomaly_matrix_report.md`).

| clause | meaning | matrix col. |
|---|---|---|
| **S1** sequential soundness | a single replica's final read equals the naive-list fold of its script (the "obvious spec": insert-after places immediately right of the anchor; delete removes) | c |
| **S2** step display stability | no two consecutive reads of one replica flip a surviving pair | d (seq.) |
| **S3** merge convergence | `merge(L,A,B)` reads equal to `merge(L,B,A)` | — |
| **S4** pairwise display stability | no pair displayed by any LCA/branch read flips in the merge read (the spec adopted in the design-record §7¾) | d |
| **S5** non-interleaving | designated concurrent runs stay contiguous, in run order | g/h |
| **S6** list-linearizability | the merge read equals the naive fold of **some** causal interleaving of the branch scripts | — |
| **S7** strong-list closure | the merge read respects the **transitive closure** of all displayed pairs (Attiya et al.-style; provably unachievable tombstone-free — see L15) | e |
| **DUP** | no element duplicated in a merge read | — |
| **IDL** | idle-branch identity: `merge(L, A, L) ≃ A` (the CX-F "frame mismatch" essence: an idle branch must contribute nothing) | — |
| (L14 probe) | fidelity to the tombstoned oracle | f |

**Deliberately excluded: RA-linearizability w.r.t. the datatype's own fold.**
Own-fold RA-lin certifies convergence to the datatype's own `do_`, so a
sequential reorder baked into `do_` is invisible to it (the spec-limit lesson:
the flat RGA is own-fold RA-linearizable *and* fails S1). It belongs to each
design's mechanized verification, not to an implementation-agnostic anomaly
matrix. S6 plays its role here, against the one fixed sequential spec.

## The tests

**Sequential** (S1, S2):

- **L1 delete-reorder** — `ins a·1←⌂; ins b·2←⌂; ins c·3←a; del a` → must read
  `[2,3]`. The flat RGA's classic failure (rehome + timestamp re-sort ⇒
  `[3,2]`). Provenance: `tombstone_free_violates_delete_order`
  (`Sal/MRDTs/RGA/RGA_Tombstone_Free_SPOT.lean`).
- **L3a / L3b deep delete-runs** — build `[5,4,3,2,1]` by front-inserts
  (resp. `[1,..,5]` by chained inserts), delete the middle run `2,3,4`.
  Detects loss of transitive order testimony when every link of the bridge
  dies together. Kills bare birth-records (B2 reads `[1,5]` for `[5,1]`).
  Provenance: this session's deep-chain analysis.
- **L2 splice fooling pair** (two worlds) — W1 `ins b before a; ins c after a`
  vs W2 `ins b after a; ins c before a`, then `del a`. The worlds require
  opposite survivor orders; a design whose two final states are **bit-identical**
  (reported) is *provably* unable to satisfy both. Kills the symmetric-splice
  two-tree design (and the flat RGA). Provenance: design-record §9,
  `new_proposal.excalidraw`.

**Merge diamonds** (S3, S4, S6, S7, DUP, IDL):

- **L4 criss-cross split** — LCA `[1]`; A: `ins 2←1, ins 4←⌂, del 1`; B:
  `ins 3←1`. The dead node's cross-branch children must not be split by the
  concurrent sibling. The rose-tree Shesha outputs `[3,4,2]` — no fold —
  reproducing its machine-checked refutation (`Shesha_Rows_Refuted.lean`).
- **L5 ins ∥ del-anchor** — duplication guard for the pair that broke the
  plain join hook (`Shesha_Join_Refuted.lean`; observable residue only —
  the full force of that refutation is proof-layer).
- **L7 concurrent runs** (+S5) — two runs after one anchor must stay blocks.
  Kills flat position-key designs (Logoot-genus interleaving).
- **L8 T2 dual markers** — both branches insert under a shared sibling and
  delete it (design-record §5). Order must route through both dead markers.
- **L9 w-slot** — a fresh front insert concurrent with an insert occupying a
  deleted node's slot (design-record §5, the greedy-weave killer;
  reconstruction). Exposes *open-boundary* key assignment (see findings).
- **L10 attach-deep / L11 head jump-back** — the two extracted rose-tree merge
  bugs (design-record §7½): a marker's children must not split across rows; a
  branch-born run must not land behind a marker its own branch deleted.
- **L12 leapfrog**, **L13 puncture** — survivor placement across a deleted
  interior node; L13 is the CX-P "puncture" (insert into a gap whose bound was
  concurrently deleted). IDL on the same shape is CX-F.
- **L16 concurrent double delete** — both branches delete the same node.
- **L17 ceiling escape, sequential** — a chain grows under an *open* key
  ceiling (every node a row head); a later head's key floor sees only the old
  head, not the chain's deep keys; deleting the chain re-sorts an escaped deep
  key above the newer head — flipping a co-displayed pair on ONE replica.
  Found by attempting the pen-and-paper proof of Q-tree's nesting invariant
  (2026-07-13), **not** by the battery — a suite-gap lesson. Sequential repair
  exists: floor a new head's key above the anchor's entire subtree max.
- **L18 merge-then-delete collapse** — the *concurrent* ceiling escape: B
  deepens a chain under an open ceiling while A concurrently inserts a new
  head; post-merge the pair is co-displayed, and deleting the chain flips it
  on the merged replica itself. **No birth-time floor can prevent this** (B
  cannot see A's key), so it is structural for eagerly-assigned immutable keys
  combined with splice-and-re-sort deletes. Lazy/relational orders (ghost,
  rose) and flat remove-only keys (Q-flat, whose delete never re-sorts) pass.
- **L20 tie inheritance** — concurrent same-anchor inserts carve *identical*
  ranges under any deterministic name-free scheme; each branch types a child
  under its own insert; post-merge, deleting the two heads must not reorder
  the children — the heads' tie verdict (by ts) must be *inherited* by their
  subtrees, but a child's own ts votes independently and can vote wrong.
  Kills `range-ts` (and flat-RGA, Q-tree). **The nameless-carving lemma**:
  pairwise display stability under concurrency forces a per-level
  disambiguator — the path is required by column d itself, not by the
  fooling pairs.
- **L21 stale frame** — a replica forks *before* a re-ranging merge and keeps
  carving in the old coordinates; the merge's re-carve moves its anchor's
  range; the stale number then meets re-carved numbers as siblings. Built to
  refute `range-repro` (the CX-F "numbers born in different computations"
  shape) — and it did not: two-branch scenarios let the LCA-precedence keep
  every sibling comparison inside one frame. The refutation needed L22.
- **L25 fold-verdict inheritance** — minimized from the DAG PBT's refutation
  of the delta-tree design (seed 0). A *repair* decides `10 before 6`
  (ts-descending); `22` is then typed under `6`, co-displaying `10 before
  22`; a branch that knew only `{6}` deletes it; the final merge must
  fold/rehome `6`'s children. **The dead parent's timestamp was load-bearing
  for the repair verdict**: designs that erase it (strictly dead-free folds,
  timestamp re-sorts) let the child re-litigate with its own newer ts and
  flip the co-displayed pair. Kills `delta-tree`, `flat-RGA`, `range-ts`,
  `range-splitN`; immutable-key designs inherit the verdict through the
  retained name. The companion mechanism (found on the `delta-tree-sf`
  repair, PBT seed 1): **repair non-locality** — re-slotting a node inside
  one overlap family perturbs its numeric relation to nodes *outside* it, so
  a pair tie-decided by ts at one merge is re-decided by position at a
  causally disjoint one. Together these close the mutation family: eight
  variants, eight countermodels.
- **L22 three-branch convergence** (KC's question) — three branches diverge
  from ONE initial version, each inserting under the same anchor (identical
  name-free carves); merge two, re-range, then merge the pending third. The
  re-ranged node carries a promoted number the late brancher never saw, so
  **the merge order leaks into the display**: `range-repro` reads
  `[1,20,30,10]` or `[1,30,20,10]` depending on topology — **convergence
  fails, refuting re-range-at-merge outright**. Bonus catch: `rose(Shesha)`
  also diverges here (`[1,30,10,20]` on one topology) — the rose merge is
  not topology-convergent, a defect its own 16k-merge PBT never surfaced.
- **L23 rescaled-children topology** — two different merge topologies, each
  followed by an insert *under a repaired/rescaled node*, then the final
  merges; both must read identically. `range-repro` fails (again);
  the local-split designs, paths, ghosts converge.
- **L24 frame mixing** (KC: "same node, different ranges at merge") —
  children of ONE node carved against *different frames* of it (stale-wide
  vs repaired-narrow) meet at a merge; **no deletes anywhere**, yet naive
  per-node value inheritance flips a co-displayed pair (`range-split`:
  `(62,61)`). Fixed by **frame normalization** (`range-splitN`): canonical
  range per node = the LCA's value (any shared node is an LCA node), each
  input's values rewritten top-down through the affine map input-frame →
  canonical frame, then the canonical overlap repair. Bonus catches:
  **`splice2` and `B2` flip four co-displayed pairs each on this
  delete-free scenario** — their read-time tie resolution is non-monotone
  under growth, an independent disqualification.

**Impossibility probes** (two-world; the suite verifies the fooling premise):

- **L14 oracle fooling (4-node)** — design-record §6. B deletes its own `g`
  (timestamp 2 in W1, 6 in W2); the tombstoned oracle requires opposite orders.
  `inputs identical: True` = that design is *provably* fooled (bounded state).
  Expected for every bounded tombstone-free design; only the tombstoned
  baseline — and unbounded-state designs (see findings) — answer both.
- **L15 strong-list (5-node)** — design-record §7½.3. Transitive constraints
  through dead nodes' past displays force opposite orders of two survivors
  that were never co-displayed.

**Multi-epoch:**

- **M1 two epochs** — merge output feeds a second diamond. Catches state
  degradation across epochs and key-space corruption (see findings — it
  caught a real bug in this suite's own first Q implementation).

## The designs

| column | design | provenance |
|---|---|---|
| `naive(spec)` | the sequential list spec itself (reference; no merge) | `Shesha.lean` SeqList |
| `tombstoned` | RGA with tombstones (oracle-faithful baseline; **not** tombstone-free) | `Sal/MRDTs/RGA_with_tombstones/` |
| `flat-RGA` | tombstone-free RGA: anchor only, newest-first, splice+re-sort on delete | `Sal/MRDTs/RGA/` (proved RA-lin w.r.t. own fold) |
| `rose(Shesha)` | rose-forest, order-preserving splice, skeleton/marker merge | `sl_pbt.py`, design record §§2–4; refuted `Shesha_Rows_Refuted.lean` |
| `splice2` | symmetric-splice two-tree (after + before, both spliced) | design record §9 (refuted) |
| `B2(bare)` | immutable birth records `(after,before)`, delete=remove, ghost read | this exploration |
| `ghost(spine)` | birth records + carried ancestry spines, delete=remove; newest-first read ties | `sibling-origin-pbt.py`, `sibling-edge-design.pdf` (0 anomalies / 37k sweeps) |
| `ghost-cf` | same state as `ghost(spine)`; the read's tie rule follows the just-emitted node's own chain before falling back to newest-first | the L19 h-fix (2026-07-13) |
| `Q-flat` | immutable `(N,Q,char)`, Q = dense position identifier, read = sort | the Q proposal (flat instantiation) |
| `Q-tree` | RGA tree + bounded sibling keys `Q(x) ∈ (max(Q(anchor),Q(head)), Q(A))` | the Q proposal (tree instantiation) |
| `path-key` | key = ancestor path of uids, lex sort (prefix = KC's "carved Q range"; one-sided) | the range proposal made concurrency-sound; StoredPath's shape |
| `path-2` | **the full two-sided path scheme**: records `(id, pos, char)`, pos = ancestor path of `(side, uid)` components (`L↦(0,uid)`, `R↦(2,−uid)`, node terminator `(1,)`), insert = L-child of `r` if `r` inside `l`'s subtree else R-child of `l`, delete = remove, merge = OR-set + verbatim, read = tuple sort | the surviving design, eager encoding (Fugue id-space) |
| `range-ts` | KC's written-down scheme: each node = a bounded range binary-split from the parent's free gap, NO names; ts breaks range ties; tree read | the ranges-without-paths proposal |
| `range-repro` | `range-ts` + KC's re-range-at-merge: the merge re-carves all ranges canonically (order-preserving, oldest-lowest), restoring disjoint nesting | the reprojection proposal |

## Headline results (full matrix: `litmus_matrix.md`, generated)

Failures only — everything not listed passes:

| design | fails |
|---|---|
| `tombstoned` | nothing (baseline; pays permanent tombstones) |
| `flat-RGA` | L1, L2/W1 (**provably fooled** — states identical), L8·L9·L13 (S6/S7), **L18 (d!)**, L14+L15 fooled |
| `rose(Shesha)` | **L4 (its refutation, reproduced)**, **L22 (merge not topology-convergent — new)**, L9 (S6/S7), L14+L15 fooled — but passes L17/L18/L19/L20 (order lives in links) |
| `splice2` | L2/W2 (**provably fooled**), L4 (S4!), L11 (S4!), L17, L18, L14 fooled |
| `B2(bare)` | L3a (deep chain), L17, L18, L14/W2 (ghost rank unknowable) |
| `ghost(spine)` | **L19 — backward runs interleave** (retracting the earlier "passes everything": the battery lacked an h test). The R-chains are in the state; the newest-first read tie walks across them — a read artifact, not a state deficiency (see `ghost-cf`) |
| `ghost-cf` | **nothing — the full battery including L19 and both impossibility probes** (same state as ghost; chain-following tie rule) |
| `path-2` | **nothing — the full battery** (L1–L22, both probes both worlds). The eager-encoding twin of `ghost-cf`: same information as the spines, stored as sort keys; read = a tuple sort |
| `Q-flat` | L7 (interleaving), L19, L14 fooled — passes L17/L18 (delete never re-sorts) |
| `Q-tree` | **L17 (S1/S2 — sequential!), L18 (d on the merged replica)** — the ceiling escape, structural for eager keys + splice; plus L9+L13+L15/W1 (licensed e-class), L19, L14 fooled |
| `path-key` | **L19 only** (one-sided: no `before` information — needs the two-sided/Fugue form). Passes everything else, including both fooling probes and L17/L18: prefix-ranges are fixed in the causal past of everything inside them, so concurrent operations cannot escape them |
| `range-ts` | **L20 (the nameless-carving refutation)**, L19, L14 fooled — passes L17/L18 (bounded ranges fix the ceiling escapes without paths) |
| `range-repro` | **REFUTED — L22 + L23: convergence fails across merge topologies** (KC's three-branch scenario). Passes L20/L21, which is why two-branch testing looked clean; the third concurrent branch exposes the frame leak |
| `splice2`, `B2` (addendum) | **also fail L24** — four co-displayed pairs flipped on a delete-free, pure-insert scenario: their read-time tie resolution is non-monotone as elements arrive |
| `range-split` | **L24 (frame mixing — KC's same-node-different-ranges question)**: raw per-node value inheritance mixes affine frames among siblings; plus L19, L14 fooled. Passes L17/L18/L20/L21/L22/L23 |
| `range-splitN` | **REFUTED — DAG PBT (43/120) + L25**; the frame normalization is not globally canonical, and the fold erases repair verdicts |
| `delta-tree` (in `delta_tree.py`) | KC's full design (parent-relative fractional ranges, isometric-fold delete, LCA-revert merge, local overlap-split). **Battery-clean incl. L20–L24, but REFUTED by the DAG PBT (43/120) and L25**: the fold via the LCA's frame erases repair verdicts — the dead parent's ts was load-bearing |
| `delta-tree-sf` (in `delta_tree.py`) | the source-consistent-fold repair: **fixes L25, still REFUTED by the DAG PBT (41/120)** — repair non-locality re-decides ts-tied pairs by position at causally disjoint merges |

**Correction (2026-07-13, same day):** an earlier revision of this file said
Q-tree "passes S4/d in every case." That was a battery artifact — the battery
lacked L17/L18. Q-tree fails the adopted spec (d), sequentially at L17 and
structurally at L18.

## Findings the suite produced on day one

1. **It reproduces every known refutation** from named tests: L1 (flat RGA),
   L2 with the state-identity bit proving the splice fooling, L4 = the
   `Shesha_Rows_Refuted` countermodel giving `[3,4,2]` and failing S6/S7.
2. **The suite locates exactly where Q-tree's licensed e-anomalies live
   (new).** The sibling bound "`Q(x) < Q(A)`" is vacuous when the anchor is
   the *newest* sibling (no A exists); keys born in that open interval lose
   cross-branch comparability, and the merge can contradict the *transitive*
   closure of displays routed through a dead node (L9, L13, L15/W1 — S6/S7
   only; **S4 holds in every case**). In the anomaly-matrix vocabulary this
   is precisely a **column-e (strong-list) failure with column d intact** —
   the class the adopted spec (§7¾) licenses, and that L15 proves unavoidable
   for bounded tombstone-free state. It is *not* the Shesha disease: Q-tree's
   merge is the fold of its own operations under every order (keys are
   carried on the ops and commute), so own-fold RA-linearizability is
   untouched. The flat rule — bound by the *display successor*, which always
   exists — closes these particular e-instances, but pays with interleaving
   (L7, columns g/h): a rung trade, not a dominance.
3. **Naive midpoint-fraction keys are unsound (new — caught by M1 only).**
   Two concurrent inserts into one gap pick the same rational; the sub-gap
   between them is then *empty* and a later insert misplaces. Dense keys must
   put the uid **inside the order** (hierarchical position identifiers), not
   in a sort tie-break. This is why M1 is in the battery.
4. **`ghost(spine)` passes everything, including both impossibility probes** —
   consistent, not contradictory: the impossibility theorems quantify over
   *bounded* states, and the spines grow with birth-ancestry depth (a dead
   node's id and rank survive in survivors' spines). The escalated fooling
   chains of design-record §6 push the required spine depth up; they never
   refute it. The price is exactly that growth.
5. **The S4/S6 gap is where "licensed divergence" lives.** flat-RGA and
   Q-designs fail S6/S7 on tests where S4 still holds: the flips involve pairs
   never co-displayed. A design's published contract should state which rung
   (S4 vs S6 vs S7) it stands on — S7 is provably out (L15), S4 is achievable
   tombstone-free, S6 requires either spines or... this is the open design
   question, now stated as a row of checkmarks instead of prose.
6. **splice2 fails S4 outright** (L4, L11) — it is *below* the rose tree on
   the ladder, not beside it; its cheapness bought nothing.
7. **Ranges/prefixes rescue eager keys; scalars stay dead (path-key, new).**
   KC's "carve a Q *range* per node" proposal, made concurrency-sound
   (disjointness under concurrent carving forces a uid per level), is
   path-shaped keys — and it passes L17/L18 and both fooling probes: a
   subtree's prefix is fixed in the causal past of everything inside it, so
   the L18 quantifier over unknown concurrent keys collapses to a known
   interval. Depth grows *inside* the prefix instead of escaping upward. The
   surviving weakness is exactly the missing `before` side (L19): the
   one-sided form is StoredPath; the two-sided form is the Fugue id space —
   and it is the spine, promoted from record field to sort key. Precision
   growth = spine length: the same rent in key clothing.
8. **The battery had no h test; adding one (L19) retracted a headline.**
   `ghost(spine)` interleaves backward runs — its 0/37k record and "passes
   everything" were artifacts of workloads and tests without prepend runs.
   The state carries the R-chains; the plain newest-first Kahn tie walks
   across them. `ghost-cf` (identical state, tie rule follows the just-emitted
   node's chain) is clean on the full battery including L19 — evidence the
   defect is in the read's tie rule, not the design. Promotion of the fix
   into the design note/model and a backward-run PBT sweep are owed.
9. **The nameless-carving lemma (L20, new).** Bounded ranges (KC's scheme)
   genuinely fix the ceiling escapes without retaining any dead name — but
   deterministic name-free carving hands concurrent same-anchor insertions
   *identical* ranges, and after the anchors die no function of (range,
   own-ts) can order their descendants consistently with the merged display.
   The tie verdict must be inherited subtree-wide, which requires a per-level
   identifier: **the path is forced by pairwise display stability itself**,
   independent of the oracle/strong-list fooling pairs.
10. **Re-ranging at merge is REFUTED (L22 — KC's three-branch question).**
   Reprojection fixes L20 and survived every *two-branch* attack (L21) —
   because with two branches the LCA-precedence keeps each sibling
   comparison inside one frame. Three branches from one version break it:
   after merging two, the re-carve promotes a node's number; the pending
   third branch arrives with old-frame numbers; the resulting sibling sort
   depends on *which two merged first* — **convergence fails**, the fatal
   class. Consequence: the self-compacting-precision escape from the
   retention rent is closed. With scalar keys dead (L17/L18), nameless
   ranges dead (L20), and reprojection dead (L22), the wall is now
   three-sided: **the ordering guarantees require remembering the dead — as
   names (paths), relations (spines/ghosts), or entries (tombstones).**
11. **The rose-tree merge is not topology-convergent (L22, new).** Three
   same-anchor concurrent inserts merged in different orders read
   differently (`[1,30,20,10]` vs `[1,30,10,20]`). Sixteen thousand PBT
   merges and the entire Lean campaign never exercised this shape — found
   by a 4-insert scenario the moment the right question was asked.
11. **The verdict-inheritance principle, and the triangle is fully witnessed
   (L25 + the delta-tree PBT campaign, new).** When concurrent same-position
   content is ordered by a timestamp tie at repair time, that verdict is a
   fact about the *pair* of timestamps — including, later, a dead node's.
   Strictly dead-free designs erase the dead ts (the fold), so descendants
   re-litigate with their own newer ts (L25); and repairs are *non-local* —
   re-slotting inside one family perturbs relations outside it, so
   ts-decided pairs get re-decided by position at causally disjoint merges
   (delta-tree-sf). Eight mutation-family variants, eight machine-checked
   countermodels. Each pairwise corner of {strictly dead-free, pairwise
   display stability, topology-convergence} now has a witness: rose has the
   first two (fails L22); the delta-tree family has the first and third
   (fails L25/PBT); the immutable-key designs have the last two (retain
   dead names). Conjecture: the triple is unachievable — the dead node's
   timestamp is load-bearing for orders it participated in.
12. **Eager keys go stale; lazy references don't (L17/L18, new).** A Q key is
   the ancestry *arithmetized at birth* — evaluated eagerly against the state
   the inserter saw. A spine/ghost reference is the same information evaluated
   *lazily* at read time, against whoever is currently alive. Concurrent
   deletes are precisely where eager evaluation goes stale: a key comparison
   frozen at birth cannot adapt when the structure it summarized is deleted
   (L18: no birth-time floor can see a concurrent sibling's key). This is why
   `ghost(spine)` and `rose` survive the ceiling escape and eager-key trees do
   not — and why "the tree, arithmetized into keys" is *not* a conservative
   transformation of "the tree, kept as relations."

## Randomized DAG PBT (`pbt.py`)

`python3 pbt.py [N]` — N random executions per design, parameterized by
(#replicas, #rounds, ops/round, delete ratio, merge probability): honest
clients, LCA-disciplined random merges (a merge fires only when a recorded
version's event set equals the heads' intersection), forced convergence
rounds driving all replicas to the full event set along different paths.
Checks the scalable ladder subset: **FLIP** (global pairwise display
stability, across every read of every replica), **CONV** (same event set via
different topologies ⟹ same read), **LIVE/DUP** (survival correctness).
Interleaving (g/h), strong-list (e), and S6 remain litmus territory.

**First-run verdicts (120 executions/design):** CLEAN — `tombstoned`,
`ghost(spine)`, `Q-flat`, `path-key`, `path-2`. FAILING — `flat-RGA`,
`splice2`, `B2`, `rose` (flips at merges — beyond its known L22 divergence),
`Q-tree`, `range-ts`, `range-repro`, `range-split`, **and two of this
suite's own fixes**: `ghost-cf` (the chain-following tie rule added for L19
is pairwise-UNSTABLE at random DAG shapes — retracted; ghost's L19 remains
open, and the principled fix is to adopt path-2's structural in-order
comparison over the spine data, which makes it path-2) and `range-splitN`
(the frame normalization is not globally canonical: "canonical = the current
merge's LCA" differs across merges — the mutation family's hole at yet
another depth). **Net: `path-2` is the unique design clean on the full
litmus battery AND the randomized DAG sweep.**

## Adding a design / a test

New design: subclass `Design` (four methods + `fp` for fooling-pair state
identity), append to `DESIGNS`. New anomaly: add the history to the scenario
tables with a one-line provenance comment — and if it came from a refutation,
cite the machine-checked artifact.

Every test here is a candidate Lean SPOT for whichever design gets ported.
