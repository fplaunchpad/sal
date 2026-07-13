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

| clause | meaning |
|---|---|
| **S1** sequential soundness | a single replica's final read equals the naive-list fold of its script (the "obvious spec": insert-after places immediately right of the anchor; delete removes) |
| **S2** step display stability | no two consecutive reads of one replica flip a surviving pair |
| **S3** merge convergence | `merge(L,A,B)` reads equal to `merge(L,B,A)` |
| **S4** pairwise display stability | no pair displayed by any LCA/branch read flips in the merge read (the spec adopted in the design-record §7¾) |
| **S5** non-interleaving | designated concurrent runs stay contiguous, in run order |
| **S6** list-linearizability | the merge read equals the naive fold of **some** causal interleaving of the branch scripts |
| **S7** strong-list closure | the merge read respects the **transitive closure** of all displayed pairs (Attiya et al.-style; provably unachievable tombstone-free — see L15) |
| **DUP** | no element duplicated in a merge read |
| **IDL** | idle-branch identity: `merge(L, A, L) ≃ A` (the CX-F "frame mismatch" essence: an idle branch must contribute nothing) |

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
| `ghost(spine)` | birth records + carried ancestry spines, delete=remove | `sibling-origin-pbt.py`, `sibling-edge-design.pdf` (0 anomalies / 37k sweeps) |
| `Q-flat` | immutable `(N,Q,char)`, Q = dense position identifier, read = sort | the Q proposal (flat instantiation) |
| `Q-tree` | RGA tree + bounded sibling keys `Q(x) ∈ (max(Q(anchor),Q(head)), Q(A))` | the Q proposal (tree instantiation) |

## Headline results (full matrix: `litmus_matrix.md`, generated)

Failures only — everything not listed passes:

| design | fails |
|---|---|
| `tombstoned` | nothing (baseline; pays permanent tombstones) |
| `flat-RGA` | L1, L2/W1 (**provably fooled** — states identical), L8·L9·L13 (S6/S7), L14+L15 fooled |
| `rose(Shesha)` | **L4 (its refutation, reproduced)**, L9 (S6/S7), L14+L15 fooled |
| `splice2` | L2/W2 (**provably fooled**), L4 (S4!), L11 (S4!), L14 fooled |
| `B2(bare)` | L3a (deep chain), L14/W2 (ghost rank unknowable) |
| `ghost(spine)` | **nothing — including both impossibility probes** |
| `Q-flat` | L7 (interleaving), L14 fooled |
| `Q-tree` | L9+L13+L15/W1 (all the same open-boundary defect, S6/S7), L14 fooled |

## Findings the suite produced on day one

1. **It reproduces every known refutation** from named tests: L1 (flat RGA),
   L2 with the state-identity bit proving the splice fooling, L4 = the
   `Shesha_Rows_Refuted` countermodel giving `[3,4,2]` and failing S6/S7.
2. **Q-tree has an open-boundary defect (new).** The sibling bound
   "`Q(x) < Q(A)`" is vacuous when the anchor is the *newest* sibling (no A
   exists); a concurrent front insert then lands key-tied with subtree content
   and can violate the transitive display closure (L9, L13). The flat rule —
   bound by the *display successor* — is strictly stronger and passes both.
   Any Q-tree design must inherit the enclosing boundary instead of ∞.
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

## Adding a design / a test

New design: subclass `Design` (four methods + `fp` for fooling-pair state
identity), append to `DESIGNS`. New anomaly: add the history to the scenario
tables with a one-line provenance comment — and if it came from a refutation,
cite the machine-checked artifact.

Every test here is a candidate Lean SPOT for whichever design gets ported.
