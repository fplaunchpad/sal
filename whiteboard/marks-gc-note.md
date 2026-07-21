# GC for the Peritext marks layer: retention roots vs early re-anchoring

Status: Python-validated (task #110 phase 1). Harness:
`whiteboard/litmus/marks_gc_check.py` (self-contained model, directed cases
with hand-derived expectations, randomized DAG PBT against a never-compacted
twin). No Lean in this phase; section 8 records the theorem shapes the
surviving attack owes.

## 1. The problem

The runtime Peritext datatype (`runtime/src/datatypes/peritext.js`) keeps
text deletes logical: the state carries a shadow of every character ever
inserted (its embed coordinate is a birth constant) plus a grow-only deleted
set, because the mark resolver needs the birth position of DEAD boundary
anchors. Consequently the state-GC pass (`runtime/src/compact.js`), which
drops settled-dead ranges and renumbers coordinates for the plain text
datatype, currently refuses to compact Peritext: pruning a dead anchor's
record would destroy exactly the position a mark needs to rehome. The goal
of #110 is to remove that refusal soundly. This note designs and validates
two candidate attacks and records which one survives.

## 2. The read model, natively

State. Text is an insert-only shadow: a map from character id (a Lamport
timestamp, globally unique, exceeding the id of the insert's anchor) to an
immutable coordinate, plus a grow-only set of deleted ids. A coordinate is
the chain of birth deltas: the insert of `x` after anchor `a` stores
`coord(a) ++ [x - a]` (the document root is the empty chain). Marks are a
grow-only map from mark id `mid` (also a Lamport timestamp) to an immutable
record `(mid, mtype, op, startId, endId, startSide, endSide)`, `op` in
`{add, remove}`.

Reading order (R1). Coordinates sort birth-chain lexicographically: an
ancestor precedes its whole subtree (a chain precedes its extensions), and
among children of one anchor, larger deltas, that is NEWER timestamps, sort
first (RGA recency). The live order is the reading order filtered by the
deleted set. This order is machine-verified in the harness against the
validated embed model (`embed_tree.py`), sequentially and across merges.

Boundary resolution (R2, R3). Each boundary resolves to a live index:

* start, anchor live, side `before` (inner): the span starts at the anchor.
* start, anchor live, side `after` (outer): the span starts after the
  anchor, additionally skipping the contiguous run of live characters newer
  than the mark (`id > mid`).
* start, anchor dead, side `before`: rehome RIGHT: the nearest surviving
  character in reading order scanning right from the anchor's birth
  position; scan exhausted means the whole mark collapses (covers nothing).
* start, anchor dead, side `after`: rehome LEFT; scan exhausted means
  document start.
* end, anchor live, side `after` (inner): the span ends at the anchor and
  then GROWS right over the contiguous run of live characters newer than
  the mark.
* end, anchor live, side `before` (outer): the span ends before the anchor,
  stepping back over the newer-than-mark run.
* end, anchor dead, side `after`: rehome LEFT; exhausted means collapse.
* end, anchor dead, side `before`: rehome RIGHT; exhausted means document
  end.

Render (R4). Per (character, mtype) the covering mark with the highest mid
wins (LWW); a winning `remove` suppresses formatting. The rendered view is
the live order with each character's active mark set.

The harness resolver is a transliteration of the validated
`peritext_read_model.py` and is cross-checked against it two ways: on that
file's own directed examples (Ex1, Ex3, Ex7, Ex8, trilemma; expected
literals restated) and on 200 randomized histories, implementation versus
implementation, exact render equality.

## 3. The compaction model

Settled cut. Compaction happens at a barrier the whole group certifies:
every replica has delivered everything at or below the cut, and every op
concurrent with the cut that is not yet delivered is DECLARED in flight
(the straggler's id and anchor id). This is the same settled-cut contract
as the text-layer GC.

The map. Build the coordinate tree of the kept records. Drop the records of
settled-dead ids outside the keep-set (their chain levels survive inside
descendants' coordinates; no record is needed for that). Renumber each
sibling group of the kept tree order-preservingly to ordinals 1..k, EXCEPT
groups that receive a declared in-flight child: those keep their deltas
verbatim, because the straggler's already-minted delta must keep its order
against its siblings (renumbering the group can flip an order: siblings
with deltas 2 < 5 in flight < 9 renumber to 1, 2 and the frozen 5 jumps the
ex-9). Beyond-cut mints derive their coordinate from the re-coded anchor
record plus the fresh delta `id - anchor_id`; freshness dominates every
ordinal (ordinal i is at most the original delta i, which is below every
fresh delta), so new mints sort newest-first past the compacted block. This
is the extension law H3 of the stable-prefix-map cluster, realized as
derive-at-ingest.

The two attacks differ only in the keep-set and the mark treatment:

* H-A (retention roots): keep-set = live ids, union the boundary anchor ids
  of every present mark record (add and remove records both), union the
  anchors of declared in-flight ops. Dead boundary anchors survive as dead
  records with re-coded coordinates; marks are untouched.
* H-B (early re-anchoring): at the cut, rewrite each DEAD mark boundary to
  the resolver's own cut-time rehoming target (nearest surviving neighbour
  on the side's scan direction, side kept; an exhausted scan becomes the
  side's collapse sentinel), then keep-set = live ids union declared
  in-flight anchors only: no mark retention.
* NONE (negative control, the current refusal's reason): no mark retention
  and no rewrite. A mark whose dead anchor has no record degrades to the
  side's collapse branch.

## 4. Hypotheses, falsifiable forms first

* H-A: after compaction at any settled cut, `renderMarksDoc` is identical
  to the never-compacted twin for EVERY beyond-cut continuation (text
  insert/delete, mark add/remove, on any replica, merged in any order,
  declared stragglers delivered late), at every epoch (successive cuts
  composed). Falsifier: any version whose render differs from the twin.
  Sub-claims: A1 (the relabeling preserves the coordinate order on the
  whole kept set, retained-dead included), A2 (dropped interior dead
  records are invisible to the resolver), A3 (an add+remove pair and its
  retention roots become droppable under a guard). Cost claim: retained
  extra records at most 2 per mark record, measured.
* H-B: same reads-identical statement. EXPECTED FALSE: the rewrite commits
  at the cut to information the resolver would otherwise read at render
  time (the dead anchor's position among later arrivals). If refuted, the
  weaker true statement is: all compacted replicas still converge among
  themselves, so the divergence is only against the uncompacted twin, a
  licensed semantic change at the settled cut. The weaker claim is
  machine-checked separately and is NOT H-B succeeding.
* NONE: must demonstrably flip a read (this justifies the runtime's current
  refusal; if it did not flip, the refusal would have been vacuous).

## 5. Hand-worked directed derivations

All expected values below are derived on paper from R1..R4 and only then
machine-checked; the harness never evals the model under test to produce an
expectation.

### 5.1 D1: the countermodel family for H-B

Geometry: `R` (id 1) and `L` (id 2) minted concurrently at the root, so `L`
is newer and reads first; `d` (id 3) is a child of `L`. Reading order
`L d R`. One mark, mid 5. Delete `d`, cut, then one continuation insert `n`
anchored at `L` or at `d`:

* (a) beyond-cut insert, id 10 (newer than the mark), anchored at `L`:
  lands between `L` and `d`'s old position;
* (b) in-flight straggler, id 4 (OLDER than the mark), anchored at `L`,
  declared at the cut, delivered after compaction: also lands between `L`
  and `d`;
* (c) in-flight straggler, id 4, anchored at `d` itself: lands between `d`
  and `R`.

Per combo (the mark's boundary at `d`, the other boundary on a survivor),
covered sets, twin first, H-B subject second:

| combo (boundary at d)        | (a) id 10 at L | (b) id 4 at L | (c) id 4 at d |
|------------------------------|----------------|----------------|----------------|
| start `before` (inner)       | {R} = {R}      | {R} = {R}      | {n,R} vs {R} DIVERGES |
| start `after` (outer)        | {R} = {R}      | {R} vs {n,R} DIVERGES | {n,R} = {n,R} |
| end `after` (inner)          | {L,n} = {L,n}  | {L,n} vs {L} DIVERGES | {L} = {L} |
| end `before` (outer)         | {L} = {L}      | {L,n} = {L,n}  | {L} vs {L,n} DIVERGES |

Worked sample, end `after`, variant (b). Twin: birth order `L n d R`; the
dead end anchor `d` scans left and finds `n` live, so the span ends at `n`:
covered {L, n}. H-B rewrote the end at the cut (before `n` existed) to `L`;
at render the end sits at `L` and end-growth does not cross `n` because
`n`'s id 4 is below the mark's mid 5: covered {L}. The straggler sits
inside the twin's span and outside the subject's.

Finding (the compensation lemma, negative space of the countermodel): in
column (a), with a beyond-cut NEWER insert, all four combos agree. The
reason is exact, not lucky: every character that appears between the
rewrite target and the dead anchor's old position after a settled cut is
either a beyond-cut mint (id above every settled id, hence above the mark's
mid, so the newer-run growth and skip rules cross it on both sides of the
comparison) or a declared straggler (the only source of ids BELOW the
mark's mid). And nothing beyond-cut can land between a settled-dead anchor
and its reading-order successor without anchoring in the dead subtree,
which a settled cut makes invisible to future minters; only a straggler
anchored at the dead node itself can, which is column (c). So the H-B
countermodel NEEDS an in-flight straggler (columns b, c), or death of the
rewrite target (D1d below): the directed candidate with only a beyond-cut
newer insert does not fire. Machine-confirmed cell by cell.

### 5.2 D1(d): pure beyond-cut divergence via double death

Chain `L` (1) root, `d` (2) child of `L`; mark start `L` `before`, end `d`
`after`, mid 5; delete `d`; cut (H-B rewrites the end to `L`); beyond the
cut insert `n` (10) under `L`, then delete `L`. Twin: birth `L n d`, live
`{n}`; the start rehomes right to `n`, the dead end anchor `d` scans left
and finds `n`: covered {n}, `n` is bold. H-B subject: the rewritten end
anchor `L` is now dead too and scans LEFT from `L`'s position, where
nothing lives (`n` sits to `L`'s right, unreachable by that scan): the mark
collapses, `n` is plain. DIVERGES with no straggler anywhere: the rewrite
also forgets that `d` sat to the RIGHT of `L`, so the re-rehoming scans
from the wrong birth position.

### 5.3 D3: two boundaries in one dead run

Chars `A` (1) root, `x` (2) child of `A`, `y` (3) child of `x`, `B` (4)
child of `y`; mark m1 covers [A..x] mid 10, mark m2 covers [A..y] mid 11,
both inner sides; delete `x` and `y` (one dead run); cut; declared
straggler `g` (5) anchored at `x`, delivered after compaction. `g` is a
newer child of `x` than `y`, so birth order is `A x g y B`. Twin: m1's end
(`x`, dead) scans left to `A`: covered {A}; m2's end (`y`, dead) scans left
to `g`, which is live: covered {A, g}. So `g` carries m2 and not m1: the
two boundaries' order inside the dead run is observable. H-B rewrote both
ends to `A` at the cut (the run's left survivor): both marks cover {A} and
`g` loses m2. H-A retains `x` and `y` as dead records whose re-coded
coordinates keep their relative order (A1), and reads exactly as the twin.

### 5.4 D6: the no-retention flip (why the refusal was correct)

D1 geometry, mark start `L` `before`, end `d` `after`, mid 5, `d` dead,
cut, no continuation needed. Twin: the end rehomes left from `d` to `L`:
covered {L}, `L` is bold. NONE subject: `d` has no record, the resolver
cannot place the scan and degrades to the collapse branch: covered {},
`L` is plain. FLIP. Companion: the same compactor with all mark anchors
live reads twin-identical, so the refusal's reason is precisely dead mark
anchors, nothing else.

### 5.5 D7: the A3 drop, its guard, and a new corner

Pair shape: add m and remove r, same mtype, same boundary ids AND sides,
`r.mid > m.mid`. Since both records resolve identically forever, r beats m
on every covered character; dropping both plus their retention roots looks
render-neutral. Two corners say the naive guard is not enough:

* (alpha) settledness: a concurrent same-mtype add s with
  `m.mid < s.mid < r.mid`, still in flight at the drop. With the pair
  present, r suppresses s on the overlap; with the pair dropped, s formats
  it. FLIP. Guard: the removal must be settled and no declared in-flight
  mark of the mtype may predate r.
* (beta) the growth window (a finding of this phase): a character w with
  `m.mid < w.id < r.mid`. The add's end-growth crosses w (`w.id > m.mid`)
  but the remove's does not (`w.id < r.mid` fails its newer test), so w is
  bold with the pair present and plain after the drop. FLIP even though
  the pair's boundaries are identical. Guard: no id strictly inside
  `(m.mid, r.mid)` may exist among settled or declared ids; future mints
  are Lamport-fresh (above r.mid), so the check at the cut is sufficient.
* (iii) LWW shadowing: any OTHER same-mtype mark older than r could be
  resurrected by dropping r on any present or future overlap (spans move
  under edits, so a no-overlap check now does not persist); the guard
  refuses when such a mark exists.

Hand-derived flips for (alpha) and (beta) and the guarded reads-identical
positive (with a genuinely dead root freed, which plain H-A would have
retained) are all machine-checked.

## 6. Results (machine verdicts, full run, exit 0)

Selfcheck (model fidelity): reading order vs the validated embed model
(directed newest-first case, 120 randomized histories with deletes, 80
randomized two-branch merges) all exact; resolver vs
`peritext_read_model.py` on its five directed histories (restated hand
literals) and 200 randomized histories, exact render equality. The task's
reading-order description (birth-chain lexicographic, newer children first)
matches the model; no correction was needed.

Directed: 22/22 PASS, every cell agreeing with the hand derivation of
section 5, including all eight D1 divergence/agreement verdicts, D1(d),
D2 (respan across the cut plus the whole-span-death companion, both
attacks twin-identical, A2 witnessed by the dropped interior record), D3,
D4 (growth across the cut, newer grabbed, straggler-older not grabbed),
D6 (flip), D7 (guarded positive plus both flips).

Randomized DAG PBT (2 to 3 replicas, 1 to 3 epochs per trial, random
merges, dead-anchor marks, declared stragglers delivered after compaction,
renders compared to the never-compacted twin at every version; the text
layer additionally checked structurally: the subject's birth order must be
the twin's filtered to the subject's records):

| attack | trials | cuts | straggler cuts | diverged | verdict |
|--------|--------|------|----------------|----------|---------|
| H-A    | 2000/2000 | 4048 | 2214 | 0 | VALIDATED |
| H-B    | 2000/2000 | 4048 | 2198 | 156 trials | REFUTED (reads-identical) |
| A3 (guarded, on top of H-A) | 600/600 | 1179 | 630 | 0, with 44 pair-drops fired | VALIDATED |
| NONE (negative control) | 600/600 | 1179 | 625 | 351 trials flipped | refusal justified |

H-B's weaker claim (all compacted replicas converge among themselves: the
boundary rewrite is computed once at the common settled cut, so subjects
share it; final full exchange gives identical renders) held in every trial,
2000/2000. This is a licensed semantic change at the cut, not H-B
succeeding: the twin divergences of section 5 are the price, and 156/2000
random trials paid it on top of the directed family.

## 7. Cost measurement (H-A)

Across 4048 compactions: 6630 dead records retained for marks against
24492 mark records present, mean 1.64 retained records per cut, mean 0.296
per mark record, maximum 2.000 (the claim bound of 2 per mark, never
exceeded; the bound is structural since a mark has two boundaries). GC
efficacy under the random workload: 3304 of 10812 settled-dead records
dropped (30.6 percent). The workload marks random ranges over a small
document, so a large share of dead characters are boundary anchors; real
editing traces have far fewer marks per character and would drop a larger
share. A3 recovers roots beyond that: each guarded pair-drop removes two
mark records and frees their anchors for the next cut.

## 8. Lean obligations for the surviving attack (theorem shapes only)

H-A is the survivor. The mechanization would sit next to the embed
re-coding cluster (`EmbedRGA_Recoding.lean`) and consume its vocabulary:

* O1 (keep-set stable-prefix map). The retention-roots relabeling is a
  `StablePrefixMap` whose domain is the KEPT coordinate set (live union
  mark anchors union declared in-flight anchors): H2 (order preservation)
  on kept pairs, H3 by derive-at-ingest, H1 derived. A1 of this note is
  exactly H2 restricted to record-bearing nodes. The in-flight freeze
  guard is the same side condition as the text layer's skipped groups.
* O2 (scan factorization, the A2 lemma). For a retained dead anchor a,
  "first survivor scanning from a's position" computed in the compacted
  birth order equals the same scan in the full birth order: removing
  non-surviving, non-anchor records from a sequence does not change the
  first survivor on either side of a retained element. A pure list lemma
  over `filter`, no datatype content.
* O3 (render congruence, the capstone). `renderMarksDoc` is a function of
  (the live id sequence, the positions of mark boundary anchors relative
  to that sequence and to each other, the id order used by LWW and
  growth). O1 transports the first and second (with the embed cluster's T2
  transporting the live sequence), ids are untouched, so renders are
  equal: reads-identical for every beyond-cut continuation whose mints
  satisfy H3 and whose stragglers are declared. Multi-epoch form by
  composing keep-set maps, the `chainSPM`/`CompatOn` route, with the
  collision caveat already pinned there (a root freed by A3 between epochs
  is exactly the rank-reclaim shape `naive_composition_collides` guards).
* O4 (A3 guarded drop). Removing an (add, remove) pair with equal boundary
  tuples and `r.mid > m.mid` preserves `renderMarksDoc` under guards:
  removal settled, no other same-mtype mark with mid below r.mid (declared
  in-flight marks included), and no id strictly inside (m.mid, r.mid)
  among settled or declared ids; plus the freshness fact that beyond-cut
  ids exceed r.mid. The two negatives (alpha, beta of section 5.5) are the
  SPOT companions; beta is the new guard clause this phase found.
* O5 (the honesty residue, shared). Nothing marks-specific: the settled
  cut plus declaration layer is the text compaction's protocol half
  (all-heads visibility, re-based honesty at the epoch boundary), already
  recorded as the open obligation of the re-coding cluster.

For H-B the honest statement worth keeping is the weaker one: the cut-time
rewrite is a common op-level transformation, so compacted replicas converge
among themselves; the divergence against the uncompacted history is a
semantic change licensed by settledness, with section 5's family as its
observable price. It should never be stated as reads-identical.

## 9. Relation to the task's directed candidate

Two model-vs-expectation notes, both machine-checked:

1. The reading-order description used to frame the task (birth-chain
   lexicographic, newer children first) agrees with the authoritative
   model; nothing to correct.
2. The H-B directed candidate as narrated (survivors L, R; dead older
   child d of L; beyond-cut newer insert n under L; expect the twin to
   rehome d's boundary to n while the rewrite pinned it to L or R) does
   NOT diverge by itself: the rehome target differs but the covered set
   does not, because the newer-run growth and skip rules bridge the gap
   between the cut-time target and the render-time survivor exactly when
   everything in the gap is newer than the mark, which a settled cut
   forces for all non-straggler continuations (the compensation lemma,
   section 5.1). The countermodel fires once the gap contains an id below
   the mark's mid (a declared straggler, columns b and c) or the rewrite
   target itself dies (D1d). H-B is refuted all the same, but by those
   three shapes, not by the narrated one.

