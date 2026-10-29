# Loro text: RA-linearizability of a Fugue list with styles

## Research question

Yjs's list algorithm is RA-linearizable only under the strong list
specification (an insertion lands anywhere strictly between its recorded
neighbours), and its formatting fails in six concurrent classes and one
single-user class (`docs/yjs-oracle.md`). Loro's text is a different design
on both counts: its list is Fugue (Weidner and Kleppmann 2023), and its styles
are Peritext-like marks whose anchors are elements of the list, with an
expand behaviour configured per style key. Does the different design change
the answer?

## Claims and falsifiers

Stated before any schedule was run.

| Claim | Statement | Falsifier | Check |
| --- | --- | --- | --- |
| L0 | Convergence: replicas that have integrated the same changes display the same text and styles | two such replicas differ | `convergence` |
| L1 | Plain text is RA-linearizable under the strong list specification (gap rule); additionally record whether the one-sided rule `left` (immediately after the recorded left neighbour) and the two-sided rule `both` (immediately before the recorded right neighbour) admit every version | a version with no witness under the rule | `raLinearizability` under `gap`, `left`, `both` |
| L2 | Rich text is RA-linearizable under a marks specification of the Yjs shape: a mark or unmark over the identity interval from its first to its last selected character sets or clears its key on exactly the characters between them when it is applied; an insertion carries exactly the attributes the expand configuration of each key dictates at its issuing replica | a version with no witness | `raLinearizability` with styles |
| L2a | Local meaning: an insertion takes the attributes the expand rule computes from its visible neighbours; a mark or unmark changes exactly the selected characters; a delete removes exactly the selected characters | one disagreement with the list edit | `localMeaning` |
| L3 | Causal delivery: a change whose dependencies are absent is held back until they arrive, so partial delivery shows only causally closed versions, and nothing is lost after full synchronisation | a version no causally closed history admits; loss or divergence after synchronisation | `raLinearizability`, `conservation` under partial delivery |
| L4 | Determinism: the same request on the same display gives the same result on a replica that held the text container before receiving the state and on one that obtained it by importing a snapshot | the two disagree | `determinism` |

A falsifier of L2 is an implementation defect only if no reasonable reading of
the specification admits the view. Where a failure depends on a choice the
specification made, the alternative is stated, the refuted candidate is
recorded, and the result says which reading the implementation satisfies.

## Answer in brief

| Claim | Verdict |
| --- | --- |
| L0 | Holds: no convergence failure in 9,200 trials. |
| L1 | Holds under the gap rule. Both deterministic refinements are refuted: `left` by a hand-derived history of five inserts over three replicas (Fugue makes a head insert a left child of its right origin), `both` in 9 of 200 random trials (a right origin Loro records may be a tombstone). |
| L2 | Refuted as stated (L-001, boundary inheritance), and refuted under two further readings that give the expand configuration a meaning under concurrency. Holds, within the bounds searched, under a persistent-anchor reading in which a mark is a range between two list elements, and the expand configuration governs only where the issuing replica places its own insertion. |
| L2a | Refuted: four classes of local insertion that do not take the attributes the expand rule gives from the display (L-002 to L-005), three of them on a single replica. Marks, unmarks and deletes always had their local meaning. |
| L3 | Holds: Loro holds every change with a missing dependency pending, deletes and unmarks included; no causal gap, no conservation failure. |
| L4 | Holds: no determinism failure, created and opened replicas alike. |

Of the seven Yjs formatting classes, only boundary spread (Y-004) has a Loro
counterpart; marker ownership, redundant-opener cleanup, neighbour formatting
removed by a delete, overlapping same-key formats, the delete-set causal gap
and the opened-document family do not occur.

## Reality oracle

`loro-crdt` 1.17.1 from npm, pinned in `ra-pbt/instances/loro/package.json`
and by registry integrity and SHA-256 of the Node entry point, the
wasm-bindgen glue and the wasm binary (`ra-pbt/instances/loro/sources.json`;
`verify-sources.js` checks them offline before and after every run). The
release was built from the tag `loro-crdt@1.17.1` (commit `6114e10e`), whose
Rust source was read for every mechanism below. It loads under Node v26.3.1.

### Identities

Each request is one transaction followed by `commit()`. The op id Loro gave
each character is read with `LoroText.getCursor(i).pos()`, which returns the
id `{ peer, counter }` of the character at visible index i. For an
insertion the ids are checked against the replica's version vector before
and after the commit: the insertion must have created exactly one counter per
character, and the characters at the inserted positions must carry exactly
those counters in order. Style anchors take counters too (a mark or unmark
creates two ops), so the check also catches any offset. The JSON update
format is not used for this, since it records insertions by entity position,
not by id; it gives the ids of mark ops, which the persistent reading needs.
`getDeepValueWithID` covers containers, not characters.

A record's `update` is `export({ mode: 'update', from: vvBefore })`, exactly
the ops the commit created; `deliver` imports it. Loro merges consecutive
local commits into one change, which does not affect the export, since it
slices by counters. A change whose dependencies are missing is held in
`pending_changes` (`oplog.rs` 50-60); `hasPending` is
`exportPendingUpdates() !== undefined`, and a record is integrated exactly
when the oplog version vector covers its counter range. An opened replica is
a fresh `LoroDoc` that imports the source's snapshot (and any pending
updates) before its text container is first touched; a created replica
holds the container from construction. A request Loro records no op for (a
mark over characters that already carry the value, an unmark over characters
without the key, `handler.rs` 2576-2604) is rejected and dropped.

The style configuration is local to a document, not replicated, and an
unconfigured key cannot be marked (`StyleConfigMissing`). Every replica
configures `bold` (expand after), `link` (none), `sup` (before) and `hl`
(both), one key of each expand type; the expand type is also stored in each
mark op, which is what remote replicas use.

## Specification choices

`ra-pbt/instances/loro/spec.js` and `anchored.js` import nothing from Loro.
A state is a list of characters with identities; deleted characters stay as
anchors for later insertions. Delete marks by identity and is idempotent.
Every insertion records its visible neighbours at issue time; a multi-character
insertion records each character after the previous one.

**Insertion rules.** `gap`: strictly between the recorded neighbours (the
strong list specification, relational). `left`: immediately after the recorded
left neighbour, ignoring the right one, so a later-applied sibling lands
nearer its anchor (RGA). `both`: immediately before the recorded right
neighbour when there is one. In plain text the recorded left neighbour is
exactly Loro's `origin_left` (the visible element at the position,
`crdt_rope.rs` 86); Loro's `origin_right` is the next element in its list,
which may be a tombstone, and the API does not expose tombstones, so `both`
is tested against the visible right neighbour.

**Readings of the expand configuration.** The local meaning of an insertion is
fixed: for each key, the common value when both visible neighbours carry the
same one, else the left neighbour's when the key expands after, else the
right neighbour's when it expands before, else none (`expandAttrs`). Five
readings of what this means once replicas are concurrent were tested:

| Reading | Insertion | Mark over `left..right` |
| --- | --- | --- |
| `carry` (the L2 statement) | carries the attributes it was issued with | covers its identity interval when applied |
| `inherit` | takes `expandAttrs` of its visible neighbours when applied | covers its identity interval |
| `expand` (Peritext's intent) | as carry | also covers the gap to the issuer's outer neighbour on each side its expand type extends to (an unmark by Loro's reversed type) |
| `anchors` | as carry | also covers any adjoining part of either boundary gap, whatever the expand type (relational) |
| `persistent` (`anchored.js`) | lands where the marks its issuer knew give it its carried attributes; either side of anchors of marks it did not know | a range between two anchor elements placed by the gap rule; a character takes the last-applied enclosing mark of each key |

The readings agree on every history in which no character is inserted
concurrently beside a mark's boundary.

`experiments/loro-oracle/spec-tests.mjs` checks the specification on 17
hand-derived blocks, each with an inequality against the tempting wrong
answer.

## Results

Each run is 200 seeded trials over two or three replicas (four in
`plain-gap-long-26`), witness search on versions with at most the bound of
edits. Readings run on the same seeds execute the same schedules. 9,200 trials,
72,727 edits and 135,417 checked versions in all
(`experiments/loro-oracle/results/campaign/`). Convergence, determinism and
conservation failed nowhere, no execution anomaly was recorded, and no
causal gap occurred.

The tables are from the rerun of 2026-10-29 with the full witness search
(every admitted placement explored, views compared without identities, at
most one million explored states per version), replacing the campaign
whose search was directed by the target's identity order, a pruning that
can reject a view that has a witness when characters repeat. The rerun
changed no verdict: every failing trial of the directed campaign fails
again, except one trial of `styles-created-32-expand` whose versions
exceed the state cap (it fails again at three million states). Versions
over the cap are counted as truncated and neither passed nor failed: 878
of 135,417 across the 46 runs, most of them in the plain gap-rule runs
(68, 144, 203 and 33 in `plain-gap-21`, `plain-gap-22`,
`plain-gap-long-26` and `partial-plain-27`) and the anchors reading (133
and 55 in `styles-created-31-anchors` and `-32-anchors`), where the
directed search had found a witness for each.

Plain text:

| Run | Rule | Requests / bound | Edits | Versions checked | Failing trials |
|---|---|---|---:|---:|---:|
| plain-gap-21 | gap | 12 / 12 | 1,941 | 3,148 | 0 |
| plain-gap-22 | gap | 12 / 12, 3 replicas | 2,056 | 3,456 | 0 |
| plain-gap-long-26 | gap | 16 / 12, 4 replicas | 2,861 | 4,288 | 0 |
| partial-plain-27 | gap | 12 / 12, partial delivery (216 sends left pending) | 1,814 | 3,195 | 0 |
| plain-left-23 | left | 12 / 12 | 1,956 | 3,184 | 0 |
| plain-left-long-24 | left | 20 / 14, 3 replicas | 3,337 | 4,242 | 0 |
| plain-both-25 | both | 12 / 12 | 1,975 | 3,204 | 9 |

Two further `left` searches (`results/left-search-41.json`, 2,000 trials of
20 requests over three replicas, and `left-search-42.json`, 1,000 trials of 16
over four) found no failure either; the refutation of `left` is the
hand-derived regression below, so the generated search does not reach that
shape.

Styled text, failing trials by check (RA-linearizability / local meaning;
local meaning does not depend on the reading):

| Seed and mix | carry | inherit | expand | anchors (bound 10) |
|---|---:|---:|---:|---:|
| 31 created replicas | 28 / 11 | 25 / 11 | 33 / 11 | 0 / 11 |
| 32 created replicas | 23 / 4 | | 29 / 4 | 0 / 4 |
| 33 opened replicas | 56 / 13 | 46 / 13 | 33 / 13 | 1 / 13 |
| 34 opened replicas | 53 / 11 | | 37 / 11 | 4 / 11 |
| 35 partial delivery, opened | 54 / 12 | 47 / 12 | 42 / 12 | 0 / 12 |
| 36 partial delivery, created | 22 / 3 | | 31 / 3 | 1 / 3 |
| total (1,200 trials) | 236 / 54 | | 205 / 54 | 6 / 54 |

Twelve requests per trial, bound 12 except where noted. The same seeds with
eight requests and bound 8, where the persistent reading is tractable:

| Seed and mix | carry | anchors | persistent |
|---|---:|---:|---:|
| 31 created | 7 / 2 | 0 / 2 | 0 / 2 |
| 32 created | 4 / 2 | 0 / 2 | 0 / 2 |
| 33 opened | 20 / 2 | 0 / 2 | 0 / 2 |
| 34 opened | 19 / 1 | 1 / 1 | 0 / 1 |
| 35 partial, opened | 31 / 3 | 0 / 3 | 0 / 3 |
| 36 partial, created | 5 / 0 | 0 / 0 | 0 / 0 |
| total (1,200 trials) | 86 / 10 | 1 / 10 | 0 / 10 |

The 26 failing versions of the seven trials the anchors reading does not
admit (the six above at twelve requests and the one at eight) all have a
witness under the persistent reading (`node residues.mjs`,
`results/residues.json`).

Classes over the six carry runs at twelve requests, as trials showing the
class (the earliest failure is L-001 in 226 of the 281 failing trials): L-001 234, L-002 48,
L-003 4, L-005 3, L-004 0 (it needs two adjacent spans of one value, which the
generator rarely builds; the regression shows it), and 2 trials unexplained:
under the directed search each of their failing versions had a single
admitted view, explained as L-001; the full search admits 162 and 15 views
for them, and the nearest differs from the display by a bold the L-001 rule
does not account for. Of 995 L-001 failure
records, 453 concern a side to which the key's expand type extends the mark
and 542 a side to which it does not. The 63 local-meaning failures were all
on insertions, out of 5,874 insert requests; none of 2,802 mark, 162 unmark
and 1,507 delete requests failed.

Every class has a minimal regression with a control in
`experiments/loro-oracle/regressions.mjs`, with the expected view, the
admitted views and the verdict derived by hand in the comment above it; 54 of
54 hold (`node run.mjs --mode regressions`).

## Plain text (L1)

**Gap rule.** No failure in the 800 plain trials under the gap rule, four
replicas and partial delivery included.

**One-sided rule refuted.** From three replicas (ids `peer:counter`):

```
r1 insert 0 "q"          q 1:0
r2 insert 0 "n"          n 2:0
deliver 2->3, 1->3       r3 shows q n (concurrent head inserts by peer)
r2 insert 1 "i"          i 2:1, recorded (n, none)
r3 insert 2 "u"          u 3:0, recorded (n, none)
r2 insert 0 "f"          f 2:2, recorded (none, n)
sync                     every replica shows q f n i u
```

Loro records for f the origin none and the right origin n, and Fugue makes f a
left child of n: f lands immediately before n, after q, which r2 never saw.
Under the one-sided rule q, n and f are head inserts shown q f n, so they were
applied n, f, q, and i and u are children of n shown i u, so u was applied
before i. Causally q precedes u and i precedes f: q < u < i < f < q, a cycle.
The two-sided and gap rules fold the order n, q, u, i, f to the view. The
control records f between n and i instead and passes under every rule. The
Yjs one-sided refutation (Y-000) has witnesses under every rule on Loro, which
shows i u w l where Yjs shows i w l u: Loro makes the two inserts into empty
displays left children of the tombstone q.

**Two-sided rule refuted.** From `r1 insert 0 "r"`, sync; then r1 inserts m at
0 (recorded none, r) while r2 deletes r and inserts c into its empty display
(recorded none, none). Loro shows m c: c's internal right origin is the
tombstone r (`crdt_rope.rs` 110-148), so m and c are both left children of r,
ordered by peer. The two-sided rule puts c, which has no visible right
neighbour, at the head in every order: admitted { c m }. The control, in which
r2 does not delete r, records c before r and passes. The Yjs two-sided
refutation (the Y-000 companion) gives the same view on Loro, p t d j, with the
same verdicts.

So for lists the answer is the same as for Yjs: the strong list specification
and nothing finer, with the difference that Loro's head insertions attach to
their right origin.

## Styles (L2)

### L-001 boundary inheritance under concurrency

A character inserted concurrently with a mark, just outside the mark's
identity interval, shows the mark's value, or does not, according to peer
ids. Minimal case (Y-004 re-expressed):

```
r1 insert 0 "a"; sync
r1 mark [0,1) bold       ||   r2 insert 0 "h"
sync                     both show h* a*     admitted (carry) { h a* }
```

With `link` (expand none) the same schedule shows h~ a~. Swapping the roles
(r2 marks, r1 inserts h at 1) shows a* h* and a~ h~; the controls (h on the
other side) show a* h and a~ h. The Y-001 insert variant is the same class at
an unmark's end: from "et" bold, r1 inserts d after t (bold by expand) while r2
unbolds e..t; both show e t d, plain, where carry admits only e t d*.

Mechanism. A mark is two ops, `StyleStart` and `StyleEnd`, and both are
inserted into the Fugue tracker as list elements (`diff_calc.rs` 1315-1398),
integrated by the same code as text (`crdt_rope.rs` 63-250). An anchor and a
concurrent insertion with the same neighbours are siblings, ordered by
ascending peer (lines 187 and 217). Whether the character lies between the
anchors is therefore decided by which replica has the lower peer id, not by
the expand type, which `find_best_insert_pos` consults only for local
insertions (`richtext_state.rs` 1833-1990).

Which reading admits it:

- **carry** refutes every L-001 case. On a side the expand type extends to
  (bold at an end, sup at a start, hl at either), this is an artefact of carry:
  the inherit and expand readings admit those cases.
- **inherit** and **expand** still refute the cases on a side the expand type
  does not extend to (545 of the 1,002 records), and each has residues of its
  own, so both readings are refuted as specifications of Loro. Under inherit,
  an insertion takes styles from a concurrent neighbour its issuer never saw
  (from "r", r1 deletes r and inserts s; r2 marks r hl and inserts b before
  it, b hl; Loro shows s b=, inherit gives s the hl of b). Under expand, two
  replicas that each mark their own concurrent head insert (q hl, s sup) close
  a cycle: hl, which extends both ways, must precede s's insert, and sup, which
  extends before, must precede q's, while each mark follows its own insert.
  Loro shows q= s^.
- **anchors** admits every L-001 case except one shape, crossed boundaries,
  6 of 1,200 trials:

  ```
  r1 insert 0 "e"; r2, r3 open the document
  r1 mark [0,1) sup; r1 insert 1 "u"    ||    r3 mark [0,1) bold; r3 insert 0 "y"
  sync                                  all show y^ e*^ u*
  ```

  Each mark reaches an insertion the other replica issued after its own
  concurrent mark. With marks acting once, on the characters present when
  they are applied, sup must follow y's insert, which follows bold, and bold
  must follow u's insert, which follows sup: a cycle. Loro's anchors persist,
  and a later concurrent insertion is ordered against them by peer.
- **persistent** admits every version checked: all eight-request runs, and the
  26 crossed-boundary versions above.

So L2 holds in the persistent reading and in no reading in which the expand
configuration constrains concurrent boundary insertions. In Loro, a mark is a
range between two list elements; the expand type decides only on which side
of an anchor the issuing replica places its own text. A concurrent insertion
at a boundary takes the style or not by peer order, on either side and for
every expand type: link (expand none) reaches a concurrent insertion at
either end, and bold (expand after) reaches one at its start. Measured
against Loro's own description of expand ("None: when inserting new text
before or after this style, the new text should **not** inherit this
style", `richtext.rs` 167), the cases on a side the expand type does not extend
to are defects; the others are not.

### Yjs classes on Loro

| Yjs class | Schedule on Loro | Loro | Verdict |
| --- | --- | --- | --- |
| Y-001 overlapping bold and unbold | from a b* c, bold [0,2) and unbold [1,3) | a* b c | admitted: concurrent marks of a key resolve by the greatest (Lamport, peer) (`richtext.rs` 120-126), one of the two orders |
| Y-001 insert variant | from e* t*, insert d after t and unbold e..t | e t d | L-001 (unmark end), admitted under expand, anchors and persistent |
| Y-002 nested bolds | from a u, bold [0,2) and bold [0,1) | a* u* | admitted |
| Y-002 insert and format | from q, bold q and insert z at 0, bold z | z* q* | admitted |
| Y-003 delete beside a bold insert | from w v b*, delete b and insert z after it | w v z* | admitted: a delete removes no anchor |
| Y-004 boundary spread | as above | h* a* | L-001 |
| Y-005 overlapping bolds | from a b c, bold [0,2) and bold [1,3) | a* b* c* | admitted |
| Y-007 delete-set causal gap, both shapes | an unbold sent before its predecessors; an insert sent before the unbold it follows | pending, a / a* b* | admitted: every change waits for its dependencies |
| opened-document family | every styled run with opened replicas | no determinism failure | absent |

The classes that vanish do so because no Loro operation depends on another
operation's anchors: a mark is a range op whose value competes by Lamport
order, a delete never touches an anchor, every change carries its
dependencies, there is no clean-up pass, and an imported snapshot rebuilds the
same state on the same code path.

## Local meaning (L2a)

All four classes are about where a local insertion lands among the
zero-width anchors at its position. `find_best_insert_pos`
(`richtext_state.rs` 1833-1990) scans the anchors forward and stops at the
first one an insertion must stay before (the start of an unmark, or an
anchor whose style prefers insertions before it,
`insert_stays_before_anchor`, lines 1416-1419, and `prefer_insert_before`,
`richtext.rs` 252-263), then scans back over anchors of link-like styles. An
unmark is stored with the reversed expand type (`richtext.rs` 218-224: both
becomes none, none becomes both). The rule sees anchors; the display does
not.

| Id | Minimal trace (one replica unless stated) | Display before | Expected | Loro |
| --- | --- | --- | --- | --- |
| L-002 style from no displayed neighbour | (a) insert "ab", mark hl [0,2), unmark hl [0,2), insert X at 0 | a b | X a b | X= a b |
| | (b) insert "abc", mark hl [1,2), delete [1,2), insert X at 1 | a c | a X c | a X= c |
| L-003 expand ignored toward a neighbour | insert "abc", mark link [0,3), unmark link [1,2), insert X at 1 | a~ b c~ | a~ X b c~ | a~ X~ b c~ |
| L-004 adjacent spans of one value | insert "ab", mark link [0,1), mark link [1,2), insert X at 1 | a~ b~ | a~ X~ b~ | a~ X b~ |
| L-005 expand of a key overridden (two replicas) | from y, r1 marks bold and r2 marks sup concurrently; r2's mark reaches r1; r1 inserts X at 0 | y*^ | X^ y*^ | X y*^ |

L-002 (a): the insertion passes the hl opening anchor (hl expands before, so
an insertion may follow it) and stops before the unmark's opening anchor,
inside hl and outside the unmark. (b): the opening and closing anchors of hl
stay adjacent after their only character is deleted, and an insertion stops
before the closing one (hl expands after), inside an empty span. Controls:
bold in (a) and link in (b) give the expected view. L-003: an insertion
always stops before the start of an unmark (rule 1 of
`find_best_insert_pos`), so it stays inside the enclosing link although link
expands nowhere; with bold, which expands after, the expected view and Loro's
agree. L-004: the insertion passes the first span's closing anchor and stops
before the second's opening one, outside both; with one span it is inside.
The display, from `toDelta`, shows one link in both cases, so the meaning of
the request is not a function of what the replica displays. L-005: the two
opening anchors are concurrent siblings ordered by peer, bold's first, and the
scan stops before it (bold does not expand before), so X also misses sup;
with the peers swapped X takes sup as expected.

L-002 is the commonest local failure (48 of the 54 trials with one). Peritext asks what an insertion inside a span whose text has been
deleted should get; Loro's answer depends on the anchors left behind, not on
anything displayed.

## Limits

The search is finite: twelve requests over two to four replicas (sixteen and
twenty in the long plain runs), witness search on at most twelve edits per
version (ten for the anchors runs, eight for the persistent runs and their
companions, since the relational readings multiply states), single lowercase
letters, the four style keys above with value true, and few unmarks (162 in
the twelve-request styled runs, since an unmark is generated only where the
key is present). The persistent reading is checked at eight requests and on
the versions the anchors reading rejects, not at twelve requests. The
`both` rule is tested with visible right neighbours only. The classifier
(`ra-pbt/instances/loro/classify.js`) explains a boundary difference using
some full order of characters consistent with the display, and is a
heuristic; every class it names has a hand-derived regression, and in the
carry, anchors and persistent runs it left no failure unexplained. Only
`LoroText` was exercised: lists, maps, trees, the undo manager, `applyDelta`,
detached editing and shallow snapshots are outside the search, as is a
style configuration that differs between replicas. Everything is measured on
1.17.1 under Node v26.3.1.

## Upstream

L-001 was added on 2026-10-29 as a comment on loro-dev/loro#1009, which
reported the expand-after start case in June 2026, with the peer-id
dependence and the mechanism; L-002 to L-005 were reported as
loro-dev/loro#1240. `experiments/loro-oracle/repro/` holds one plain-Loro
script per shape.

## Reproduce

```sh
cd ra-pbt/instances/loro && npm install --ignore-scripts && node verify-sources.js
cd ../../../experiments/loro-oracle
node spec-tests.mjs                         # 17 specification blocks
node run.mjs --mode regressions             # 54 regressions with controls
node --max-old-space-size=8192 campaign.mjs --trials 200   # every run; results/campaign/, results/campaign.json
node residues.mjs                           # anchors-reading failures under the persistent reading
node run.mjs --mode search --seed 41 --trials 2000 --rule left --steps 20 --bound 14 --replicas 3 --output results/left-search-41.json
node run.mjs --mode search --seed 31 --trials 200 --styles --opened false --attrs carry --output /tmp/s.json
node run.mjs --mode replay --input results/campaign/styles-created-31.json
```

`run.mjs --mode search` takes `--rule gap|left|both` and `--attrs
carry|inherit|expand|anchors|persistent`. The campaign takes about forty
minutes with the full witness search and peaks near six gigabytes.
