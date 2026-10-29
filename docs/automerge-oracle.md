# Automerge text with marks: RA-linearizability against Peritext's semantics

## Claim and falsifiers

Claim. Automerge text with marks (`@automerge/automerge` 3.5.0, whose marks
implement Peritext, Litt, Kleppmann et al. 2022) is RA-linearizable with
respect to a sequential specification of the same shape as the one under
which Yjs failed: a list of characters with identities obeying the strong
list specification (Attiya et al. PODC 2016), deletion by identity and
idempotent, and marks that differ from the Yjs specification only in the
semantics Peritext documents: a mark range is anchored to character
identities, its expand policy (`before`, `after`, `both`, `none`) fixes on
which side of a neighbouring character each anchor sits, and among marks of
one name covering a character the last one applied wins (Peritext's rule
that the greatest operation id wins, read sequentially).

Falsifiers.

1. A version whose displayed view no linear extension of the causal order
   of its integrated changes folds to (`raLinearizability`).
2. Two replicas holding the same changes, with nothing queued, that display
   different text or marks (`convergence`).
3. A local edit whose effect on the issuer's own view differs from the
   index-level edit under the expand policy (`localMeaning`).

Also checked: a replica that opened a saved document and one that applied
the changes give the same result for the same request (`determinism`), and
after full synchronisation no character is lost and nothing is queued
(`conservation`).

## Reality oracle

`@automerge/automerge` 3.5.0 from npm, git commit
`4d2a8f6bfecfb7f1e4fca126e6d2122ac526f903` as reported by
`Automerge.releaseInfo()`, pinned by version, lockfile integrity string,
commit and SHA-256 of the executed JavaScript and WebAssembly files
(`ra-pbt/instances/automerge/sources.json`, checked by `verify-sources.js`
before and after every run). Mechanisms below cite the Rust source at that
commit.

## Specification

`ra-pbt/instances/automerge/spec.js` imports no Automerge code. A state is a
list of elements with identities and a set of applied marks.

- **List.** An element is inserted anywhere strictly after its recorded
  origin and strictly before its recorded right origin: the strong list
  specification, deleted characters kept as anchors. Deletion is by
  identity and idempotent.
- **Marks, anchor semantics (the claim).** A mark carries a start and an end
  anchor, each the start or end of the text or a side (`before`, `after`) of
  a character. The expand policy fixes the anchors from the request: an
  expanding start anchors after the character before the range (or at the
  start of the text), a non-expanding start before the first character, and
  symmetrically for the end. A character is covered when it stands between
  the anchors in the current list, so characters inserted later into an
  anchored gap are covered or not according to the side, never according to
  timing. An expanding end at the end of the text anchors at the end of the
  text; Peritext attaches end anchors to a following character and does not
  define this case, and the one A-001 trace that depends on it is marked in
  the class table.
- **Marks, marker semantics (the alternative).** A mark inserts a begin and
  an end boundary into the list under the same placement rule as characters;
  a character is covered when it stands between its mark's boundaries.
- **Resolution.** Among covering marks of one name the greatest identity
  wins (Peritext's rule: counter, then actor); a null value is an unmark. A
  mark issued by a replica has an identity above every mark it has seen, so
  sequentially the latest mark wins on its range.
- **Policies.** bold expands after, italic expands before, link does not
  expand. Bold and italic are set or cleared; links take a fresh value per
  request. `both` is not generated (see limits).
- **Local meaning.** `localEdit` applies the request to the displayed view:
  an inserted character takes, per name, the left neighbour's value
  (`after`), the right neighbour's (`before`), or the value both share
  (`none`), then the attributes passed with the insert; a format request sets
  exactly its visible range.

Identities are Automerge operation ids `counter@actor`, the same strings
`Automerge.getCursor` returns. The adapter reconstructs the element list of
the text object from the decoded changes a document holds (insert operations
form a tree by their `elemId` reference, siblings in descending id order,
deletions mark characters) and checks the reconstruction against
`getCursor` and `spans` on every view it builds; no run raised a
disagreement. An insert's origin is its recorded `elemId`, its right origin
the element that followed the reference just before the operation (a local
insert is placed immediately after its reference). Under the anchor
semantics, which has no boundary elements, a boundary neighbour is replaced
by the nearest character beyond it, which only widens the gap. A record is a
change from `getLastLocalChange`; delivery is `applyChanges`, which queues a
change whose dependencies are missing; a record is integrated when
`getChangeByHash` finds it, and a replica holds pending state when
`getMissingDeps` is nonempty. Opened replicas `load` a saved document;
created replicas apply the shared genesis change.

The witness search explores every placement the gap rule admits, deleted
characters and boundaries included, and compares views without identities.
An earlier version of the search was directed by the target's element
layout and re-checked each failure with a search directed by the visible
characters only; both directions prune by identity order while the
comparison ignores identities, which with repeated characters can reject a
view that has a witness. The campaign below was rerun with the full search
on 2026-10-29; `confirmWitness` (`confirm-witness.js`) remains as a budgeted
full search that distinguishes exhaustion from rejection.

## Results

Twenty searches of 200 trials, twelve requests each over two or three
replicas, the witness search on every version (no version exceeded the
bound of twelve edits), `experiments/automerge-oracle/results/campaign/`.
"Confirmed" counts failing trials with at least one failure that is not a
view artefact of the index-level expectation (a class below). "Truncated"
counts versions whose search reached the cap of one million explored states
and were neither passed nor failed; they are not among the versions
checked.

| Run | Semantics | Edits | Deliveries | Sends (queued) | Opens | Versions checked | Truncated | Failing trials | Confirmed | RA-lin (trials) | Local meaning (trials) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| plain-31 | anchor | 1,974 | 1,302 | 0 | 0 | 3,245 | 31 | 0 | 0 | 0 | 0 |
| plain-32 | anchor | 1,945 | 1,271 | 0 | 0 | 3,190 | 26 | 0 | 0 | 0 | 0 |
| plain-31 | marker | 1,974 | 1,302 | 0 | 0 | 3,245 | 31 | 0 | 0 | 0 | 0 |
| plain-32 | marker | 1,945 | 1,271 | 0 | 0 | 3,190 | 26 | 0 | 0 | 0 | 0 |
| partial-plain-31 | anchor | 1,821 | 876 | 579 (227) | 0 | 3,246 | 30 | 0 | 0 | 0 | 0 |
| partial-plain-32 | anchor | 1,802 | 816 | 598 (246) | 0 | 3,201 | 15 | 0 | 0 | 0 | 0 |
| partial-plain-31 | marker | 1,821 | 876 | 579 (227) | 0 | 3,246 | 30 | 0 | 0 | 0 | 0 |
| partial-plain-32 | marker | 1,802 | 816 | 598 (246) | 0 | 3,201 | 15 | 0 | 0 | 0 | 0 |
| marks-31 | anchor | 1,898 | 1,378 | 0 | 0 | 3,276 | 0 | 150 | 150 | 150 | 3 |
| marks-32 | anchor | 1,905 | 1,311 | 0 | 0 | 3,210 | 6 | 142 | 142 | 142 | 6 |
| marks-31 | marker | 1,898 | 1,378 | 0 | 0 | 2,837 | 439 | 3 | 3 | 0 | 3 |
| marks-32 | marker | 1,905 | 1,311 | 0 | 0 | 2,775 | 441 | 6 | 4 | 0 | 6 |
| marks-opened-31 | anchor | 1,633 | 1,413 | 0 | 230 | 3,276 | 0 | 108 | 108 | 104 | 4 |
| marks-opened-32 | anchor | 1,600 | 1,386 | 0 | 230 | 3,216 | 0 | 112 | 112 | 110 | 4 |
| marks-opened-31 | marker | 1,633 | 1,413 | 0 | 230 | 3,194 | 82 | 4 | 4 | 0 | 4 |
| marks-opened-32 | marker | 1,600 | 1,386 | 0 | 230 | 3,145 | 71 | 4 | 4 | 0 | 4 |
| partial-marks-31 | anchor | 1,770 | 876 | 630 (237) | 0 | 3,276 | 0 | 166 | 166 | 166 | 1 |
| partial-marks-32 | anchor | 1,749 | 816 | 651 (266) | 0 | 3,216 | 0 | 153 | 153 | 153 | 1 |
| partial-marks-31 | marker | 1,770 | 876 | 630 (237) | 0 | 2,920 | 356 | 1 | 1 | 0 | 1 |
| partial-marks-32 | marker | 1,749 | 816 | 651 (266) | 0 | 2,901 | 315 | 1 | 1 | 0 | 1 |

Convergence, determinism (opened against created replicas, 230 opens per
opened run and a fork pair before every edit) and conservation failed
nowhere, and no execution anomaly was recorded. Plain text passed every
check under both semantics, with and without partial delivery. Formatting
exactness held: no format request disagreed with the index-level edit
(2,191 in the anchor runs, the same requests in the marker runs).

**The claim is refuted.** Under the anchor semantics, 831 of 1,200 trials
with marks fail; 794 of them first fail in class A-001. **Under the marker
semantics no judged version lacked a witness** in the 2,000 trials of every
mix; 1,806 versions of the marks mixes were left unjudged at the state cap
(below). What remains under it are local-meaning failures in 17 trials
(A-002 10, A-001 6, both 1) and two view artefacts.

Trials per class over the anchor runs (a trial counts once per class it
shows; onset in brackets): A-001 807 (794), A-003 34 (26), A-002 11 (7),
A-001+A-003 11, A-001+A-002 1, A-002+A-003 1, view artefact 2 (1), other 26
(3). The 102 records of class "other", in 26 trials, fail under both
searches; what the mechanisms do not explain is the reference view. The
classifier takes as reference the admitted view with the same characters
nearest to Automerge's, and the full enumeration admits more views than the
directed one did (for trial 5 of marks-32, 180 and 6,924 views at the two
failing steps against one each), so a nearer view with a difference none of
the three mechanisms accounts for can displace the one that was explained.
Under the directed enumeration all 26 were classed A-001, and 23 of them
still show A-001 in another record.

**Rerun under the full search.** The campaign was first run with the
directed search and rerun on 2026-10-29 with the full search under the
state cap. Thirty-four anchor trials that had failed only by rejections of
the directed search now pass: thirty-three had been classed layout artefact
alone, and one (marks-32, trial 117) also carried a record that the
visible-character direction had not linearised either. Re-running trials
12, 16 and 27 of marks-31 and trial 117 of marks-32 by hand gives the same
pair of verdicts, the directed search rejecting and the full search finding
a witness, with no version at the cap. In 117 further trials a layout
artefact record disappeared beside records of other classes. Every other
failing trial fails under both searches, and no trial that passed before
fails now. The versions the cap cut off number 1,914 of 64,920: 102 in the
plain runs, 6 in marks-32 under the anchor semantics, none in the other
anchor runs with marks, and 1,806 in the marker runs with marks (439, 441,
82, 71, 356 and 315), where boundaries are list elements and the placements
multiply. The confirmation search (`confirmWitness`) repeats the
end-to-end search under a budget of 200,000 specification applications; in
96 records (28, 19, 5, 24 and 20 in the anchor runs with marks) the budget
ran out and the record is counted undecided for the confirmation, though
the end-to-end check had rejected the version without reaching the cap.

## Classes

Every class has a hand-derived regression with its control in
`experiments/automerge-oracle/regressions.mjs`, run under both semantics.
Expected outcomes are hand-derived. Notation: `x*` bold, `x/`
italic, `x~` linked; ids `counter@actor`; `<B`, `B>` begin and end
boundaries, `+` a set expand flag.

| Id | Minimal trace | Observed | Anchor admits | Marker admits | Status |
|---|---|---|---|---|---|
| A-001 | from `ax`, r1 deletes `x` and bolds `a`; concurrently r2 inserts `h` at 0 | `h* a*` | `h a*` | `h a*`, `h* a*` | defect against the documented semantics; control without the delete: `h a*` |
| A-001 | from `ab`, r2 inserts `z` at 0; r1 links `ab`; concurrently r2 inserts `x` after `b` | `z a~ b~ x~` | `z a~ b~ x` | four views incl. it | as above; control without `z`: `a~ b~ x` |
| A-001 | r1 inserts `t`; concurrently r2 inserts `f` bold at 0; sync | `f* t` | `t f*`, `f* t*` | also `f* t`, `t* f*` | same mechanism; the anchor verdict rests on the end-of-text choice noted in the specification |
| A-002 | one replica: `q` bold, link `q`, delete `q`, insert `i` | `i*` | `i*` | `i*` | local-meaning defect; control without the link: `i` |
| A-003 | one replica: `a`, italic `a`, delete `a`, insert `u` at 0 | `u` | `u/` | `u` | specification artefact of the anchor reading |

**A-001, boundary placed by operation order.** `TransactionInner::mark`
(`rust/automerge/src/transaction/inner.rs`, 801 to 872) writes a mark as two
insert operations, `MarkBegin(expand.before())` at the start index and
`MarkEnd(expand.after())` at the end index, list elements like characters.
Remote integration (`op_set2/change/batch.rs`, `Untangler`) places an
insert after its reference among siblings by operation id, and the expand
flags play no part in it: they are consulted only when a replica chooses
where its own insert goes (`op_set2/op_set.rs`, `scan_for_sticky_marks`,
494 to 544; `op_set2/op_set/insert.rs`, `identify_valid_insertion_spot`).
So a character inserted concurrently into the gap at a mark boundary lands
inside or outside the mark according to which operation has the larger
counter. The first trace is the clean form: the non-expanding start of a
bold covers `h`, typed before `a` by another user, exactly when the bold's
operation has the larger counter, and the control without the delete shows
`h` plain. Peritext's rule for a boundary is that an inserted character
inherits the formatting of the character before it, and its anchors are
positions in the document, so the rule does not depend on who inserted or
when. The second trace is the same mechanism at a non-expanding end: a link
grows over concurrent text. The third trace, an after-expanding bold at the
end of the text, shows the same ordering by counter, but Peritext attaches
an end anchor to a following character and does not say what an expanding
end means where there is none; the anchor semantics here treats it as the
end of the text, a choice the essay does not make, so that trace's verdict
under the anchor reading rests on this specification and the first two do
not. The
same reordering of two boundaries of different marks in one gap is invisible
until a later local insert lands between them, where it shows as a local
meaning failure (the 6 marker-run trials) or, under the anchor semantics, as
a version with no witness.

**A-002, shared insertion point.** A local insert lands after the last
sticky boundary between its displayed neighbours: a begin that expands
before or an end that does not expand after (`insert.rs` line 82,
`op_set.rs` 494 to 544). One point serves every mark name, so a sticky
boundary of one name carries the new character across a non-sticky boundary
of another. After deleting a bold, linked character, the link's
non-expanding end sits beyond the tombstone and drags the next insert into
the bold span: typing into an empty document produces bold text, which it
does not without the link. The anchor semantics admits the result (the
character is inside the bold's anchors once it stands after the tombstone),
so this is a local-meaning failure only; the per-name point gives the
index-level answer in every A-002 record.

**A-003, emptied mark (specification artefact).** When every character of a
mark is deleted, the scan drops a begin and end pair it finds with nothing
visible between them ("can't insert between mark start/end pair",
`op_set.rs` 520) and the insert lands outside the pair. The anchors of the
emptied mark still enclose that position, so the anchor reading covers the
new character. The index-level edit agrees with Automerge, and Peritext too
chooses where an insert goes among tombstones from the anchor points
attached to them rather than leaving it at the reference. The candidate "a mark covers whatever lies between its anchors" is
refuted for emptied marks; it is recorded, not repaired, since the marker
semantics already describes what Automerge does.

**Artefacts.** A *layout artefact* was a version the layout-directed search
rejected and the visible-character search linearised; the class cannot
arise under the full search. A *view artefact* is a local-meaning record in which a link
covers the insertion point but loses to a later link on both displayed
neighbours (`iz` linked, `i` relinked, insert between them): the index-level
expectation cannot see that coverage, and the anchor reading agrees with
Automerge.

## Relation to the Yjs classes

The Yjs classes re-expressed as Automerge schedules, each with its
predicted verdict; all hold as predicted.

| Yjs class | Automerge schedule | Predicted | Observed |
|---|---|---|---|
| Y-001 marker ownership | from `a b* c`, bold [0,2) concurrent with unbold [1,3) | pass | `a* b c`, admitted under both |
| Y-002 opener judged redundant | from `q`, bold `q` concurrent with bold `z` at 0 | pass | `z* q*` |
| Y-003 delete removes neighbour formatting | from `w v b*`, delete `b` concurrent with bold `z` after it | pass | `w v z*` |
| Y-004 boundary spread | from `a`, bold `a` concurrent with plain `h` at 0 | pass when `h` has the larger counter, A-001 otherwise | `h a*`; with a raised counter `h* a*` |
| Y-005 overlapping same attribute | from `abc`, bold [0,2) concurrent with bold [1,3) | pass | `a* b* c*` |
| Y-007 delete sets bypass buffering | unbold sent ahead of the insert it depends on | pass (queued) | `a*`, change queued |
| opened document | opened replica deletes and inserts | pass | agrees with a created replica |

Automerge marks belong to characters' identities and are resolved by id, so
none of the Yjs marker-maintenance classes occur, and causal buffering is
complete because a change is one unit with explicit dependencies. Y-004
survives in a different form: Automerge orders a boundary against a
concurrent insert by counter, where Yjs ordered its marker by client.

## Limits

The search is finite: twelve requests over two or three replicas, single
lowercase letters, three mark names with fixed policies. `both` is not
generated, because the index-level edit cannot decide its outcome when the
two neighbours show different values; the policy is covered only by the source reading (remote integration
does not read the expand flags). Block markers, `updateSpans`, `updateText`, cursors as edit
positions, the sync protocol and `merge` of diverged forks beyond what
`deliver` exercises are outside it. The element reconstruction relies on
the RGA ordering it is checked against; the check covers every displayed
character and attribute, not the relative order of invisible elements, which
is why every failure is re-checked without the layout. Results concern the
pinned release only.

## Upstream

A-001 was reported on 2026-10-29 as automerge/automerge#1649 with the two
interior shapes and the question whether expand is meant to govern
concurrent inserts; A-002 as automerge/automerge#1650.

## Reproduce

`experiments/automerge-oracle/repro/` holds one plain-Automerge script per
defect shape with its control (`npm install --ignore-scripts && node
run-all.mjs`); the harness runs are:

```sh
(cd ra-pbt/instances/automerge && npm install --ignore-scripts)
node ra-pbt/instances/automerge/verify-sources.js
cd experiments/automerge-oracle
node spec-tests.mjs
node run.mjs --mode regressions
node --max-old-space-size=8192 campaign.mjs --trials 200 --seeds 31,32
node run.mjs --mode search --seed 31 --trials 200 --format --opened false --semantics anchor --output results/search-31.json
node ../../ra-pbt/instances/automerge/classify.js results/search-31.json results/search-31-classified.json anchor
```
