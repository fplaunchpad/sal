# Automerge text with marks: causal-history conformance and anchor semantics

Review update (2026-10-29): the packaged visual specification now searches
all admitted placements. The original target-ID pruning could reject an
observation that ignores IDs when characters repeat. Campaign JSON below
is preserved historical evidence; negative campaign verdicts require a
corrected rerun. The named short reproductions and their controls were
checked separately. See [the search review](notion-production-text-review.md).

## Claim and falsifiers

Candidate claim, tested rather than proved. Automerge text with marks
(`@automerge/automerge` 3.5.0, whose marks
implement Peritext, Litt, Kleppmann et al. 2022) admits causal-history
witnesses under a sequential specification of the same shape as the one under
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

Here `raLinearizability` is the legacy name of a causal-history check, not a
general paper-RA checker. It preserves all causal dependencies among the
integrated records, adds no concurrent implementation `rc` edges, and now
reports `paperRaVerdict: 'not-checked'`. Its order can be incomparable with
the paper's `lo_E`; either paper-RA conclusion needs a separate order and
interface correspondence argument. The counts below retain their historical
check names. Bound/partial-record skips and missing-dependency gaps limit
coverage; dropped-dependency slices are not causally closed paper versions.

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

The original campaign first searched the full target layout, then tried
visible-character-directed confirmation. Both forms could constrain hidden
identities more than the visual query permits. The current specification
uses full observation-preserving search instead. Its confirmation helper
budgets `applyAll` and reports `undecided` on exhaustion. Historical
"confirmed" and layout-artefact counts below are the old classification,
not freshly validated negative verdicts. The hand-derived minimal examples
have independent controls.

## Results

Twenty searches of 200 trials, twelve requests each over two or three
replicas, the witness search on every version (no version exceeded the
bound of twelve edits), `experiments/automerge-oracle/results/campaign/`.
"Confirmed" counts failing trials with at least one causal-history or local-meaning failure that is not an
artefact of the layout-directed search or of the index-level expectation
(classes below).

| Run | Semantics | Edits | Deliveries | Sends (queued) | Opens | Versions checked | Failing trials | Confirmed | Causal-history (trials) | Local meaning (trials) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| plain-31 | anchor | 1,974 | 1,302 | 0 | 0 | 3,276 | 0 | 0 | 0 | 0 |
| plain-32 | anchor | 1,945 | 1,271 | 0 | 0 | 3,216 | 0 | 0 | 0 | 0 |
| plain-31 | marker | 1,974 | 1,302 | 0 | 0 | 3,276 | 0 | 0 | 0 | 0 |
| plain-32 | marker | 1,945 | 1,271 | 0 | 0 | 3,216 | 0 | 0 | 0 | 0 |
| partial-plain-31 | anchor | 1,821 | 876 | 579 (227) | 0 | 3,276 | 0 | 0 | 0 | 0 |
| partial-plain-32 | anchor | 1,802 | 816 | 598 (246) | 0 | 3,216 | 0 | 0 | 0 | 0 |
| partial-plain-31 | marker | 1,821 | 876 | 579 (227) | 0 | 3,276 | 0 | 0 | 0 | 0 |
| partial-plain-32 | marker | 1,802 | 816 | 598 (246) | 0 | 3,216 | 0 | 0 | 0 | 0 |
| marks-31 | anchor | 1,898 | 1,378 | 0 | 0 | 3,276 | 164 | 150 | 164 | 3 |
| marks-32 | anchor | 1,905 | 1,311 | 0 | 0 | 3,216 | 149 | 143 | 149 | 6 |
| marks-31 | marker | 1,898 | 1,378 | 0 | 0 | 3,276 | 3 | 3 | 0 | 3 |
| marks-32 | marker | 1,905 | 1,311 | 0 | 0 | 3,216 | 6 | 4 | 0 | 6 |
| marks-opened-31 | anchor | 1,633 | 1,413 | 0 | 230 | 3,276 | 111 | 108 | 107 | 4 |
| marks-opened-32 | anchor | 1,600 | 1,386 | 0 | 230 | 3,216 | 112 | 112 | 110 | 4 |
| marks-opened-31 | marker | 1,633 | 1,413 | 0 | 230 | 3,276 | 4 | 4 | 0 | 4 |
| marks-opened-32 | marker | 1,600 | 1,386 | 0 | 230 | 3,216 | 4 | 4 | 0 | 4 |
| partial-marks-31 | anchor | 1,770 | 876 | 630 (237) | 0 | 3,276 | 171 | 166 | 171 | 1 |
| partial-marks-32 | anchor | 1,749 | 816 | 651 (266) | 0 | 3,216 | 158 | 153 | 158 | 1 |
| partial-marks-31 | marker | 1,770 | 876 | 630 (237) | 0 | 3,276 | 1 | 1 | 0 | 1 |
| partial-marks-32 | marker | 1,749 | 816 | 651 (266) | 0 | 3,216 | 1 | 1 | 0 | 1 |

Convergence, determinism (opened against created replicas, 230 opens per
opened run and a fork pair before every edit) and conservation failed
nowhere, and no execution anomaly was recorded. Plain text passed every
check under both semantics, with and without partial delivery. Formatting
exactness held: no format request disagreed with the index-level edit
(2,191 in the anchor runs, the same requests in the marker runs).

**The candidate anchor specification has counterexamples.** Under the
anchor semantics, 832 of 1,200 trials
with marks fail (layout artefacts excluded); 761 of them first fail in class
A-001. **No checked version lacked a marker-specification witness** in
2,000 bounded trials. This does not prove RA-linearizability. What remains
under it are local-meaning failures in 17 trials (A-002 10, A-001 6, both 1) and
two view artefacts.

These 832 failing anchor trials are not 832 library defects: they include
the emptied-mark specification artefact A-003 and cases depending on the
custom expanding end-of-text sentinel. The two non-expanding-boundary
reproductions support the A-001 finding without that sentinel choice.

Trials per class over the anchor runs (a trial counts once per class it
shows; onset in brackets): A-001 811 (761), A-003 34 (25), A-002 11 (7),
A-001+A-003 13, A-001+A-002 1, A-002+A-003 1, view artefact 2 (1), layout
artefact 160 (71). No failure was left unclassified.

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
| A-001, end-sentinel candidate | r1 inserts `t`; concurrently r2 inserts `f` bold at 0; sync | `f* t` | `t f*`, `f* t*` | also `f* t`, `t* f*` | refutes the chosen expanding end sentinel; not independent evidence of a Peritext defect |
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

**Artefacts.** A *layout artefact* is a version the layout-directed search
rejected and the visible-character search linearised (160 anchor trials, no
marker trial). A *view artefact* is a local-meaning record in which a link
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

Measurement provenance: the campaign tables are recorded output from source
baseline `14f073e`, not fresh campaigns on the integrated tree. Review
re-ran the pinned source check, 12 specification tests, 18 declared
regressions and all three plain-library reproductions successfully. In a
pure-specification sensitivity check, replacing only the expanding
end-of-text `null` anchor by `after(f)` admitted `f* t`; the sentinel trace
therefore cannot decide the semantics that Peritext leaves unspecified.

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
