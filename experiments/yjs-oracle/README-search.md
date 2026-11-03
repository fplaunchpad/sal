# Schedule search over Yjs Y.Text

Randomised, seeded schedules over two or three Yjs replicas, executed and
checked against the sequential specification of the Y.Text instance
(`ra-pbt/instances/yjs/spec.js`) with the ra-pbt witness search
(`ra-pbt/src/witness.js`). Nothing here is a proof: a passing search is evidence
over the schedules explored, and a failure is a concrete, replayable
counterexample to the property checked, under the specification as written.

## Commands

```
node run.mjs --mode regressions
node run.mjs --mode search --seed 1 --trials 20 --output results/search-seed1.json
node run.mjs --mode search --seed 2 --trials 20 --format --output results/search-seed2-format.json
node run.mjs --mode search --seed 3 --trials 20 --partial --output results/search-seed3-partial.json
node run.mjs --mode replay --input results/search-seed1.json
```

Search options: `--steps K` (edits plus transfers per trial, default 12),
`--format` (formatting edits and inserts with attributes), `--partial`
(individual ops sent in shuffled order, some held back until the final sync),
`--replicas R` (default: 2 or 3 chosen by the seed), `--bound B` (largest
number of integrated edits for which the witness search runs, default 12),
`--opened true|false` (some replicas join by opening a stored document;
default on with `--format`). Trial `t` of seed `S` uses generator seed
`(S * 1000003 + t) mod 2^32`, recorded in the output.

`verifySources()` runs before and after every mode.

## Files

| File | Contents |
| --- | --- |
| `regressions.mjs` | hand-derived failing schedules with passing controls |
| `run.mjs` | the command-line driver |
| `campaign.mjs` | classifies a set of search outputs, shrinks one representative per class and run, writes `results/campaign.json` |
| `spec-tests.mjs` | hand-derived tests of the specification and the witness search |

The machinery is in `ra-pbt`: schedule execution and the trace
(`src/schedule.js`), the checks below (`src/checks.js`), seeded generation
(`src/generate.js`), greedy shrinking by step removal and request reduction
(`src/shrink.js`) and the search loop (`src/campaign.js`). The Y.Text
instance (`ra-pbt/instances/yjs/`) supplies the specification, the replica
adapter, the request generator and reducers (`len` and text shortening), and
the mechanism classifier of check failures and the conservation diagnosis
(`classify.js`).

Schedule steps: `edit` (insert, delete, format at an index valid for the
acting replica's current view), `deliver` (sync everything the sender has),
`send` (one op of the sender's op list, possibly out of causal order), `open`
(construct a replica by loading another's state before first touching the
text type). After the schedule, execution appends a final-sync round in which
every ordered pair of replicas delivers once.

Ops carry keys `r<replica>#<n>`. An op's `deps` are the ops integrated at its
issuing replica when it was issued. Yjs's follow-up formatting cleanup on a
receiving replica is recorded as an op of kind `cleanup` issued by the
receiver, with no specification operations.

## Checks

| Check | Meaning |
| --- | --- |
| `convergence` | two replicas with equal state vectors, equal integrated ops and nothing pending display the same text; after the final sync, all replicas do |
| `raLinearizability` | after every edit and delivery at replica R, R's displayed text is the specification's fold over some linear extension of the causal order on the ops R has integrated; skipped (and counted) above the bound or when an op is only partly integrated |
| `localMeaning` | after every edit at R, R's displayed text is `localEdit` of its text before the edit |
| `determinism` | before every edit, a fork created fresh and synced and a fork opened by loading R's state issue the same request with the same explicit attributes, and display the same text afterwards |
| `conservation` | after the final sync, the displayed characters (by id) are the inserted ones minus the deleted ones, every op is integrated everywhere, and nothing is pending |

## Output and exit status

The summary table reports trials, edits, deliveries, sends, opens, cleanup
events, versions checked by the witness search, witness skips, causal gaps
(deps of an integrated op that are not themselves integrated, which occur
only with `send`), and failures by check. The JSON output holds the summary,
every failing trial (schedule, op list, check details), and one shrunk
representative per distinct `(check, op kinds)` signature, with the
specification's admitted final views where the check is `raLinearizability`.

Exit status 1 means some check failed on some trial (search, replay) or some
regression did not hold; 0 means none did.

## Campaign

```
node run.mjs --mode search --format --opened false --seed 11 --trials 200 --output results/campaign/format-created-11.json
node run.mjs --mode search --format --opened false --seed 12 --trials 200 --output results/campaign/format-created-12.json
node run.mjs --mode search --format --opened false --seed 13 --trials 200 --output results/campaign/format-created-13.json
node run.mjs --mode search --format --opened true  --seed 14 --trials 200 --output results/campaign/format-opened-14.json
node run.mjs --mode search --format --opened true  --seed 15 --trials 200 --output results/campaign/format-opened-15.json
node run.mjs --mode search --seed 16 --trials 200 --output results/campaign/plain-16.json
node run.mjs --mode search --partial --seed 17 --trials 200 --output results/campaign/partial-17.json
node run.mjs --mode search --partial --format --opened false --seed 18 --trials 200 --output results/campaign/partial-format-18.json
node run.mjs --mode search --partial --format --opened true  --seed 19 --trials 200 --output results/campaign/partial-format-19.json
node campaign.mjs format-created-11=results/campaign/format-created-11.json ... partial-17=results/campaign/partial-17.json
```

### Classes

`classify.js` re-executes a failing schedule, records for every edit the
governing marker (last live format item of each key to the left) of each
character it wrote at the issuing replica, and at a failing step compares
the replica's view with the nearest admitted view (same characters, fewest
attribute differences). Each differing (character, key) is explained from
the item walk, the op that created each marker and the ops whose updates
delete it.

| Id | Mechanism | Evidence required | Label |
| --- | --- | --- | --- |
| Y-001 | marker ownership | a marker that a character's value depends on (the opener its writer relied on, or a closer ending a span) was deleted by a format op unaware of the dependency (concurrent with the writer or with the character's insert); `formatText` deletes every live marker of its key in its range and, absorbing an equal opener, emits no closer | Peritext §2.3.2 reports the shape for the 2016 y-richtext; no public report on the current text type |
| Y-002 | opening marker judged redundant | the marker was deleted by a cleanup op (`cleanupYTextFormatting`), as overwritten by a later marker of the same key in its gap | no public report |
| Y-003 | delete removes neighbour formatting | the marker was deleted by a delete op (`cleanupFormattingGap` from `deleteText`) concurrent with the writer or the character's insert | not matched to a public report |
| Y-004 | boundary spread | a live opener or closer of a span sits on the far side of a concurrently inserted character the span's op never wrote, with no marker deleted | issue #385 family |
| Y-005 | overlapping same attribute | a live marker of the same key, created by an op concurrent with the writer that does not write the character, restores the value its creator saw inside the writer's span | issue #382 family |
| Y-006 | opened document | a determinism failure: a created fork and an opened fork of the same replica display different values after the same request; no concurrency involved | no public report |
| other | none of the above | the item walk is attached | |

Y-006 is assigned by the determinism check rather than by the item walk, and
one family is counted outside the classes: `final-sync` (conservation failures, and final convergence failures, in
which every op missing at a replica is a cleanup that replica never
received).

### Histogram

Trials per class: the class of the trial's earliest view failure (onset) /
trials showing the class in any failure record. Later failures at a replica
can inherit an earlier anomaly's state, so onset is the primary count. The
`Y-006` column counts trials with a determinism failure. Seven
runs of 200 trials, twelve steps each, witness bound 12; `results/campaign/`
holds the outputs and `results/campaign.json` the classification.

| Run | Failing trials | RA failures | Determinism | Y-001 | Y-002 | Y-003 | Y-004 | Y-005 | other | Y-006 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| plain-16 | 0 | 0 | 0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0 |
| partial-17 | 0 | 0 | 0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0 |
| format-created-11 | 41 | 112 | 12 | 6/6 | 0/0 | 7/7 | 13/13 | 4/5 | 0/0 | 12 |
| format-created-12 | 41 | 147 | 9 | 5/5 | 2/3 | 12/13 | 11/11 | 4/5 | 0/0 | 9 |
| format-created-13 | 49 | 163 | 8 | 4/4 | 1/1 | 10/10 | 12/14 | 15/16 | 0/1 | 8 |
| format-opened-14 | 58 | 264 | 2 | 4/6 | 1/2 | 16/17 | 23/26 | 12/13 | 0/2 | 2 |
| format-opened-15 | 52 | 191 | 9 | 10/10 | 2/2 | 15/15 | 11/13 | 8/9 | 0/0 | 9 |
| partial-format-18 | 37 | 109 | 10 | 4/4 | 0/0 | 7/7 | 14/14 | 3/4 | 1/1 | 10 |
| partial-format-19 | 51 | 190 | 3 | 5/6 | 3/3 | 14/16 | 16/18 | 7/8 | 4/5 | 3 |

Over the seven formatting runs the onset totals are Y-001 38, Y-002 9,
Y-003 81, Y-004 100, Y-005 53 and other 5, the five all in the
partial-delivery runs. Conservation and final
convergence failed in no run once the final sync repeats until no cleanup
update is emitted.

Formatting exactness (claim 4) is the `localMeaning` check on format
requests: 2,301 format requests across the seven formatting runs, 0 failures.
The one `localMeaning` failure in `partial-format-19` is on a delete at an
opened replica with no concurrent operation, Y-006:
`a p* m* o` with `m` deleted shows `a p* o*`.

The campaign outputs keep each run's summary, shrunk representatives and the
seeds of its failing trials; the full failing traces are regenerated by
rerunning the seed. `results/campaign.json` keeps item walks only for
unclassified records.

Plain-text and partial-delivery runs (three replicas) found no failure of any
check: with identities carried by the target view, the witness search under
the gap rule checked 3,600 and 3,592 versions respectively. Partial delivery
with formatting (`partial-format-18`, `partial-format-19`) shows the same
classes as complete delivery and nothing new.


| Run | Trials | Failing trials | RA failures | Y-001 | Y-002 | Y-003 | Y-004 | Y-005 | other | Y-006 | final-sync |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| format, created, seed 11 | 200 | 45 | 108 | 6 / 6 | 0 / 0 | 7 / 7 | 13 / 13 | 4 / 5 | 1 / 1 | 0 / 12 | 0 / 4 |
| format, created, seed 12 | 200 | 43 | 136 | 5 / 5 | 2 / 3 | 12 / 13 | 11 / 11 | 5 / 6 | 0 / 0 | 0 / 9 | 0 / 3 |
| format, created, seed 13 | 200 | 55 | 167 | 4 / 4 | 1 / 1 | 10 / 10 | 12 / 14 | 15 / 16 | 2 / 3 | 0 / 8 | 0 / 5 |
| format, opened, seed 14 | 200 | 64 | 266 | 4 / 6 | 1 / 2 | 17 / 18 | 24 / 27 | 12 / 13 | 0 / 2 | 0 / 2 | 0 / 5 |
| format, opened, seed 15 | 200 | 56 | 191 | 11 / 11 | 2 / 2 | 15 / 15 | 11 / 13 | 8 / 9 | 1 / 1 | 0 / 9 | 0 / 2 |
| plain, seed 16 | 200 | 0 | 0 | | | | | | | | |
| partial, seed 17 | 200 | 0 | 0 | | | | | | | | |
| format runs, total onset | 1000 | 263 | 868 | 30 | 6 | 61 | 71 | 44 | 4 | | |

Every trial with an RA failure (216 in the format runs) has an onset class.
Determinism failures appear in created runs because the check itself forks
an opened replica; they are Y-006, the opened-document family.

### Minimal regressions

| Class | Schedule (then sync both ways) | Observed | Admitted |
| --- | --- | --- | --- |
| Y-001 | `r1 insert 0 "et" {bold}; deliver 1->2; r2 format [0,2) {bold:null} ‖ r1 insert 2 "d" {bold}` | e t d | e t d(bold) |
| Y-002 | `r1 insert 0 "au"; deliver 1->2; r1 format [0,2) {bold} ‖ r2 format [0,1) {bold}` | a(bold) u | a(bold) u(bold) |
| Y-003 | `r1 insert 0 "wv"; r1 insert 2 "b" {bold}; deliver 1->2; r1 delete [2,3) ‖ r2 insert 3 "z" {bold}` | w v z | w v z(bold) |
| Y-004 | `r1 insert 0 "a"; deliver 1->2; r1 format [0,1) {italic} ‖ r2 insert 0 "h"` | h(italic) a(italic) | h a(italic) |
| Y-005 | `r1 insert 0 "abc"; deliver 1->2; r1 format [0,2) {bold} ‖ r2 format [1,3) {bold}` | a(bold) b(bold) c | a(bold) b(bold) c(bold) |

These are the hand-derived regressions in `regressions.mjs`; each has a
control that changes one ingredient and passes. `results/campaign.json`
holds the per-run representatives shrunk from the search.

### final-sync

All 48 ops missing at some replica after the final-sync round, over the 25
format trials with a conservation failure (runs 4, 5 and 11 to 15), are
cleanup ops that the replica never received: they were emitted during the
final-sync round after the issuing replica's last outgoing delivery in that
round. The displayed character multisets equal the inserted minus deleted
characters in every case, so no text is lost. In 26 of the 48 the cleanup's
deletion is already present at the replica (its own cleanup deleted the same
marker); in 22 it is not, and the replica holds a live marker that the
issuer has deleted. One further all-pairs round integrates every missing op
in all 25 trials. The one final convergence failure (seed 13, trial 40) is
the same case: replicas 2 and 3 lack replica 1's cleanup, which deletes an
italic marker, and show `g(bold) k(bold,italic) q(bold,italic)` against
replica 1's `g(bold) k(bold) q(bold)` until a further round delivers it.

### other

- Records that no class explains are kept with their item walk. In the
  campaign below every `other` record is either an attribute difference
  inherited from an earlier Y-004 or Y-005 onset at the same replica, or a
  comparison against an empty reference set; the reference set is now the
  admitted views consistent with the displayed character order, so the
  latter no longer occurs.
- Two shapes that first appeared here are specification results, not
  anomalies, and have regressions: the placement pair (sibling order under the
  one-sided and two-sided rules) and the admitted unbold (an unbold interval containing a
  concurrent bold insert).

### Marker-anchored inserts

The four `other` records reported as "character order outside the admitted
orders" (shrunk from seed 11 trial 31, seed 12 trial 18, seed 13 trial 6
and seed 14 trial 20) are not character-order failures. At every step of
each schedule, the history with formats removed and inserted attributes
cleared has a witness for the displayed character order, so the gap rule
with marker origins resolved to characters admits the order Yjs produced.

- Seeds 11 and 12: the admitted views at the failing step exceed the
  enumeration cap of `allFinalViews` (200,000 states), which then returns an
  empty, truncated list; the classifier finds no reference view with the
  same characters and reports the order pattern. Enumerating only placements
  consistent with the displayed order gives one reference view, and the
  differences are Y-004 (an italic opener spreading over concurrent plain
  inserts: `u v u c w g` in seed 11, `g j` in seed 12).
- Seeds 13 and 14: the onset is Y-005 (seed 13, step 6) and Y-004 (seed 14,
  step 4); the later `other` records are attribute differences inherited
  from that onset state, not order differences.

Resolution cannot exclude a position Yjs uses. A marker origin is resolved
to the nearest character to its left, a marker right origin to the nearest
character to its right, and markers never move relative to characters, so
the resolved gap contains the marker-bounded gap; a concurrent insert that
lands between the marker and the resolved character is concurrent with the
new character and may take either order relative to it. The regression
"marker-anchored insert" pins the case in which a concurrent insert lands
exactly there (`a z B b N`, showing `a z b(bold)`, admitted). No refinement
of the resolution rule is needed for these cases; a tighter rule could only
remove admitted views.

### Causal gaps through delete sets

The five `other` onsets of the partial-delivery runs (seed 18 trial 3, seed
19 trials 65, 83, 86 and 151) are not tracking errors. At every step of each
trial, every op the harness counts as integrated has all its structs present
and all its deletions applied at the replica, and no received op with its
whole effect present is left out; Yjs holds nothing pending at the failing
steps. Four of the five show a Yjs behaviour under out-of-order delivery,
pinned by regression Y-007; the fifth is Y-006, the opened-document family.

Yjs holds back a struct until its clock predecessor and its origins are
present (`integrateStructs`), and applies a delete set as soon as the items
it names exist (`readAndApplyDeleteSet`). Neither waits for a causal
predecessor whose update is a delete set alone, which is the update of a
delete and of a format that only removes markers. The replica then shows an
event set that is not causally closed. In plain text the witness search
accepts such a set (a delete needs only the characters it names, and a
deleted character still anchors insertions), which is why `partial-17`
found nothing. With formatting a marker deletion changes attributes, and
the displayed view is the view of no causally closed version.

- Shape A (seed 18 trial 3, seed 19 trials 83 and 86): a marker-removing
  format arrives before the insert that created one of its endpoints. The
  format's endpoint is absent, so its precondition fails in every order and
  the admitted set is empty, which the classifier reports as a character
  order pattern. Minimal: `r1 insert 0 "a" {bold}; r1 insert 1 "b"; r1 format
  [0,2) {bold:null}; send r1#0, r1#2 to r2` shows `a` at r2; the closed
  versions show `a(bold)`, `a(bold) b` and `a b`.
- Shape B (seed 19 trial 151): an insert arrives before the
  marker-removing format issued before it at the same replica. The insert
  wrote no marker because the format had already ended the span there, so
  it lands inside the span at the receiver. Minimal: `r1 insert 0 "ab"
  {bold}; deliver 1->2; r2 format [0,2) {bold:null}; r2 insert 1 "q"; send
  r2#1 to r1` shows `a(bold) q(bold) b(bold)` at r1; admitted
  `a(bold) q b(bold)`; the closed versions show `a(bold) b(bold)`, `a b` and
  `a q b`.

Each shape has a control that sends the same ops in issue order and is
admitted; both shapes converge after the final sync. Seed 19 trial 65 has no
causal gap at its onset: on an opened replica, deleting `m` from
`a p* m* o` also deletes the closing marker and shows `a p* o*`, the
Y-006 case "last character of a run"; a fresh replica synced
instead of opened keeps the marker. Its determinism failure at the same
step carries the `Y-006` label, but onset is taken from view
failures only, and its view failure has no concurrent deleter, so no class
applies.
