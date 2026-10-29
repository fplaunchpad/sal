# Notion production text: RA-linearizability of the shipped editing code

## Research question

Three deployed libraries measured with `ra-pbt` (Yjs, Automerge, Loro) satisfy
the strong list specification for plain text, and all three fail formatting
when an insertion is concurrent with a mark at its boundary, each by its own
mechanism: Yjs because a format's extent depends on marker items it does not
own, Automerge and Loro because a mark boundary is a list element ordered
against the concurrent insertion by identity (`docs/yjs-oracle.md`,
`docs/automerge-oracle.md`, `docs/loro-oracle.md`). The editing code that
production Notion clients execute is a fourth design: an RGA list with
Lamport identities and annotation operation sets attached to the sides of
characters. Measured the same way, at the text layer of one block (insertion,
deletion, bold), does it pass where the others fail, and if so, why?

## Claims and falsifiers

Stated before the campaign. The source reading of the modules named below
and a 30-trial pilot preceded them; the pilot is not counted in the results.

| Claim | Statement | Falsifier | Check |
| --- | --- | --- | --- |
| T1 | Plain text within a block satisfies the strong list specification (an insertion lands strictly between its recorded origin and its visible right neighbour), on created and on opened replicas; additionally record which deterministic refinements pass: `left` (immediately after the recorded origin) and `both` (immediately before the visible right neighbour) | a version with no witness | `raLinearizability`, plain mixes |
| T2 | Text with bold is RA-linearizable under the anchored reading: an annotation covers exactly the characters between its recorded start and end anchors ('before X' is the gap before character X, 'after X' the gap after it), including characters inserted into that range concurrently or later; a removal clears the same range; a character takes the last-applied covering annotation | a version with no witness | `raLinearizability`, bold mixes |
| T3 | Local meaning: the effect of every request on its issuing replica is the index-level request semantics of `experiments/notion-oracle/positional-spec.mjs` (plain insertion, deletion of a range, bold as a toggle) | one disagreement | `localMeaning` |
| T4 | Determinism: the same request on the same display has the same result on a replica created with the block and on one opened from a snapshot | the two differ | `determinism` |
| T5 | Convergence under causal delivery, in arbitrary interleavings, and no character lost or kept | two replicas with the same integrated records differ; a conservation failure | `convergence`, `conservation` |

A falsifier is a defect only if no reasonable reading of the specification
admits the view. Where a failure depends on a choice the specification made,
the alternative is stated and run, and the result says which reading the
implementation satisfies. Delivery out of causal order is outside the
library's contract ("deliver each batch once, after its causal
predecessors"); it is measured as a separate probe, not as part of T1 to T5.

## Answer in brief

| Claim | Verdict |
| --- | --- |
| T1 | Holds under the gap rule and under the one-sided rule `left`, created, opened, partial delivery and four replicas: six runs, 1,200 trials over 800 distinct schedules, no failing version. The two-sided rule `both` is refuted by a three-insertion history (NT-2). |
| T2 | Holds: 2,000 trials with bold under the anchored reading (gap and left rules, created, opened, partial, sixteen requests), 34,596 checked versions, no failing version. The Yjs-shaped interval reading is refuted (NT-3), because a bold's end anchor is the gap before the next item, so text placed there is covered. |
| T3 | Refuted as stated, by one class only (NT-1): a typed character takes the bold of its left neighbour, which the positional semantics does not model. With that inheritance rule added (`inherit`), no disagreement in the eleven runs that use it (2,200 trials); deletion and bold toggles always had their positional meaning. |
| T4 | Holds: no determinism failure in 3,800 trials, every request forked onto a created and an opened replica. |
| T5 | Holds: no convergence or conservation failure in 3,800 trials. |

Every Yjs formatting class re-expressed on the shipped code (Y-001 to Y-005)
gives a view the specification admits. Of the boundary-spread family that all
three libraries share, the shipped code has the deterministic half only: an
insertion concurrent with a bold is never covered at the left boundary and
always covered at the right boundary, whichever session has the greater id.

The probe without causal buffering finds two ways to lose or keep text
permanently: a deletion that arrives before its insertion is applied as a
no-op (P-1), and an insertion whose first characters a backfill already
supplied is dropped as already applied, losing the rest of its text (P-4,
inside the shipped out-of-order path).

## Reality oracle

The code is the editing code of the production Notion web client as served
on 29 October 2026, extracted by `experiments/notion-production-client` of
the main tree: 63 public application assets (9,006,862 bytes) are downloaded
and checked against the SHA-256 recorded in its `sources.json`; Acorn
extracts 4,335 module bodies as verbatim byte ranges; `extract.mjs` writes a
standalone export (`index.mjs`, `client.mjs`, `runtime.mjs`, `requests.mjs`,
`modules.json`, `sources.json`) that needs only Node. The extraction's own
19 controls passed before the export was written. The application bootstrap
is not run; editing functions have no replacement implementations; missing
dependencies fail.

The export is Notion's code and is vendored at `vendor/notion-production/`
with a notice that the repository's licence does not cover it and that it is
included only so the measurements can be repeated; `NOTION_PRODUCTION_LIBRARY`
names another export when set. The
instance records only digests. `verify-sources.js` runs before and after
every search, replay, regression and probe run, at one of two levels:

- level 1 (always):
  holds exactly the six files, and each has the SHA-256 pinned in
  `ra-pbt/instances/notion-production-text/sources.json`. The pinned digests
  include the export's asset manifest, so the public URLs and asset digests
  cannot change unnoticed;
- level 2 (when `NOTION_PRODUCTION_CACHE` names the download cache): every
  asset has the manifest's length and SHA-256, and every module body in
  `modules.json` is exactly the source slice of its asset at the recorded
  offsets. This ties the running code to the public bytes rather than to an
  earlier export. Every campaign run and the probe ran at level 2.

A regression copies the export to a temporary directory outside the
repository, changes one date in its manifest without changing its length,
and checks that verification rejects the copy and accepts it once restored.

### Replicas

A replica is one `createClient(session)` of the export, with session `s<r>`
for replica r, and one block. A created replica builds the block record itself
with the shipped empty-tree constructor (`createBlock`); the text instance id
is derived from the block id, so every created replica holds the same empty
record. An opened replica is `createClient(session, snapshot)` from another
replica's `snapshot()`. Every request goes through the shipped operation
builders (`prepareInsert`, `prepareDelete`, `prepareBold`) and the shipped
record handler (`apply`); visible text and bold are read from the shipped
`text()` and rich-text serialisation, and checked against a walk of the
shipped text slice's item list, which supplies character identities.

Bold requests are toggles, as in the positional semantics: removal when
every selected character is bold on the issuer's display, addition
otherwise; the builder then takes that explicit choice.

### Identities and anchors

Read from the operations the builders emit, and checked on every record:

| Operation | Field | Reading |
| --- | --- | --- |
| `insertText` | `id: [session, counter]`, `content` | the k-th character has `[session, counter + k]`; the run's characters are found at the requested indices after the insertion |
| | `originId` | the recorded origin of the first character (`start` for the head); each later character's origin is the character before it |
| | (none) | the visible right neighbour at issue time is recorded by the adapter as `rightOrigin` for the gap and two-sided rules; the operation carries no right origin |
| | `prevItems` | the origin's chain back to the slice start, with content, deletion flag and annotation operations; used only by the receiver's backfill |
| `deleteText` | `idRanges: [[id, length]]` | expanded to character ids; must equal the selected characters' ids |
| `addAnnotation`, `removeAnnotation` | `id`, `start: {id, anchor}`, `end: {id, anchor}`, `annotation: ['b']` or `annotationKey: 'b'` | the specification's annotation, with value true or null; the first and last selected characters are recorded for the interval reading |

The adapter cross-checks every record: its ids exceed every id in its causal
past (the counter is a Lamport clock), and every character it names was
inserted by a record in its past. No anomaly was recorded in 3,800 trials.
For bold, every anchor the builder emitted was 'before': the start before the
first selected character, the end before the item following the last one,
which may be a tombstone or the end item.

### Delivery

The client applies an operation once and does not buffer: a duplicate is
dropped, a deletion of absent characters changes nothing, an annotation with
an absent anchor throws, and an insertion with an absent origin triggers a
backfill. The adapter is therefore the transport: it applies a record at
most once and only after every record in its causal past, so every schedule,
single-record sends included, is delivered causally; a record that arrives
early is held, and `hasPending` reports it. In the partial-delivery runs 524
of 1,202 sends were held.

## Specification choices

`ra-pbt/instances/notion-production-text/spec.js` imports nothing from the
library; its only import is the request semantics of `positional-spec.mjs`.
A state is a list of characters with identities, deleted characters
remaining as anchors, and the applied annotations in application order.

**List rules.** `gap`: strictly between the recorded origin and the visible
right neighbour (relational; the search is directed by the identities in
the displayed view). `left`: immediately after the recorded origin. `both`:
immediately before the visible right neighbour when there is one, else after
the origin.

**Annotation readings.** `anchored`: an annotation is a range between its two
recorded anchors, coverage is read from the positions of the characters when
the view is read, and a character's bold is the value of the last-applied
covering annotation; an inserted character carries nothing. `interval`: the
Yjs-shaped reading, in which an annotation sets or clears bold on the
characters from its first to its last selected character when it is applied,
and an inserted character carries the bold its issuer displayed for it.

**Local meanings.** `positional`: `request` of `positional-spec.mjs`, the
claim as stated. `inherit`: the same, except that inserted characters take
the bold of the visible character to their left and are plain at index 0.
The inheritance rule was derived from the source (the origin choice, the
placement immediately after it, the rich-text walk) and confirmed by a
regression before the campaign.

`experiments/notion-production-text/spec-tests.mjs` checks the specification
on 14 hand-derived blocks, each with an inequality against the tempting wrong
answer (the rival rule's placement, the other reading's verdict, a removal
that is a no-op, an insertion that inherits at index 0).

## Results

Each run is 200 seeded trials of twelve requests over two or three replicas
(four replicas and fourteen requests in `plain-four-24`, three replicas and
sixteen requests in the `long` runs), witness search on every version with at
most the bound of edits (12, or 14 and 16 for the longer runs), followed by
the final synchronisation. Requests insert one or two letters, delete one or
two characters, or toggle bold on one or two. Runs sharing a seed execute the
same schedules, so their verdicts differ only by the specification
configuration. 3,800 trials, 1,800 distinct schedules, 37,311 edits (17,637
distinct) and 65,584 checked versions (32,084 distinct); no witness search
was skipped. Results are in `experiments/notion-production-text/results/`.

| Run | Mix | Rule | Reading | Local | Edits | Versions | Failing trials | RA-lin | Local meaning | Determinism | Convergence | Conservation | Classes (trials) |
|---|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| plain-created-21 | plain | gap | anchored | positional | 1,941 | 3,216 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| plain-left-21 | plain | left | anchored | positional | 1,941 | 3,216 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| plain-both-21 | plain | both | anchored | positional | 1,941 | 3,216 | 105 | 556 | 0 | 0 | 0 | 0 | NT-2 105 |
| plain-opened-22 | plain, opened | gap | anchored | positional | 1,675 | 3,220 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| plain-partial-23 | plain, partial | gap | anchored | positional | 1,813 | 3,184 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| plain-partial-left-23 | plain, partial | left | anchored | positional | 1,813 | 3,184 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| plain-four-24 | plain, 4 replicas | left | anchored | positional | 2,469 | 5,200 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-created-31 | bold | gap | anchored | positional | 1,973 | 3,276 | 64 | 0 | 85 | 0 | 0 | 0 | NT-1 64 |
| bold-inherit-31 | bold | gap | anchored | inherit | 1,973 | 3,276 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-left-31 | bold | left | anchored | inherit | 1,973 | 3,276 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-both-31 | bold | both | anchored | inherit | 1,973 | 3,276 | 71 | 379 | 0 | 0 | 0 | 0 | NT-2 71 |
| bold-interval-31 | bold | gap | interval | inherit | 1,973 | 3,276 | 77 | 377 | 0 | 0 | 0 | 0 | NT-3 77 |
| bold-opened-32 | bold, opened | gap | anchored | inherit | 1,659 | 3,216 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-opened-left-32 | bold, opened | left | anchored | inherit | 1,659 | 3,216 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-partial-33 | bold, partial | gap | anchored | inherit | 1,785 | 3,164 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-partial-left-33 | bold, partial | left | anchored | inherit | 1,785 | 3,164 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-long-34 | bold, 16 requests | gap | anchored | inherit | 2,643 | 4,400 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-long-left-34 | bold, 16 requests | left | anchored | inherit | 2,643 | 4,400 | 0 | 0 | 0 | 0 | 0 | 0 | none |
| bold-opened-35 | bold, opened | gap | anchored | inherit | 1,679 | 3,208 | 0 | 0 | 0 | 0 | 0 | 0 | none |

The opened runs opened 910 replicas in all. Local meaning under the
positional semantics failed on 85 of 1,158 insertions in `bold-created-31`
and on none of its 303 deletions and 512 bold toggles. Every failure record
of every run is classified; none is unexplained.

## Classes

Each class has a shrunk trace from the search, a hand-derived regression
with a control in `experiments/notion-production-text/regressions.mjs`, and
a reproduction against the exported library alone in
`experiments/notion-production-text/repro/`. Sessions are s1, s2, s3 for
replicas 1, 2, 3; `x*` is a bold x.

### NT-1: a typed character inherits its left neighbour's bold

Specification artefact of the positional semantics (T3 as stated).

Shrunk: `r1 insert 0 "j" | r1 insert 1 "o" | r1 bold [1,2) | r1 insert 2
"n"` shows `j o* n*`; the positional semantics expects `j o* n`. Regression:
`d`, bold it, type `e` after it: `d* e*`; control: type `e` before it:
`e d*`. Reproduction: `repro/NT-1.mjs`.

Mechanism. `getOriginItemForInsertionIndex` (module 458789) takes the visible
left neighbour as origin (or `start`), `integrateItem` places the new item
immediately after it, and the bold's end anchor is before the following
item; the rich-text walk (module 146739) gives each character the annotation
set at the last anchor before it, so the new character falls inside the
range. At index 0 it falls before the start anchor and is plain. This is
the ordinary editor convention; the positional semantics, written for the
demo campaign, has no rule for it. With the rule added, T3 holds.

### NT-2: the two-sided list rule is refuted

Specification result about the list rule (T1).

Shrunk: `r1 insert 0 "t" | r1 insert 0 "s" | r2 insert 0 "j"` shows `s j t`
everywhere. Regression and `repro/NT-2.mjs`: s1 types `c` then `f` before it,
s2 types `x` into the empty block: `f x c`. Ids c s1:1, f s1:2, x s2:1, all
with origin `start`. Under `both`, f lands immediately before c and the
admitted views are `x f c` and `f c x`; under `left` they are `x f c`,
`f x c`, `f c x`; under the gap rule `f c x`, `f x c`, `x f c`. Control: s2
receives c before typing x (x becomes s2:2): `x f c`, admitted under all
three.

Mechanism. `integrateItem` and `findInsertionPoint` (module 458789) are RGA:
the new item goes after its origin and past every following item whose id
is greater, ids compared counter first and session second (module 117797),
with the counter a Lamport clock (`reserveTicks` and `maybeUpdateClock`,
module 508649). The right neighbour is not consulted. Since the ids are
Lamport, the order of events by id is a linear extension of causality in
which every insertion lands immediately after its origin, which is why the
one-sided rule holds. Yjs and Loro satisfy neither refinement; the shipped
code satisfies the one-sided one, as an RGA should.

### NT-3: a bold covers text placed into its end gap

Specification artefact of the interval reading (T2 holds under the anchored
reading).

Shrunk, three requests: `r1 insert 0 "w" | r2 insert 0 "u" | r2 bold [0,1)`
shows `u* w*`; the interval reading admits `u* w` and `w u*`. The head
siblings are ordered u (s2:1) before w (s1:1), so w lands after u and before
the end item that bounds r2's bold. A five-request trace found by the
search shows the same with a character its own author had unbolded: r1
types `l` and toggles it twice, r3 types `ja` and bolds `a`; after sync
`j a* l*`, since l lands in r3's end gap and r3's annotation s3:3 is greater
than r1's removal s1:3. Regression at the boundary itself and
`repro/NT-3.mjs`: a shared `a`, one replica bolds it while the other types a
plain `h` after it: `a* h*` in both session orders; control: `h` typed before
`a`: `h a*`.

Mechanism. `getTextSliceSpansForAnnotationOperation` (module 300957) anchors
a bold, like every key module 866433 marks as expanding (bold, italic,
strike, underline, highlight, code, suggestions), from before its first
character to before the item following its last; `applyAnnotationOperation`
(module 458789) creates an operation set at each anchor, the start's a copy
of the set in force before it plus the new operation, the end's a copy
without it, and adds the operation to every set between. A character placed
anywhere in the end gap is governed by a set that contains the operation.
The anchored reading says exactly this. The interval reading, under which
Yjs was measured, gives such a character the bold its issuer saw.

### Re-expressed Yjs classes

| Yjs class | Notion schedule | Yjs outcome | Shipped outcome | Admitted (anchored) |
|---|---|---|---|---|
| Y-001 marker ownership | from `a b* c*`, s1 toggles [0,2) (adds) while s2 toggles [1,3) (removes) | `a* b* c*` | `a* b c` | `a* b c`, `a* b* c` |
| Y-002 two formats | from `au`, s1 bolds [0,2) while s2 bolds [0,1) | `a* u` | `a* u*` | `a* u*` |
| Y-002 insert and format | from `q`, s1 bolds it while s2 types `z` at 0 and bolds it | `z* q` | `z* q*` | `z* q*` |
| Y-003 delete removes a closer | from `w v b*`, s1 deletes b while s2 types `z` after it | `w v z` | `w v z*` | `w v z*` |
| Y-004 boundary spread, left | from `a`, s1 bolds it while s2 types `h` at 0 | `h* a*` | `h a*` | `h a*` |
| Y-004 mirrored, right | from `a`, s1 bolds it while s2 types `h` at 1 | `a* h` with these client numbers, `a* h*` with them swapped | `a* h*` in both session orders | `a* h*` (interval: `a* h`) |
| Y-005 overlapping same key | from `abc`, s1 bolds [0,2) while s2 bolds [1,3) | `a* b* c` | `a* b* c*` | `a* b* c*` |

An insertion carries no formatting request in Notion, so a bold insertion is
an insertion followed by a bold, and unbold is the toggle of an all-bold
range. In Y-001 the shipped outcome depends on session order through the
tie between the two annotations' counters (both 5), and both outcomes are
admitted.

## Out-of-order probe

Outside the delivery contract and outside T1 to T5.
`experiments/notion-production-text/out-of-order.mjs` hands every received
record to the client at once, retries a record whose application throws
after every later arrival, and reads integration from the client's own
items, not from the transport. It checks convergence and conservation after
the final synchronisation (RA-linearizability is not checked, since an
insertion that overtakes its predecessors names neighbours the
specification does not hold yet). Seed 41, 200 trials each, partial
delivery.

| Mix | Edits | Sends | Failing trials | Convergence | Conservation | Classes (trials) | Refused and retried | Backfilled insertions |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| plain | 1,754 | 646 | 56 | 57 | 73 | P-1 54, P-4 1, both 1 | 0 | 185 |
| bold | 1,749 | 651 | 37 | 39 | 47 | P-1 37 | 487 | 113 |

**P-1, a deletion ahead of its insertion is lost.** Shrunk: `r1 insert 0 "l"
| r1 delete [0,1) | send 1#1->2`; after the final sync r1 shows nothing and
r2 shows `l`. `applyDeleteTextOperation` (module 458789) collects the items
in each id range with `getTextItemsInIdRange`, finds none, and reports no
change; the record handler (module 971340) exempts deletions from its check
that an operation modified a block, so nothing is raised and the transport
has no reason to redeliver. `repro/P-1.mjs`.

**P-2, an annotation ahead of its anchor is refused.** The handler throws
`Unable to apply annotation operation due to start missing` (or `end
missing`) and keeps nothing. 487 refusals in the bold mix, every one
recovered by redelivery after the insertion arrived; no trial failed through
it. `repro/P-2.mjs`.

**P-3, an insertion ahead of its origin is backfilled.** When the origin is
absent, `backfillPrevItems` (module 971340) inserts the items the operation
lists in `prevItems`, with their content, deletion flag and annotation
operations, then the insertion. The origin's own insertion, arriving later,
is rejected as already applied (`containsOpId`, mapped by module 650747 to
an error class the handler catches and ignores). 298 backfills, converging
in all but P-4. `repro/P-3.mjs`.

**P-4, a partial backfill loses the rest of a run.** Shrunk from the
search and hand-checked: s2 types `hw` (s2:1, s2:2), then `j` after h, which
splits the item into h | w, then `x` after h; x's `prevItems` lists the item
h alone (`s2:1`, length 1). s1 receives the insertion of x first: h is
backfilled and x inserted. When the insertion of `hw` arrives,
`containsOpId` finds an item starting with s2:1 with the same origin and
returns `exists_likely_same` without comparing lengths; module 650747 turns
the rejection into the error class the handler swallows, and w is never
inserted. s2 shows `h x j w`, s1 `h x j`, permanently. Control: without
`j` the item is not split, `prevItems` lists `hw` whole, and both show
`h x w`. `repro/P-4.mjs`. This is a defect of the shipped out-of-order path
itself, which exists to tolerate insertions that arrive before their
origins; whether production transport ever delivers in that order is not
known here.

## Why the shipped design passes

The witness the search finds can be named: order the insertions and
annotations by id, and place each deletion immediately after the greatest id
in its causal past. Since ids are Lamport timestamps compared counter first,
this order extends causality. Three properties of the source then make the
fold of that order under the one-sided rule and the anchored reading equal
the displayed view:

1. the list is RGA, so the item order equals the one-sided fold in id order;
2. an anchor is a side of an existing character, never a list element, and
   the operation set at an anchor holds exactly the annotations whose range
   contains that point (the start set copies the preceding set and adds the
   operation, every set inside the range gains it, the end set copies the
   set without it); so a character's covering annotations are those whose
   anchors enclose it in the final order, which is the anchored reading;
3. the sets are kept sorted by id (module 519193) and resolved in that order
   (module 499116), so the greatest id wins, which is the last-applied rule
   in the id order.

This is an argument from the source checked on 34,596 versions, not a proof.
It suggests a composition condition worth stating and proving in the
framework: a formatting layer over an RA-linearizable list is
RA-linearizable when its boundaries are attached to list elements rather
than inserted among them, and its conflicts are resolved by the same total
order that witnesses the list. Yjs violates both halves (markers are items,
and their effect is decided by position, not by operation order); Automerge
and Loro violate the first (a mark boundary is an element ordered by
identity against a concurrent insertion at the boundary). The anchored
reading the shipped code satisfies is Peritext's anchor semantics for
expanding keys; its price is NT-3: a bold can extend over text another
replica typed concurrently, when the list order puts that text into the
bold's end gap.

## Library gaps and limits

- One block, one text slice. Splits, merges and moves of blocks, which give a
  text instance several slices (`splitIntoSlices`, the slice-start anchors
  with 'after'), are the block layer, measured separately.
- Bold only. Non-expanding annotations (links, mentions), whose end anchor
  is 'after' the last character, and the origin rule that chooses a deleted
  character carrying an 'after' set, are not exercised; every anchor in this
  campaign was 'before'. Colours and multi-instance annotations are not
  exercised.
- ASCII letters only; the grapheme and surrogate-pair validation is not
  exercised.
- Bold is a toggle decided by the adapter from the display, not the editor's
  UI command; inverted (undo) operations, `enforceMonotonicInsertTextOperations`
  and search-label changes are not exercised.
- The record handler runs on fixture records; server acceptance,
  transaction batching, permissions and the production transport are
  outside the scope. Causal delivery is the adapter's; whether the
  production transport preserves it, and so whether P-1 and P-4 can occur in
  deployment, is not established.
- The search is bounded: two to four replicas, twelve to sixteen requests of
  one or two characters, witness search over at most sixteen edits.

## Commands

```sh
export NOTION_PRODUCTION_CACHE=/path/outside/the/repository/notion-prod/cache
export NOTION_PRODUCTION_LIBRARY=/path/to/a/fresh/export   # optional; the default is vendor/notion-production
P=/Users/kc/repos/sal/experiments/notion-production-client
python3 $P/download.py --cache "$NOTION_PRODUCTION_CACHE"
NOTION_PRODUCTION_CACHE="$NOTION_PRODUCTION_CACHE" npm test --prefix $P
node $P/extract.mjs "$NOTION_PRODUCTION_CACHE" "$NOTION_PRODUCTION_LIBRARY"

cd experiments/notion-production-text
node ../../ra-pbt/instances/notion-production-text/verify-sources.js
node spec-tests.mjs
node run.mjs --mode regressions
for r in $(node campaign.mjs list | grep -v verified); do node campaign.mjs run $r; done
node campaign.mjs summarise
node out-of-order.mjs --seed 41 --trials 200 --output results/out-of-order.json
node repro/run-all.mjs
cd ../../ra-pbt && npm test
```
