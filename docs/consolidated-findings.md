# Consolidated findings: proof obligations as property tests

State of the `yjs-oracle` branch on 2026-10-29. Everything below is
uncommitted in the worktree `/Users/kc/repos/sal-yjs`.

## The question

The framework proves an MRDT RA-linearizable by discharging five
verification conditions, the rc conditions and sequential conformance. Do
the same conditions, run as search on implementations that have no proof,
find the defects those implementations actually have, and agree with the
proofs where proofs exist? The answer measured here is yes on both counts,
with one caveat about what a pass means, stated under limits.

## What was built

`ra-pbt/`, a dependency-free ES module library with two layers.

- **Law layer** (`src/laws.js`): over seeded event sets of a state-based
  datatype `{init, apply, merge3, read}`, checks that every linear extension
  of visibility folds to one state, that merge equals the canonical state
  of the union, VC1 to VC5 as stated in the paper, the rc conditions, merge
  idempotence and initial-state laws, and sequential conformance. A failure
  names the obligation and gives a shrunk event set.
- **End-to-end layer** (`src/checks.js`, `schedule.js`, `witness.js`):
  schedules over replicas of a running implementation with deliveries,
  out-of-order sends and opened replicas; checks convergence,
  RA-linearizability of every version by an exact witness search over the
  causal order, local edit meaning, determinism and conservation; shrinks a
  failure to a representative; declared regressions with controls.

Instances, each with a sequential specification and an adapter:

| Instance | Role | Where |
|---|---|---|
| Yjs text, 13.6.31 pinned | deployed library under test | `ra-pbt/instances/yjs`, `experiments/yjs-oracle` |
| Automerge text with marks, 3.5.0 pinned | deployed library under test | `ra-pbt/instances/automerge`, `experiments/automerge-oracle` |
| Loro text with styles, 1.17.1 pinned | deployed library under test | `ra-pbt/instances/loro`, `experiments/loro-oracle` |
| Notion block editor demo (hash-pinned modules) and its corrected variant | product model under test, and its repair | `ra-pbt/instances/notion`, `experiments/notion-ra-pbt` |
| Notion production editing code, text layer (63 assets pinned 2026-10-29, vendored at `vendor/notion-production/` under its own notice) | product code under test | `ra-pbt/instances/notion-production-text`, `experiments/notion-production-text` |
| Notion production editing code, block layer | product code under test | `ra-pbt/instances/notion-production-blocks`, `experiments/notion-production-blocks` |
| Sal runtime OR-set and RGA | positive control, verified counterparts | `ra-pbt/instances/sal-runtime` |
| Broken OR-set and broken RGA | negative control | `ra-pbt/instances/sal-runtime` |

## What was formalised

**Sequential specifications written for this work.**

- Text with marks for Yjs: characters with identities, insertion under the
  strong list specification (anywhere strictly between the recorded left
  and right origins), idempotent delete, format as an identity-bounded
  interval that covers concurrent inserts inside it, inserted text carrying
  exactly its attributes. Two deterministic refinements are kept because
  their refutations are results (`experiments/yjs-oracle/SPEC.md`).
- Text with marks for Automerge, in two readings: Peritext anchors (a mark
  is a pair of positions fixed by the expand policy; a character is covered
  when it stands between them) and markers (a mark's begin and end are list
  elements placed by the strong list rule). The two differ exactly at a
  concurrent insert on a boundary.
- Text with styles for Loro, in five readings of what a style covers
  (carry, inherit, expand, anchors, persistent), the first four refuted by
  a minimal shape each and the fifth, in which styles are ranges between
  anchor elements placed by the gap rule, holding within the bounds
  searched.
- The Notion block model: a sequential specification of split, merge, bold
  and insert over blocks, plus the paper's rc relations and generators for
  the law layer.
- The paper's OR-set and RGA specifications with their rc relations, and a
  live-anchor list specification kept as a pinned negative.

**The proof obligations as executable properties.** VC1 merge
commutativity, VC2 merge with the initial state, VC3 local redistribution,
VC4 causal delta, VC5 redistribution, rc non-commutation, no rc chain,
conditional commutation, specification non-commutation, sequential
conformance (clause 2 of RA-linearizability), merge idempotence. Each is a
function of a datatype, a generator and an rc relation, and each has a
negative control that it catches.

**Lean counterparts.** `Sal/MRDTs/Instances/YjsMarkerCounterexample.lean`
renders the measured marker lists of the Yjs marker-ownership case and
proves the merged document differs from both sequential outcomes and that
supplying the missing closer restores one. `YjsDeleteSetCounterexample.lean`
models the delivery rule that admits a delete-set-only update whose
predecessor is absent and proves the resulting view differs from every
causally closed version. Both by `decide`, standard axioms only. Neither is
a model of the integration algorithm; each is a semantic counterpart of a
measured execution, written once per distinction.

## Defects found

Ids are stable. "Reproduction" means a self-contained script importing only
the library, with expected and observed output, in a `repro/` directory.

### Yjs (`docs/yjs-oracle.md`)

| Id | Shape | Mechanism | 13.6.31 | 13.6.33 | 14.0.0-rc.29 | Upstream |
|---|---|---|---|---|---|---|
| Y-001 | bold insert relying on an opener a concurrent unbold deletes | `formatText` absorbs an equal opener and omits its closer | yes | yes | yes | yjs/yjs#828 |
| Y-002 | nested concurrent bolds; outer opener judged redundant | positional cleanup after the transaction | yes | yes | yes | #828 |
| Y-003 | delete of a bold character strips a concurrent bold insert after it | delete-time gap cleanup removes the span's closer | yes | yes | yes | #828 |
| Y-004 | format spreads over a concurrent insert at its boundary | marker and character ordered by client at the boundary | yes | yes | yes | comment on #385 |
| Y-005 | overlapping concurrent same-key formats lose a span | closer absorbed, extent lost | yes | yes | yes | comment on #382 |
| Y-006 | delete on an opened replica formats its neighbour; no concurrency | text type built after the state lacks the formatting flag and keeps the index cache | yes | yes | no | not reported, removed in v14 |
| Y-007 | delete-set-only update applied before the insert it follows | `readAndApplyDeleteSet` applies any range whose ids exist; no causal buffering for delete sets | yes | yes | yes | yjs/yjs#829 |
| Y-008 | struct past a same-client clock gap integrated behind a `Skip` | v14 `integrateStructs` fills the gap when origins exist | no | no | yes | #829 |

Three root causes: formatting as unowned marker items (Y-001 to Y-005),
delivery without causal buffering (Y-007, Y-008), the flags on a lazily
built root type (Y-006). The list algorithm itself passed every check under
the strong list specification: plain text and partial delivery, 400 trials,
7,192 versions, no failure. Formatting exactness on a single replica held
on 53,784 probes with both companions rejected on every probe where they
could be.

### Automerge (`docs/automerge-oracle.md`)

| Id | Shape | Mechanism | Status |
|---|---|---|---|
| A-001 | concurrent insert at a non-expanding boundary covered by the mark when the mark's operation has the larger counter; control without the counter-raising delete is correct | mark begin and end are insert operations ordered against concurrent inserts by operation id; expand flags are read only when placing a local insert | defect against the semantics the documentation names (Peritext's preceding-character rule); automerge/automerge#1649 |
| A-002 | single replica: bold `q`, link `q`, delete `q`, type `i`: `i` is bold; without the link it is plain | one sticky insertion point serves every mark name | local-meaning defect; automerge/automerge#1650 |
| A-003 | after deleting an italic character, a new character is plain | Automerge skips an emptied begin/end pair | specification artefact of the anchor reading, recorded as a refuted candidate |

Automerge is RA-linearizable under the marker specification: 2,000 trials,
no failing version. The Yjs classes re-expressed on Automerge pass (Y-001,
Y-002, Y-003, Y-005, Y-007), Y-004 becomes A-001 when the counter is
raised, and opened replicas agree with created ones. The one A-001 trace at
the end of the text rests on a specification choice Peritext does not make
and is marked as such.

### Loro (`docs/loro-oracle.md`)

| Id | Shape | Mechanism | Status |
|---|---|---|---|
| L-001 | a character typed concurrently at a style boundary takes the style or not according to peer id, for every expand setting; 545 of 1,002 records are on a side the key's expand setting does not extend to | style anchors are ordinary Fugue list elements, ordered against a concurrent insert with the same neighbours by peer | defect against Loro's own expand documentation; the expand-after start case was reported in loro-dev/loro#1009 (June 2026, open, no maintainer reply); our comment there adds the peer-id dependence and the mechanism |
| L-002 | single replica: style a span, remove the style, type at its start: the new character takes the style; or style one character, delete it, type into its gap | the anchor scan for a local insert, and reversed expand on unmark | local-meaning defect; loro-dev/loro#1240 |
| L-003 | single replica: unlink the middle of a link, type at the hole's left boundary: the character is linked, though links expand nowhere | same | local-meaning defect; #1240 |
| L-004 | single replica: two adjacent link spans with one value; typing between them gets no link though one link is displayed | same | local-meaning defect; #1240 |
| L-005 | concurrent bold and superscript on one character, then a local insert before it misses the superscript | same | local-meaning defect; #1240 |

Loro's list is Fugue and, like Yjs's, satisfies the strong list
specification and neither deterministic refinement: 800 plain-text trials
pass under the gap rule, the one-sided rule fails a hand-built five-insert
history (Fugue makes a head insert a left child of its recorded right
origin) and the two-sided rule fails in 9 of 200 trials. No convergence,
determinism, conservation or causal-gap failure in 9,200 trials and 135,417
checked versions; Loro holds back every change with missing dependencies,
deletes and unmarks included, so the Yjs delivery classes do not arise.
Of the Yjs formatting classes only boundary spread (Y-004) recurs.

### Across the three libraries

Boundary spread is the one class all three share: Y-004 in Yjs, A-001 in
Automerge, L-001 in Loro. In each, a mark boundary is a list element
ordered against a concurrent insert by identity, so whether the insert is
covered depends on client, counter or peer rather than on the mark's
policy. Yjs alone has the marker-ownership classes, because Yjs alone lets
a format's extent depend on markers it did not create; Yjs alone applies
delete sets without causal buffering. Automerge and Loro each have a
single-replica insertion-point defect (A-002, L-002 to L-005) arising from
one sticky insertion point serving every mark name.

### Notion block editor (`docs/notion-ra-pbt.md`)

All five catalogued defects are detected through the library, each by a
property naming the obligation violated, with shrunk counterexamples no
larger than the existing traces (N-001 five requests against eight).

| Defect | Detecting property | Obligation |
|---|---|---|
| N-001 | local meaning (split), RA-linearizability | local effect; RA-linearizability |
| N-002, N-003 | local meaning (bold), RA-linearizability | same |
| N-004 | conservation, RA-linearizability; sequential conformance in the law layer | conservation; clause 2 |
| N-005 | conservation, RA-linearizability; sequential conformance | same |

Every merge law (VC1 to VC5, join, rc, idempotence) passes on both the
demo and the corrected model, because the replica merge is a union of
transactions. Sequential conformance is the only law that fails, and only
on the demo. So the Notion defects live in issuing and replaying requests,
not in merge. The corrected model fails only N-002 and N-003, as the
existing experiments report. Two further demo shapes outside the catalogue
were found, a split replayed after a concurrent merge that moves no text
and the empty-block removal path, neither on the corrected model.

### Notion production editing code, text layer (`docs/notion-production-text.md`)

Measured the same way as the three libraries, the production text CRDT
passes formatting under causal delivery: plain text satisfies the strong
list specification and the one-sided RGA rule (not the two-sided one);
bold is RA-linearizable under the anchor specification the operations
record (2,000 trials, 34,596 versions, no failure); determinism,
convergence and conservation hold over 3,800 trials; the five Yjs
formatting classes give admitted documents. Three refuted readings: the
positional specification lacks left-neighbour inheritance of bold (NT-1),
the two-sided list rule (NT-2), the Yjs-style interval reading of a format
(NT-3). The passing witness orders inserts and annotations by id and places
each delete after the largest id in its past; it works because the list is
RGA, format boundaries sit on the sides of existing characters, and
conflicting formats are settled by largest id, a candidate composition
theorem. One defect outside the client's delivery contract: under
out-of-order delivery, an insert that arrives before its origin after the
origin was split is rebuilt from a partial chain, and the original insert
is then swallowed as a duplicate, losing the rest of the run for good
(P-4). Whether Notion's transport ever delivers out of order is unknown.

### Notion production editing code, block layer (`docs/notion-production-blocks.md`)

Six defect classes of the production split and merge path, none of them a
demo defect, each with a minimal trace, a control and a reproduction:

| Class | Shape | Mechanism |
|---|---|---|
| label-divergence | concurrent splits, then an insertion into a split block is rejected at the other replica; replicas diverge for good | slice labels are reassigned by binary subdivision at every split, so they depend on the order concurrent splits were applied; a receiver routes an operation only to slices in its label's range |
| past-boundary | a second split, or an insertion at a block's start, concurrent with a merge is rejected | the merge's split marker reserves twenty ticks, so a concurrent item sorts past the end of the origin's slice |
| concurrent-move | two concurrent splits move the same slice; last move applied wins, no rejection | both splits move the slice by its start item |
| stale-merge | a late duplicate merge of a removed block moves its text again | the move handler proceeds when the source block is already removed |
| removed-anchor | a block listed after a merged-away block goes to the end of the page | `listAfter` appends when its anchor is missing |
| order-mismatch | block order follows application order, text division follows identifiers; no single order explains both | two orders in one document |

Each class shows at a replica that applied causally ordered records, so a
sequencing server receiving them in that order would show it; what a live
client does with a rejected transaction is outside the experiment. N-001,
N-004 and N-005 pass on the production path; N-002 and N-003 have the
correct local effect but the bold is rejected at the other replica by label
divergence after the final exchange, which the main-tree replays could not
see because they never compared replicas after a full exchange. Two harness
choices are documented: trees are parsed with the editor's per-instance
clock holders rather than the client adapter's single clock (the single
clock gives two concurrent-free splits the same marker id), and clients
share one runtime for memory.

### Sal runtime (`ra-pbt/instances/sal-runtime/README.md`)

The codec omits the content id of a commit whose child follows it in the
same delta, and `ingest` skips only ids on the wire, so a receiver fed two
deltas computed against the same have-set stores one commit twice and
diverges. `syncReplicas` never produces such deltas; a transport with
overlapping deltas in flight would. The runtime is unmodified.

### The paper's own definitions

The law layer, from random executions alone, reproduces the mismatch found
earlier by reading the definitions: the paper sets rc empty for RGA, while
the list specification does not commute insert-after-x with delete-x, so
specification non-commutation fails on the verified RGA and nothing else
does. End to end, the runtime's RGA passes under the paper's
anchor-retaining specification and fails under a live-anchor one, pinned
by a test.

## Specification results, not defects

- Yjs's list algorithm satisfies the strong list specification and neither
  deterministic refinement: the one-sided rule fails a ten-request history
  (a cycle through client-ordered siblings and program order) and the
  two-sided rule a five-request one. Recorded as the placement pair.
- An unbold whose interval holds a concurrently inserted bold character that
  keeps its bold is admitted (the admitted unbold); so are marker-anchored
  inserts.
- Automerge's marks satisfy the marker specification; the difference from
  Peritext's anchors is observable only under concurrency at a boundary.
- A-003, above.

## Controls

Positive: the verified OR-set and RGA pass every law except the known
specification non-commutation on RGA; Yjs plain text passes; Automerge
passes the Yjs formatting shapes; the corrected Notion model passes where
the earlier experiments say it does. Negative: the broken OR-set and RGA are
each caught by at least one verification condition with counterexamples of
one to three events; every SPOT-style expected value has a companion
pinning the tempting wrong answer; formatting exactness rejects over-wide
and under-wide expectations on every probe; every class has a control
schedule that passes.

## Verification status

| Suite | Result |
|---|---|
| `ra-pbt` library tests | 48 of 48 |
| Yjs: spec tests, regressions, facts, opened-document, exactness | 26, 28 of 28, 11 of 11, 8 of 8, 0 failures |
| Yjs reproductions | 7 of 7 on 13.6.31 and 13.6.33; 6 of 7 plus Y-008 on rc.29 |
| Automerge: spec tests, regressions, reproductions | 12 of 12, 18 of 18, 3 of 3 |
| Loro: spec tests, regressions, reproductions | 17 of 17, 54 of 54, 5 of 5 |
| Notion production text: spec tests, regressions, reproductions | 14 of 14, 24 of 24, 6 of 6 |
| Notion production blocks: spec tests, regressions, reproductions | 15 of 15, 35 of 35, 6 of 6 |
| Notion: regressions | 34 of 34 |
| Lean counterexamples | both build, standard axioms |

## Upstream

- yjs/yjs#828: Y-001 to Y-003, three scripts, common cause, links to
  #382, #385, #291, #521.
- yjs/yjs#829: Y-007 and Y-008, framed as a question about intermediate
  states, since the documentation promises only convergence.
- Comments with scripts on yjs/yjs#382 (Y-005) and #385 (Y-004).
- automerge/automerge#1649 (A-001, both interior shapes, with the question
  whether expand governs concurrent inserts) and #1650 (A-002), posted
  2026-10-29. The repository has no contributing file, issue template or AI
  policy.
- loro-dev/loro#1009, comment with the L-001 script, peer-id dependence
  and mechanism (the thread reported the expand-after start case in June
  2026); loro-dev/loro#1240 for L-002 to L-005. Posted 2026-10-29.

## Open items

1. Watch the eight upstream threads (four Yjs, two Automerge, two Loro)
   and answer; record every verdict with its date.
2. #291 and #521 on the Yjs tracker are cited as earlier sightings without
   having been run through the classifier.
3. The Notion instance made two choices that affect verdicts (the position
   of the demo merge's own split marker; bold checked against the selection
   rather than the emitted annotation), to be checked against the catalogue.
4. Nine library gaps listed by the Notion instance, six by the Automerge
   instance and six by the Loro instance, all worked around inside the
   instances; the library source is unchanged since the Yjs migration, and
   `ra-pbt/README.md` does not yet list the new instances.
5. The runtime `ingest` finding: fix before artifact export, or document.
6. Nothing is committed.

## Limits

The end-to-end check is RA-linearizability with respect to the causal
order, program order included, the standard definition; the paper's
criterion orders only dependent and non-commuting pairs, so a view can be
admitted by the paper and have no causal-order witness, as a pinned OR-set
case shows (`ra-pbt/test/endtoend-sal.test.js`). Only the law layer
evaluates the paper's order. The upstream reports rest on two-operation
shapes where both orders agree and on specifications that retain
identities, so this distinction does not affect them. A pass is a
measurement on a pinned version over bounded schedules, not a
proof. The witness search is exact but bounded (twenty events, witness
bound twelve). The law layer samples states beyond four events. The
runtime's `apply` is partial and the adapters fall back to the paper's
total effect where the guard fails. Declared regressions compare displayed
views after `normalise`, so instances whose `normalise` drops information
write their negatives directly.
