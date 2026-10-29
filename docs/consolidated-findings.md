# Consolidated findings: proof obligations as property tests

Historical measurements from the `yjs-oracle` source baseline `14f073e`,
committed in `/Users/kc/repos/sal-yjs` on 2026-10-29. Its integration into
`/Users/kc/repos/sal` is currently uncommitted. Counts below describe those
recorded campaigns, not fresh runs on the integrated tree. The law-layer
commutation evaluator was corrected during review: historical law verdicts and
counts are pre-review candidates pending reruns with the corrected evaluator.

## The question

The framework proves an MRDT RA-linearizable by discharging five
verification conditions, the rc conditions and sequential conformance. Do
the same conditions, run as search on implementations that have no proof,
find the defects those implementations actually have, and agree with the
proofs where proofs exist? The recorded executions find concrete defects and
provide bounded agreement on positive controls. Agreement between the law
layer and the formal obligations remains under review; see the provenance
warning above and the limits below.

## What was built

`ra-pbt/`, a dependency-free ES module library with two layers.

- **Law layer** (`src/laws.js`): over seeded event sets of a state-based
  datatype `{init, apply, merge3, read}`, samples agreement of linear extensions
  of the event-indexed `lo_E`, that merge equals the canonical state
  of the union, VC1 to VC5 as stated in the paper, the rc conditions, merge
  idempotence and initial-state laws, and sequential conformance. A failure
  names the obligation and gives a shrunk event set.
- **End-to-end layer** (`src/checks.js`, `schedule.js`, `witness.js`):
  schedules over replicas of a running implementation with deliveries,
  out-of-order sends and opened replicas; checks convergence,
  causal-history conformance of eligible versions by witness search over
  supplied dependencies, local edit meaning, determinism and conservation; shrinks a
  failure to a representative; declared regressions with controls.

The legacy end-to-end key `raLinearizability` is not a paper-RA verdict:
current results carry `paperRaVerdict: 'not-checked'`. The checker preserves
all supplied causal edges and adds no concurrent implementation `rc` edges;
its order and the paper's `lo_E` can be incomparable. A missing witness
rejects this causal-history criterion only. Relating either verdict to
paper RA requires a separate order and interface correspondence argument.
Partial-record skips, bound skips and missing-dependency gaps must accompany
coverage claims; a slice with dropped dependencies is not a causally closed
paper-model version. See [the library note](ra-pbt.md).

Instances, each with a sequential specification and an adapter:

| Instance | Role | Where |
|---|---|---|
| Yjs text, 13.6.31 pinned | deployed library under test | `ra-pbt/instances/yjs`, `experiments/yjs-oracle` |
| Automerge text with marks, 3.5.0 pinned | deployed library under test | `ra-pbt/instances/automerge`, `experiments/automerge-oracle` |
| Loro text with styles, 1.17.1 pinned | deployed library under test | `ra-pbt/instances/loro`, `experiments/loro-oracle` |
| Notion block editor demo (hash-pinned modules) and older `anchor-absorb` variant | demo model and block-merge repair | `ra-pbt/instances/notion`, `experiments/notion-ra-pbt` |
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
  elements placed by the strong list rule). They differ at concurrent
  boundary inserts and on emptied marks; the expanding end sentinel is an
  additional choice of the anchor reading.
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

Measured mechanisms include marker reuse/cleanup (Y-001 to Y-003 and Y-005),
boundary ordering (Y-004), delivery without causal buffering (Y-007, Y-008),
and flags on a lazily built root type (Y-006). No common repair is established.
The list algorithm itself passed the recorded checks under
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

No checked version lacked a marker-specification witness in 2,000 bounded
Automerge trials; this is not a proof of RA-linearizability. The Yjs classes
re-expressed on Automerge pass their declared cases (Y-001,
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

Loro's list is Fugue. No version checked in 800 plain-text trials lacked a
strong-list (gap-rule) witness. Both tested deterministic refinements have
counterexamples: the one-sided rule fails a hand-built five-insert
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
| N-001 | local meaning (split), causal-history conformance | local effect; stated dependency-history criterion |
| N-002, N-003 | local meaning (bold), causal-history conformance | same |
| N-004 | conservation, causal-history conformance; law-layer conformance candidate | conservation; specification witness under the tested order |
| N-005 | conservation, causal-history conformance; law-layer conformance candidate | same |

The historical law campaign reported no merge-law failures on either
transaction-archive model and reported sequential-conformance failures on
the demo. Those verdicts remain pre-review candidates pending evaluator
reruns. The carrier's `merge3` unions transaction sets; this is distinct from
the editor's block-merge request. The concrete failures concern issuing or
replaying requests, including replay of block-merge transactions, and a
union carrier does not establish their correctness. The older
`anchor-absorb` block-merge repair reproduces N-002 and N-003 and passes the
other catalogue regressions. The recorded bounded searches also found a
split after a concurrent merge and the empty-block removal path on the
demo. This comparison does not test today's repaired rich-text model or
the separately extracted production bundle on main.

### Sal runtime (`ra-pbt/instances/sal-runtime/README.md`)

The codec omits the content id of a commit whose child follows it in the
same delta, and `ingest` skips only ids on the wire, so a receiver fed two
deltas computed against the same have-set stores one commit twice and
diverges. `syncReplicas` never produces such deltas; a transport with
overlapping deltas in flight would. The runtime is unmodified.

### The paper's own definitions

The historical law layer reported specification non-commutation on the RGA
counterpart and interpreted it as a mismatch between the paper's empty rc
relation and the list specification. That diagnosis remains a candidate;
the old evaluator output does not establish a mismatch in the paper's
definitions. It requires a rerun after the commutation-evaluator correction.
End to end, the runtime's RGA passes the recorded bounded runs under the
paper's anchor-retaining specification and fails under a live-anchor one, pinned
by a test.

## Specification results, not defects

- Yjs plain text has witnesses in the recorded strong-list search; both
  tested deterministic refinements have counterexamples. The one-sided rule
  fails a ten-request history
  (a cycle through client-ordered siblings and program order) and the
  two-sided rule a five-request one. Recorded as the placement pair.
- An unbold whose interval holds a concurrently inserted bold character that
  keeps its bold is admitted (the admitted unbold); so are marker-anchored
  inserts.
- Automerge's checked versions have marker-specification witnesses. The
  anchor reading differs at concurrent boundaries and on emptied marks
  (A-003); the expanding end-of-text trace depends on a custom end sentinel.
- A-003, above.

## Controls

Positive: historical law results for the OR-set and RGA counterparts await
reruns after the evaluator correction; Yjs plain text passes its bounded
checks; Automerge passes the declared Yjs formatting shapes; the older
Notion block-merge repair passes where
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
3. Preserve the Notion instance's explicit specification choices: merge
   marker completion makes the N-004 trace interpretable; selection-based
   bold matches the catalogue's request contract. See `docs/notion-ra-pbt.md`.
4. Nine library gaps listed by the Notion instance, six by the Automerge
   instance and six by the Loro instance, all worked around inside the
   instances; the library source is unchanged since the Yjs migration, and
   `ra-pbt/README.md` does not yet list the new instances.
5. The runtime `ingest` finding: fix before artifact export, or document.
6. Rerun historical law campaigns after the evaluator correction and record
   the integrated revision, command, seed, bounds and skipped checks.

## Limits

A pass is a measurement on a pinned version over bounded schedules, not a
proof. The witness search is exact but bounded (twenty events, witness
bound twelve). The law layer samples states beyond four events. The
runtime's `apply` is partial and the adapters fall back to the paper's
total effect where the guard fails. Declared regressions compare displayed
views after `normalise`, so instances whose `normalise` drops information
write their negatives directly.

The 832 failing anchor trials reported for Automerge include A-003 and
specification-sensitive end-of-text behavior; they are not a count of 832
library defects. The two non-expanding-boundary reproductions do not depend
on the expanding end sentinel. Historical law counts cannot establish
general commutation or discharge a universally quantified obligation.
