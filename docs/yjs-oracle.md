# Yjs text: RA-linearizability and local edit meaning

## Research question

Is the shared text type of Yjs, as published, RA-linearizable with respect to
an independent sequential specification of plain and formatted text, and do
its locally issued edits keep their ordinary meaning after concurrent editing?
This asks of a widely deployed library the question the Notion demo campaign
asked of a demo: not whether replicas converge, which they may do on a wrong
document, but whether every version is the result of some sequential history
the specification admits.

The reality oracle is `yjs` 13.6.31 from npm, pinned by version, registry
integrity string and SHA-256 of the distributed module
(`ra-pbt/instances/yjs/sources.json`), executed offline. The specification
(`ra-pbt/instances/yjs/spec.js`) imports no Yjs code. It is a list of
characters with identities and per-character marks: insertion places a
character anywhere strictly between its recorded origin and its recorded
right origin, the strong list specification of Attiya et al. (PODC 2016),
deleted characters remaining anchors; deletion marks by identity and is idempotent; formatting is
an identity-bounded interval that sets or clears a key on every character
between its endpoints when it is applied, so it also covers characters
inserted concurrently between them. Inserted text carries exactly the
attributes passed with it. These are the specification's choices; the anchors
are what the implementation records, as the Notion anchors were, resolved to
the nearest character when the implementation recorded a format marker.

A version is RA-linearizable when some linear extension of the causal order of
the updates it has integrated folds, under the specification, to the view it
displays. The search (`ra-pbt/src/witness.js`) is exact over down-closed subsets of up to
twenty events; since the target view carries identities, each insertion's
placement is forced up to deleted neighbours, so the relational rule costs
little more than a deterministic one.

## Candidate claims and falsifiers

| Claim | Falsifier | Check |
| --- | --- | --- |
| Convergence: replicas with the same integrated updates show the same text and marks | two such replicas differ | `convergence` |
| Plain-text RA-linearizability | a version with no witness | `raLinearizability` |
| Local edit meaning: the view after an edit equals the independent list edit | one disagreement | `localMeaning` |
| Formatting exactness: a format marks exactly its visible range | a selected character left unmarked, an unselected one marked | `localMeaning` on format requests, and `formatting-exactness.mjs` |
| Formatting RA-linearizability | a version with no witness | `raLinearizability` with formatting |
| Partial delivery: the above with updates held and delivered out of causal order, and no text lost after full synchronisation | loss or divergence after synchronisation, or a version no causally closed history admits | `conservation`, the others under `--partial` |
| Determinism: the same request on the same display gives the same result on every replica | two replicas disagree | `determinism` |

## Inheritance policy

Claim 5 requires the inheritance policy to be measured before the
specification fixes it. The measurement (fact b) found two behaviours: text
inserted with an attribute object carries exactly those attributes, and text
inserted with the attributes omitted copies the attributes in effect at the
left neighbour, which fact i then showed to depend on whether the replica
created or opened the document. The specification therefore gives inserted
text exactly its own attributes, and the generator passes an attribute
object with every insert, an empty one for plain text. That choice was fixed
before any search ran and did not change afterwards; the later change to the
specification concerned where an insertion lands, not what it carries, and
every formatting result reported here was produced under the final
specification.

## Measured facts

`facts.mjs` records, with hand-derived expected values and negative
companions, how the pinned version behaves on fixed scenarios: identities per
character and per marker; that inserted text takes exactly the attributes
passed and, with attributes omitted, the attributes in effect at the left
neighbour; that concurrent formatting reaches a concurrently inserted
character inside its range; that pending structs hold an update whose
predecessor is missing; and the two facts that motivate the formatting
results below. All run on Node 26 with the source check before and after.

## Results

Nine seeded searches of 200 trials, twelve requests each over two or three
replicas, witness search on versions with at most twelve edits
(`experiments/yjs-oracle/results/campaign/`). "Versions checked" counts the
replica states on which the witness search ran. "Format requests checked"
counts the format requests whose immediate effect was compared with the
list edit, claim 4. Convergence failed nowhere; conservation, which also
requires every update integrated everywhere and nothing pending after the
final synchronisation, failed nowhere.

| Run | Trials | Edits | Deliveries | Versions checked | Failing trials | RA-linearizability | Local meaning | Determinism | Conservation | Format requests checked |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| plain-16 | 200 | 2,064 | 1,536 | 3,548 | 0 | 0 | 0 | 0 | 0 | 0 |
| partial-17 | 200 | 1,883 | 1,200 | 3,556 | 0 | 0 | 0 | 0 | 0 | 0 |
| format-created-11 | 200 | 1,876 | 1,334 | 3,210 | 41 | 112 | 0 | 12 | 0 | 343 |
| format-created-12 | 200 | 1,852 | 1,382 | 3,221 | 41 | 147 | 0 | 9 | 0 | 333 |
| format-created-13 | 200 | 1,877 | 1,335 | 3,209 | 49 | 163 | 0 | 8 | 0 | 342 |
| format-opened-14 | 200 | 1,612 | 1,418 | 3,262 | 58 | 264 | 0 | 2 | 0 | 336 |
| format-opened-15 | 200 | 1,622 | 1,379 | 3,218 | 52 | 191 | 0 | 9 | 0 | 348 |
| partial-format-18 | 200 | 1,749 | 848 | 3,238 | 37 | 109 | 0 | 10 | 0 | 294 |
| partial-format-19 | 200 | 1,599 | 820 | 3,197 | 51 | 190 | 1 | 3 | 0 | 305 |

The table is from the rerun of 2026-10-29 with the full witness search
(every admitted placement explored, views compared without identities,
at most one million explored states per version). The earlier campaign
directed the search by the target's identity order, which can reject a view
that has a witness when characters repeat; the rerun gave the same failing
trials, the same failure counts and the same classes in every run. The
difference is 107 versions of 29,766 (52 in plain-16, 36 in partial-17, 13,
3 and 3 in format-created-12, format-created-13 and partial-format-18) whose
search exceeded the state cap; they are counted as truncated and neither
passed nor failed, where the directed search had found a witness for each.

Plain text passed every check under the strong list specification. Both
deterministic refinements of it are refuted by plain-text histories, and the
refutations say what the list algorithm's sequential meaning is. The
one-sided rule, insertion immediately after the recorded left origin as in an
RGA specification, fails a ten-request history over three replicas
(the first history of the placement pair): two concurrent head insertions are ordered by client, two
concurrent children of one character are ordered by client, and the issuing
replicas' program orders close a cycle that no linear extension satisfies.
The two-sided rule, insertion immediately before the recorded right origin,
fails a five-request history (the pair's second history): a concurrent head insertion
sorts between a character and its right origin. Yjs places an insertion
somewhere in its recorded gap, as the strong list specification says, and
nothing finer. These are results about which sequential specification the
list algorithm satisfies, not anomalies. A formatting shape found by the
search, an unbold whose interval holds a concurrently inserted bold character
that keeps its bold, is admitted for the same reason (the admitted-unbold
regression).

Formatting did not pass. The failures fall into mechanism classes, each with
a hand-derived minimal regression and a passing control in `regressions.mjs`
(`node run.mjs --mode regressions`):

| Id | Shape | Observed | Admitted | Status |
| --- | --- | --- | --- | --- |
| Y-001 | from `a b* c`, bold [0,2) concurrent with unbold [1,3) | `a* b* c*` | `a* b c`, `a* b* c` | marker ownership; Peritext class for y-richtext, no public report on the current type |
| Y-002 | from `q`, bold [0,1) concurrent with an insert of bold `z` at 0 | `z* q` | `z* q*` | opening marker judged redundant by cleanup; no public report found |
| Y-003 | from `w v b*`, delete `b` concurrent with an insert of bold `z` after it | `w v z` | `w v z*` | deletion removes a neighbour's closer; no public report found |
| Y-004 | from `a`, italic [0,1) concurrent with a plain insert of `h` at 0 | `h_ a_` | `h a_` | boundary spread; issue #385 |
| Y-005 | from `abc`, bold [0,2) concurrent with bold [1,3) | `a* b* c` | `a* b* c*` | overlapping same-key formats; issue #382 |
| Y-007 | from `a* b`, an unbold of both arrives at a replica that has `a` but not the insert of `b` | `a` plain | none: no causally closed version shows it | partial delivery: delete sets bypass causal buffering; no public report found |
| Y-006 | from `a* b* c`, delete `b` on a replica that opened the document | `a* c*` | `a* c` | opened document: single user, no concurrency; no public report found |

Claim 4 also has a dedicated falsifier run, `formatting-exactness.mjs`: on
every reachable state of 60 seeded concurrent histories, forked both as a
created and as an opened replica, every nonempty visible range receives each
of four attribute deltas on a fresh copy, and the result is compared with
the list edit character by character.

| Reachable states | Format probes | Failures | Over-wide expectations rejected | Under-wide expectations rejected |
|---:|---:|---:|---:|---:|
| 682 | 53,784 | 0 | 17,784 of 17,784 | 17,784 |

The two companions show the comparison can fail: an expectation that marks
one character beyond the range, or leaves one selected character as it was,
is rejected on every probe where the range leaves room for it. Formatting
exactness therefore holds on the pinned version, on created and on opened
replicas alike; the Notion demo's N-002 and N-003 have no Yjs analogue,
since Yjs resolves a visible range directly to the characters it displays.

Onset counts over the seven formatting runs, that is trials whose earliest
failing version falls in the class: Y-001 38, Y-002 9, Y-003 81, Y-004 100,
Y-005 53, and 5 first reported as unclassified, all in the partial-delivery
runs: four are Y-007, and one is Y-006, the opened-document family, reached through
a view failure rather than the determinism check. Formatting exactness
held: 2,301 format requests, no
disagreement with the list edit. Determinism failures, 53 over the seven
runs, are Y-006, the opened-document family, and the one local-meaning failure is
that family too: a delete at an opened replica with no concurrent operation
formats its neighbour. Partial delivery with formatting shows the same
classes and nothing new.

## Mechanisms

Yjs keeps formatting as marker items interleaved with the characters. A
left-to-right walk carries a current attribute map; a live marker sets or
clears a key; characters take the map; deleted markers are skipped. Two
properties of the operations that maintain these markers account for the
classes above.

**A format's extent depends on markers it does not own.** `formatText`
deletes every live marker of its key inside its range. When it meets an
existing opening marker of the value it is setting, it forgets that it owes a
closing marker and relies on whatever closed the existing span. A concurrent
operation that deletes that closer, which an unbold of an overlapping range
does, leaves the new opening marker unclosed and the formatting runs to the
end of the text. No sequential order produces that document.

**Cleanup judges markers by position, not by span.** After deletions and
remote formatting, `cleanupFormattingGap` deletes markers it finds redundant
in a left-to-right pass, without knowing which opening marker a closer
belongs to. An opening marker that sorts after a concurrent one of equal
value is deleted as overwritten although the concurrent span closes earlier;
a deletion adjacent to a span can remove the span's closer.

**Delete sets bypass causal buffering.** An update that arrives before an
update it causally follows is held back only while a struct it contains
lacks its clock predecessor or an origin. A delete set is applied as soon as
the ids it names exist. A format that only removes markers is a delete set,
so it takes effect at a replica that has not yet received the insertion of
the format's own endpoint, and an insertion issued after an unbold takes
effect at a replica that has not received the unbold and so lands inside a
still-live span. In plain text the same gaps are invisible, because deleted
characters still anchor insertions and the witness search admits the view;
with formatting the replica shows a document that no causally closed version
has. Full synchronisation then converges.

**Opened documents are edited with a disabled code path.** A text type
obtained after the document state was applied has `_hasFormatting` unset and
its index cache enabled, which the source marks unsupported for rich text.
Deletions on such a replica compute attributes from the cache and can delete
a closing marker, so deleting a plain character formats its neighbour, and
the post-transaction cleanup never runs there. The same request on the same
display therefore gives different results on a replica that created the
formatting and one that opened the document.

## Other versions

The pinned version is 13.6.31. The release after it, 13.6.33, changes no
text, formatting or delete-set code, and every result above repeats on it
with the same per-trial outputs. The 14.0.0 release candidate (rc.29,
published as the package `@y/y`) is a rewrite with one node type, and on
it Y-001 to Y-005 and Y-007 persist, since `formatText`, the two cleanup
passes and `readAndApplyDeleteSet` keep the 13.x logic; Y-006 is gone,
because the decoder and the application now share one node object and
every edit walks from the start of the type. The candidate also integrates
a struct past a clock gap of its own client, filling the gap with a `Skip`
when the struct's origins exist, where 13.x held the struct pending. A
replica then shows an insert without the text its author had typed before
it, a plain-text form of the Y-007 condition; `experiments/yjs-oracle/repro/`
holds one plain-Yjs script per class, run on all three versions, with
this case as Y-008.

## Relation to prior reports

The Peritext paper (CSCW 2022, section 2.3.2) describes the first mechanism
for the 2016 `y-richtext`, with an unbold of a whole range concurrent with an
unbold of a sub-range; it did not test the current text type. Yjs issues
#382 (overlapping formats of the same key lose a span) and #385 (formatting
reaches concurrently inserted text) are open reports of two of the classes.
Y-001 to Y-003 were reported upstream on 2026-10-29 as one issue with the
three plain-Yjs scripts, yjs/yjs#828, and the scripts for Y-004 and Y-005
were added as comments on #385 and #382 with a pointer to the common cause.
Y-007 and Y-008 were reported the same day as yjs/yjs#829, framed as a
question about intermediate states, since the documentation promises only
convergence once every update has arrived. Before these reports, the opened-document family (Y-006), the delete-set
class (Y-007) and the marker-ownership shape (Y-001) on the current text
type had no public report that the sweep found. The only machine-checked
work on Yjs, `lean-yjs`, covers the list algorithm and not formatting.

## Lean counterparts

Counterparts are written where a disagreement exposes a semantic
distinction, and once per distinction.

- `Sal/MRDTs/Instances/YjsMarkerCounterexample.lean` renders the measured
  marker lists of the marker-ownership case (Y-001) and proves that the
  merged document differs from both sequential outcomes, and that supplying
  the missing closer restores one of them. The distinction is between
  formatting as marker items rendered by a walk and formatting as marks on
  characters; Y-002 to Y-005 differ from Y-001 only in which operation
  removes or misplaces a marker, so they share this counterpart.
- `Sal/MRDTs/Instances/YjsDeleteSetCounterexample.lean` covers Y-007, a
  different distinction: which received updates count as integrated. It
  renders the version that holds an unbold's delete set without the
  insertion of the unbold's endpoint, proves it differs from every causally
  closed version, models the delivery rule that admits a delete-set-only
  update whose predecessor is absent, and shows the view is the closed one
  once the missing insertion arrives.
- The opened-document family (Y-006) has no counterpart. The same request on the
  same document gives two results because of an internal flag of the text
  type, not because of a different meaning; `opened-document.mjs` and facts
  i to k are its evidence.

Both modules are semantic counterparts of measured executions, not models
of Yjs's integration algorithm.

## Limits

The search is finite and bounded: histories of twelve requests over two or
three replicas, witness search on at most twelve edits per version, single
lowercase characters, bold and italic only. It covers the text type's
`insert`, `delete` and `format`; arrays, maps, embeds, the undo manager and
editor bindings are outside it. Omitted-attribute inserts are measured as
facts but excluded from the search, since the specification gives inserted
text exactly its own attributes. The results are measured on the pinned
version, and the release notes of 13.6.32 and 13.6.33 list no formatting
change, but no later version was run. Nothing here concerns Yjs's list
algorithm, which passed every check in this search.

## Reproduce

```sh
cd experiments/yjs-oracle
(cd ../../ra-pbt/instances/yjs && npm install --ignore-scripts)
node ../../ra-pbt/instances/yjs/verify-sources.js
node spec-tests.mjs
node facts.mjs
node run.mjs --mode regressions
node formatting-exactness.mjs --seed 41 --trials 60
node run.mjs --mode search --seed 11 --trials 200 --format --opened false --output results/search-11.json
```

See `experiments/yjs-oracle/README.md` and `README-search.md`.
