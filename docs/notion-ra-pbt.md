# The Notion block editor through ra-pbt

## Claim and falsifier

**Claim.** Each defect in the Notion catalogue (N-001 to N-005,
[notion-bugs.md](notion-bugs.md)) is detected by at least one ra-pbt
property, and the property that detects it names the obligation of the
tested contract that the defect violates. The generic end-to-end witness
check is causal-history conformance, not a verdict on the paper's full RA
criterion; connecting it to a paper obligation requires a separate argument.

**Falsifier.** A catalogued defect that no property detects, or a property
failing on the corrected model where the existing experiments say the
corrected model is correct.

The source campaign stated its detection claim and falsifier before the
runs below; this review narrows the generic check's interpretation to its
actual causal-history criterion. The corrected model is expected to
fail N-002 and N-003, because the existing experiments report that the
corrected block merge leaves formatting unchanged and both bold failures
persist under it ([merge design gate](../experiments/notion-merge-design/README.md)).

## Model

The existing campaigns (`experiments/notion-oracle`, `notion-correctness`,
`notion-merge-design`) all execute the JavaScript of Notion's public demo:
the seven modules pinned by SHA-256 in
[sources.json](../experiments/notion-oracle/sources.json), fetched
separately and never committed. The corrected model is the `anchor-absorb`
variant of the merge design gate: the same modules patched by
[patch.py](../experiments/notion-merge-design/design-patch/patch.py), with one
`mergeBlock` operation anchored at the end of the target's last slice,
removal derived from attachment, and the source tree attached under the last
node of the holder tree. The Lean source model (`NotionCore*`) is not
executed by these campaigns and is not used here.

Here, "corrected model" means this older block-merge-only `anchor-absorb`
variant. It does not mean the newer repaired rich-text model on main, or
Notion's production client. The separately extracted production-bundle
experiments on main are outside this campaign's evidence.

The campaign counts below are historical output from source baseline
`14f073e`. They have not been regenerated on the integrated tree. The
law-layer commutation evaluator was corrected during review; historical law verdicts
and counts are pre-review candidates pending reruns. Review independently
hash-checked the cached demo, checked the two recorded repair hashes, and
re-ran all 34 declared regressions successfully.

`ra-pbt/instances/notion/prepare.js` downloads the pinned modules into
`$NOTION_RA_PBT_SOURCES/cache`, checks every hash, and writes each patch.py
variant to `$NOTION_RA_PBT_SOURCES/variants/<name>`; `sources.js` imports a
variant from there and refuses a demo whose hashes differ from the manifest.
The patched `anchor-absorb` modules used for the results hash to
`document.js` `bb3d773de012aa8f54a0274f787a068709f597133974bcb44e09652986225f8a` and `replica.js` `74e009a1b894db9dbd6967ad8764974f5586dc5665d4dfa8eb2e676287648857`
(the other five modules are unpatched).

## The instance

`ra-pbt/instances/notion/` exposes one model in both layers.

**End-to-end layer** (`adapter.js`, `spec.js`, `requests.js`). A replica is
the model's `Replica` with a fixed session per replica number, constructed
holding the seed document's transactions. Requests are positional
(`insert`, `delete`, `split`, `merge`, `bold` on a displayed block index),
each emitting one transaction. A record carries the transaction and the keys
of every transaction its issuer held; delivery holds a record until those
are present, then the replica receives it whole (the demo itself does not
buffer). Every check of ra-pbt runs:

| Check | Obligation it names |
| --- | --- |
| `raLinearizability` (legacy name) | causal-history conformance: some linearization of the supplied causal dependencies, folded through the identity specification, gives the display |
| `localMeaning` | local effect: the issuer's display after a request is the positional contract applied to its display before ([positional-spec.mjs](../experiments/notion-oracle/positional-spec.mjs)) |
| `conservation` | text conservation: after the final sync every replica shows exactly the seed and inserted characters that were never deleted |
| `convergence` | convergence: replicas holding the same transactions show the same display |
| `determinism` | a replica opened from stored transactions and one synced from empty issue the same request alike |

Current witness-check results carry `paperRaVerdict: 'not-checked'`. This
check preserves all supplied causal edges, including commuting ones, and
adds no concurrent implementation `rc` edges; its order can be incomparable
with the paper's `lo_E`. Neither verdict alone decides paper RA. Reporting
coverage also requires bound skips, partial-record skips and dependency
gaps; a checked slice with dropped dependencies is not a causally closed
paper-model version. The historical tables below retain the legacy API key.

The specification is the identity-addressed block document of
[identity-spec.mjs](../experiments/notion-merge-design/identity-spec.mjs),
imported unchanged, in its `sliceFollow` merge meaning, under which the
corrected merge agrees with all 162,373 archives of the merge design gate.
Two additions live in the instance. The formatted instance adds a command
`bold addresses value` that sets the bold flag of the characters the issuer
selected, with the value of an ordinary toggle on its own view; the adapter
derives it from the request and the issuer's display, not from the
annotation the model emits. The demo's merge transaction splits the source
at its start before moving it, and a later merge can be anchored at that
split's marker; the imported decoder gives the marker no position, so such a
merge is stuck. Following the specification's own rule for a split, the
instance decodes a demo merge to `mark` (the end slot `i/^m` and the marker
slot `i/m` immediately after the source's start slot) followed by the merge.
Views are compared on what a reader sees: the text of each block in order,
and in the formatted instance each character's bold flag. Whether inserted
text inherits bold is not specified by the positional contract, so the
formatted request profile issues no insertion.

**Law layer** (`laws.js`). The model's replicated state is its transaction
archive: `receive` adds a transaction to a map, and a document is rebuilt by
sorting and replaying the archive. As a state-based datatype, `apply` adds a
transaction, `merge3` is the union of the branches and `read` is the
display. Events are issued honestly by a model replica holding the canonical
state of its event set. rc is empty, since set insertion commutes;
commutativity is declared false so that `lo_E` is the visibility order and
the conformance witness is a causal linearization. The `bag` observation
reads only the multiset of visible characters, so sequential conformance
then detects a character multiset no admitted causal linearization explains.
It can also fail when the specification admits no linearization; that
decoder/specification failure must be distinguished from lost or duplicated text.

**Classification** (`classify.js`). A failure is named by reading the
model's state, separately from the checks: N-001 when a split's local effect
is wrong or a placement-only causal-history failure occurs in an archive
whose slice forest branches; N-002 and N-003 when a bold toggle misses
selected characters or changes others; N-004 and N-005 when a demo merge
whose anchored slice lies in a removed block, or in the source's own tree
(the cycle no-op), hides text.

## Results

Node v26, the pinned demo (`demo`) and the corrected merge
(`anchor-absorb`). End to end, per model: 14 search configurations (3,050
generated trials, 38,965 edits, 57,553 versions checked for
causal-history conformance, 6,759 versions above the witness bound of 12 edits
skipped), and 6 systematic configurations (342 prefixes); 17,060 probes in
all. Laws: 16 runs per model.
Every count is in `experiments/notion-ra-pbt/results/`.

### Per defect

"Size" is the number of requests (edits) in the smallest shrunk
counterexample of that class. "Existing" is the catalogue's trace.

| Defect | Detecting properties (layer) | Obligation violated | Size, search | Size, existing | Agrees with existing trace |
| --- | --- | --- | --- | --- | --- |
| N-001 | `localMeaning` (split), `raLinearizability` (end to end) | local effect of split; causal-history conformance | 5 (seed `ab \| cd`, 2 replicas) | 8 (7 setup requests over `a`, then the split); 7 in the six-request variant | yes: the same symptom and mechanism (duplicate concurrent merges of one block leave a branching slice tree, then a split moves only a subtree), on a shorter history. Both catalogue traces reproduce unchanged as regressions |
| N-002 | `localMeaning` (bold), `raLinearizability` (end to end, formatted) | local effect of bold; causal-history conformance | 4 | 4 | yes: request for request (split at 0 and at 1, one-way delivery, merge of the last block, bold of the merged block) |
| N-003 | `localMeaning` (bold), `raLinearizability` (end to end, formatted) | local effect of bold; causal-history conformance | 4 | 4 | yes: request for request |
| N-004 | `conservation`, `raLinearizability` (end to end); `specConformance` (laws, declared configuration) | text conservation; conformance under the tested specification order | 8, in a history that also takes the N-005 path | 5 | the catalogue trace: yes, reproduced as a regression on both layers. Search: no pure N-004 history, only one combined with N-005 |
| N-005 | `conservation`, `raLinearizability` (end to end); `specConformance` with the bag observation (laws) | text conservation; conformance under the tested specification order | 4 events (laws), 8 (end to end) | 4 | yes in the law layer: event for event (split at 1; split at 0; merge back of the split-off block; the delayed merge) |

The historical law campaign reported no failures of
`eventSetDeterminesState`, VC1 to VC5, `rcNonComm`, merge idempotence or
merge-init in 16 runs per model (60,000 reported non-vacuous evaluations
for most properties). It reported sequential-conformance failures on the
demo in 7 of 16 runs. These are pre-review candidate results, not discharged
verification conditions; the corrected evaluator must rerun them.

The law datatype's `merge3` unions transaction archives. That operation is
distinct from the editor's block-merge request. Passing union-carrier laws
does not establish correctness of that request or its replay. N-001 to N-003
have concrete issuance/replay failures; N-004 and N-005 occur during replay
of the demo's block-merge transaction, whose block removal runs whether or
not the move happened. In the recorded bounded end-to-end runs, convergence
and determinism reported no failures on either model: replicas can agree on
lost text.

### Corrected model

`anchor-absorb` fails only N-002 and N-003, and in the same way as the demo
(declared regressions, 1 random trial, 29 systematic probes). The existing experiments
report exactly this: the corrected block merge leaves formatting untouched.
No other end-to-end check failed in the recorded bounded trials and probes;
the historical law verdicts await evaluator reruns. In particular it passes
the declared N-001, N-004 and N-005 traces.
On the N-004 history its display before B's last merge is `a | bc`, as
the merge design gate reports. The falsifier is not met.

### Outside the catalogue

The search reports two further failure classes on the demo. Neither appears
on the corrected model.

- **A split after a concurrent merge of its block** (`split-after-removal`;
  3 events in the law layer, 3 requests end to end). From `a | b | c`, one
  replica merges `c` into `b` and splits that block; another concurrently
  merges `b` into `a`. In every linearization the split moves the text after
  `b`'s start slot, which the merge moved into `a`, giving `a | bc`. The demo
  creates the split's block at the front of the document, because its
  predecessor has left the display order, and moves no text: `empty | abc`.
  This is the precondition the catalogue's N-004 trace passes through. No
  text is lost, so only the causal-history check detects it. It is the order
  inversion the merge design gate counts for the demo (`design-order-splice`
  reproduces it), and it is not a catalogued bug.
- **The N-005 code path hiding an empty block** (`N-005-path`, 10 events, law
  layer). A merge whose move is the cycle no-op still removes its live
  source. Here the source is empty, so no character is lost, but the display
  has one block fewer than any linearization.

## Undetected defects

None. All five are detected by search and by declared regressions. Two
qualifications follow.

- N-004 was found by search only together with the N-005 path, in 40-step
  histories over `a | b | c`. Neither the law search (6,000 trials over
  `a | b | c`) nor the short end-to-end searches produced the pure five-request
  history. ra-pbt detects the catalogue trace as a declared case.
- N-002 and N-003 need two concurrent splits of one block, a one-way
  delivery, a merge and a bold selection of a specific range. Random
  generation reached N-002 in 1 trial out of 3,050 and N-003 in none, and
  probes from random schedules found neither. Both are found by the
  systematic stage (the directed suite of `notion-correctness` as ra-pbt
  schedules): 29 of its 4,290 formatted probes fail, on either model. The
  formatted law search found neither: its events come from the same random
  walk, and the law layer has no probes.

## Library gaps

Each is worked around inside the instance or the campaign. `ra-pbt/src` is
unchanged.

1. `runCampaign` keys shrunk representatives by check and record kinds, so
   distinct mechanisms with the same kinds (N-001, N-005 and the
   split-after-removal class are all `merge+split`) collapse into one. The
   campaign groups failures by (check, class) and calls `shrink` with a
   class-preserving predicate.
2. `runCampaign` always runs every check. The campaign calls `execute` with
   chosen checks for probes.
3. Generation is a random walk, with no way to probe every request at a
   reached state. Probes and the systematic stage are schedule extensions
   built in the campaign, so their failures are ordinary schedules and shrink.
4. `conservation` counts only elements inserted by records, with no initial
   state. The adapter reports the seed's characters as inserted by every
   record. A schedule without records would fail spuriously; none occurs.
5. A declared regression compares `displayed` with the specification's
   admitted views under one `viewKey`, and its controls run on the same
   instance. Views therefore drop identities, and controls on the other model
   are procedure cases.
6. The law layer evaluates properties only on generated configurations; no
   named property (for instance `specConformance`) can be checked on a given
   configuration. The law regressions use `evaluator` and `makeConfiguration`
   for the join lemma and the witness search for conformance.
7. The law shrinker preserves only the failure kind, and `runProperty`
   reports one failure per property. A conformance failure can shrink from
   one mechanism to another (text loss to split-after-removal), and a
   specification with no admitted extension shares the kind
   `no-admitted-linear-extension` with a disagreement (distinguished by
   `closestAdmitted` being null). The `bag` observation targets text loss.
8. `localMeaning` compares the whole display. It has no way to leave part
   unspecified (whether inserted text inherits bold), so the formatted
   profile issues no insertion.
9. With an empty rc on a carrier whose updates all commute, the paper's
   `lo_E` is empty, and conformance would admit non-causal orders. The
   instance declares commutativity false. For the same reason `specNonComm`
   would fail on both models by construction, as for RGA in the Sal runtime.
   It is not run (no `specCommutes`) and is not part of the claim.

## Modelling choices that bear on the verdicts

- The specification extends the imported one in two places: the `bold`
  command (the issuer's selection, from the request) and the `mark` command
  (the demo merge's split marker, under the specification's own split rule).
  Without `mark`, the demo's failures include histories the specification
  cannot interpret: review confirmed that the N-004 catalogue trace has no
  admitted linearization without this completion, whereas the completion
  admits block texts `abc` or `bca`. N-005 retains the admitted view
  `empty | x` with or without the completion. This completion is an explicit
  abstraction choice, not a proof of correspondence to the internal split.
- Selection-based `bold` matches the exact-selection contract of catalogue
  N-002 and N-003. Deriving expected coverage from the emitted annotation
  would conceal the selection-to-annotation defect. Merely dropping `bold`
  commands while retaining formatted observations is not an alternative
  contract: it can admit the unchanged N-002 view but cannot explain ordinary
  successful bold requests. Local meaning independently checks the selection.
- Views ignore block identities. Causal-history conformance is checked against what
  a reader sees: block texts in order, and bold flags.
- The classifier reads source state. It names failures; it never decides
  them.

## Reproduce

From the repository root, with Node and curl:

```sh
export NOTION_RA_PBT_SOURCES=/tmp/notion-ra-pbt-sources   # default: <os tmpdir>/notion-ra-pbt-sources
node ra-pbt/instances/notion/prepare.js                    # download, hash-check, write the variants
cd experiments/notion-ra-pbt
node regressions.mjs                                       # 34 declared cases; exit 0 when all hold
node campaign.mjs                                          # results/*.json (about 6 minutes); --quick for a smoke run
node run.mjs --mode laws --model demo --texts '["x"]' --observation bag --trials 2000 --size 8 --sync 0.4
node run.mjs --mode endtoend --model anchor-absorb --texts '["a","b","c"]' --trials 300 --steps 14 --partial
cd ../../ra-pbt && npm test                                # 48/48
```
