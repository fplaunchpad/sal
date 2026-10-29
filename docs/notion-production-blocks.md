# The production Notion block layer through ra-pbt

## Question, claims and falsifiers

The public Notion demo had five catalogued defects, N-001 to N-005
([notion-bugs.md](notion-bugs.md)). All five were in issuing and replaying
split, merge and bold requests, not in merge, and ra-pbt detects each
([notion-ra-pbt.md](notion-ra-pbt.md)). The editing code shipped in
production Notion clients builds those requests differently: splitting
gathers the following slice-tree siblings, merging appends to the target's
last slice, and the shared move handler places a split's new block after the
block that actually holds the moved text. Replays of the five demo schedules
through the production request builders did not reproduce any of them
(`experiments/notion-production-client` in the main tree). Those replays
tried only the demo's schedules.

**Question.** Does the block layer of the production editing code
(creating blocks, splitting a block, merging a block into its predecessor,
with insertion and bold inside blocks) meet the obligations whose violations
exposed the demo's defects? If not, what failure classes do the production
builders have of their own?

The claims and their falsifiers were stated before any run:

| Claim | Statement | Falsifier |
| --- | --- | --- |
| B1 | Under causal delivery, replicas converge for arbitrary interleavings of create, split, merge, insert and bold | Replicas holding the same records with different displays |
| B2 | Every version is RA-linearizable under a block specification of the demo instance's shape, with identities from the operations | A version with no witness |
| B3 | A request's local effect is the one given by `positional-spec.mjs` | A local-meaning disagreement |
| B4 | After the final sync, the characters present are exactly those inserted (none are deleted at this layer) | A lost or duplicated character |
| B5 | A replica opened from a snapshot and one built by replaying records issue a request alike | A created/opened disagreement |

Prediction for the demo schedules, also stated before running: N-001 to
N-005, re-expressed as positional schedules through this instance, pass
every check, as the replays found.

## Answer

None of B1, B2 and B4 holds. B3 and B5 hold, apart from one specification
reading and one artefact of the harness. The prediction for the demo
schedules is refuted for N-002 and N-003. Their requests now have the
contracted local effect, but after the final sync the bold record is
rejected at the other replica, and the replicas diverge.

Six defect classes of the production code were found, none of them the
demo's. Two are rejections of a causally ready record by the shipped
handlers: an operation names a slice by a search label that depends on the
order in which the replica applied concurrent splits (**label-divergence**),
or the new item of a split or insertion is ordered past the end of its
origin's slice by a concurrent merge's marker (**past-boundary**). One is a
non-convergence without any rejection: two concurrent splits move the same
slice, and the move applied last wins (**concurrent-move**). Three are
RA-linearizability failures with no lost text. A late duplicate merge moves
the text of an already removed block again (**stale-merge**). A block listed
after a removed block goes to the end of the page (**removed-anchor**).
Block order follows application order while text division follows
identifiers (**order-mismatch**). Each defect class shows on one replica
that applied causally ordered records. A sequencing server that received
those records in that order would therefore show it too. Only the
non-convergence of block order (`list-order`) depends on peer-to-peer
delivery.

## The library and its verification

Notion's code is proprietary. Nothing of it is in this repository. The
instance executes an export produced outside the repository and named by
the environment variable `NOTION_PRODUCTION_LIBRARY`:

1. `download.py` of `experiments/notion-production-client` (main tree)
   fetched the 63 public application assets listed in its `sources.json`
   (9,006,862 bytes, recorded 29 October 2026) and checked each length and
   SHA-256.
2. `NOTION_PRODUCTION_CACHE=<cache> npm test` there passed its 19
   extraction and replay controls.
3. `extract.mjs <cache> <export>` wrote the standalone library: 4,335 module
   bodies as verbatim source slices (`modules.json`), the runtime and record
   adapter (`index.mjs`, `client.mjs`, `runtime.mjs`, `requests.mjs`) and
   the asset manifest.

`ra-pbt/instances/notion-production-blocks/verify-sources.js` checks the
export against [library.json](../ra-pbt/instances/notion-production-blocks/library.json).
It checks the length and SHA-256 of the six exported files, the module
count, and the digests and source positions of the eight modules the
findings name: 701590 (split and merge request builders), 971340 (record
operations), 300957 (slice tree), 458789 (text slice), 121141 (slice lookup
by label), 663360 (label subdivision), 929891 (list commands) and 75332
(list placement). It refuses a library located inside the repository.
Every runner (`campaign.mjs`, `regressions.mjs`, `run.mjs`) verifies the
library before it loads it and again after the run.

| Exported file | Bytes | SHA-256 |
| --- | --- | --- |
| `modules.json` | 9,379,972 | `8ecc246d0707254baf0f8230c271cdee125819377d96f9fe1f92a85463771bc8` |
| `client.mjs` | 4,064 | `564729b916d7344ef4024d20311e38f6e9620d65705c36c70b26cd3d72660892` |
| `runtime.mjs` | 3,158 | `d88b5eab5387afe9fe1e0e52caeed5eb89f57d2094d07f6bc42b716589106303` |
| `requests.mjs` | 1,792 | `7a319d594ecc3b9a8c04a21c80e4820309eb1babaab66eb0553d0ac10bddab18` |
| `index.mjs` | 436 | `d48d9dcce273cc7d88d26bec22d666403d1c346860858c181ee39a2797de02df` |
| `sources.json` | 14,336 | `6c31e32d25cc102d61de01e4b4476bab7cc456c2686d86e106d2ab92adb097be` |

## The instance

`ra-pbt/instances/notion-production-blocks/`.

**Document and requests** (`adapter.js`). One page block whose `content`
lists the blocks, as in the main tree's `ReplayReplica`. A block is created
with the shipped empty-tree constructor, sent as a `set` of its value with
`parent_id` the page, and listed by `listAfter` on the page's content. The
display is the page's content filtered by `alive`, with each block's
characters read by the shipped slice-tree iterators and readers. The five
requests, each one record:

| Request | Operations |
| --- | --- |
| `create after` | `set` + `listAfter` (the harness's block creation) |
| `insert block index text` | the shipped insertion builder (`prepareInsert`) |
| `split block index` | creation of the new block after the source, then the original split builder (`RequestBuilder.split`, 701590) |
| `merge block` | the original merge builder (`RequestBuilder.merge`), then `set alive false` and `listRemove` (the harness's removal) |
| `bold block start end` | the shipped annotation builder, adding unless every selected character is bold |

Every operation is applied by the shipped record handlers (971340), locally
and on receipt. A record carries its operations and the keys of every record
its issuer held. A receiver holds it until that past is present, then
applies it once. An application that throws is undone from the snapshot
before it. The record stays unintegrated, so the replica stays pending.
Replica r has session `A`, `B`, ...; an opened replica is a client
constructed from the source's `RecordMap` snapshot.

**Clocks.** The library's `ProductionClient.tree` reads a block through the
record model (500183), which parses the slice tree with one plain clock per
tree. The editor's record store (970831), whose trees the request builders
receive in the application, parses it with clock holders of class
`997076.W`. These are backed by a per-process map from text instance to the
largest counter seen or reserved. The adapter parses trees the record
store's way (266858 with `997076.W` holders) and gives each client its own
map. With the record-model clocks, one session's splits in different blocks
of one text instance allocate the same marker identifier. Even a sequential
single-replica history then goes wrong (the `duplicate-marker` control
below).

**Runtime.** Every library client is a VM context with its own compiled
modules, too heavy for a search that forks two replicas before every edit.
Clients share one runtime per loaded library, built by the body of the
`ProductionClient` constructor. A regression checks that shared and isolated
runtimes give identical displays and verdicts on four schedules.

**Specification** (`spec.js`). That of the demo instance: the
identity-addressed block document of
`experiments/notion-merge-design/identity-spec.mjs` in its `sliceFollow`
merge meaning, with the demo instance's `bold` and `mark` commands
(`FormattedIdentitySpec`, imported). Blocks form an ordered list, each alive
or a tombstone, holding slots with addresses `instance/item`. `create` puts a
new block after a given one. `insert` places characters after their origin
slot wherever it now is. `split` moves the slots after its origin, headed by
its marker, into the new block. `merge` appends the source's slots to the
block holding the anchor's end slot and tombstones the source, unless the
source is already a tombstone or is that block. `bold` sets the flags of
exactly the selected characters. A record's operations decode
(`decode.js`) into one atomic command group with the identities the
production code assigned. Differences from the demo instance, each forced by
the production operations or behaviour:

1. `splitAt instance start target`. When a split index is the end of a
   slice-tree node, the builder emits no split operation, only a move of the
   following slice, which starts at an existing marker (`splitNodeEnd`).
   The command moves the slots from that marker to the end of their block.
2. `insert` carries a bold flag. Inserted characters take the flag of the
   nearest visible character before them in their block, in the state the
   insertion is applied to (reading `inherit: 'apply'`). This is the
   production editor's inheritance rule. The demo instance avoided the
   question by issuing no insertion in its formatted profile.
3. A split's new block follows the block that holds the split point
   (reading `splitPlacement: 'holder'`), as `moveTextSliceIntoBlock` places
   it. The demo instance's reading (`'source'`) leaves it after the block the
   issuer split, which may be a tombstone.
4. The local meaning is `positional-spec.mjs`'s `request`, extended by
   `create` and by the inheritance rule of (2).
5. The initial state is the fold of the seed's decoded command groups.

Fifteen hand-derived tests with companions cover the commands, both
readings of (2) and (3), atomicity, stuck histories, the local meaning and
the decoder ([spec.test.js](../ra-pbt/instances/notion-production-blocks/spec.test.js)).
Views compare block texts in order, and in the `format` and `mixed`
profiles each character's bold flag.

**Profiles** (`requests.js`). `structure`: split, merge. `blocks`: create,
split, merge, insert. `format`: split, merge, bold. `mixed`: all five.

**Classification** (`classify.js`). A failure is named by re-executing its
schedule with an observer that reports every issued and applied record,
with the whole document before and after: block records, alive flags,
visible characters, and every slice with its label and items. The
classifier never decides a failure. The evidence and the class definitions
are in the file's header; the classes are described below.

## Results

Node 26.3.1. Fifteen configurations, each with three campaign seeds of 100
trials: 4,500 generated trials in all, every check of ra-pbt after every
step and after the final sync, witness bound 12 edits (no version exceeded
it). The first twelve configurations use the default readings; the last
three change one reading or the harness, to measure artefacts. Every count
is in [results/](../experiments/notion-production-blocks/results/):
`campaign.json` per configuration, `summary.json` per class with the shrunk
representative, `regressions.json` for the declared cases (35, all holding).

| Configuration | Profile | Seed | Delivery | Replicas | Failing trials | With a rejected record | Convergence | RA-lin | Local meaning | Determinism | Conservation |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| abc-blocks3-structure | structure | `a \| b \| c` | sends | 2 | 107 | 95 | 89 | 14 | 0 | 0 | 95 |
| abc-blocks3-structure-r3 | structure | `a \| b \| c` | sends | 3 | 152 | 138 | 137 | 25 | 0 | 0 | 138 |
| abc-structure | structure | `abc` | sends | 2-3 | 238 | 238 | 219 | 1 | 0 | 0 | 238 |
| x-structure | structure | `x` | sends | 2 | 250 | 250 | 211 | 0 | 0 | 0 | 250 |
| ab-cd-blocks | blocks | `ab \| cd` | sends | 2-3 | 152 | 96 | 148 | 13 | 0 | 0 | 96 |
| ab-cd-blocks-exchange | blocks | `ab \| cd` | whole state | 2-3 | 180 | 114 | 175 | 26 | 0 | 0 | 114 |
| a-blocks-exchange | blocks | `a` | whole state | 2-3 | 229 | 167 | 227 | 24 | 0 | 0 | 167 |
| ab-format | format | `ab` | sends | 2 | 127 | 127 | 111 | 0 | 0 | 0 | 127 |
| abc-format | format | `abc` | sends | 2 | 127 | 127 | 116 | 0 | 0 | 0 | 127 |
| ab-c-mixed | mixed | `ab \| c` | sends | 2-3 | 120 | 84 | 108 | 17 | 1 | 0 | 84 |
| ab-c-mixed-opened | mixed, opened replicas | `ab \| c` | sends | 2-3 | 81 | 43 | 74 | 14 | 4 | 0 | 43 |
| abc-blocks-opened-exchange | blocks, opened replicas | `abc` | whole state | 2-3 | 109 | 61 | 107 | 7 | 0 | 0 | 61 |
| ... with splitPlacement `source` | structure | `a \| b \| c` | sends | 2 | 119 | 95 | 89 | 32 | 0 | 0 | 95 |
| ... with inherit `issue` | mixed | `ab \| c` | sends | 2-3 | 153 | 84 | 108 | 72 | 1 | 0 | 84 |
| ... with record-model clocks | structure | `abc` | none | 1 | 114 | 0 | 0 | 103 | 51 | 0 | 4 |

Columns from "Convergence" on count failing trials (out of 300 per
configuration). "Sends" delivers single records, some held back until the
final sync; "whole state" syncs replicas pairwise. Trials of 8 to 12 steps.

In the twelve default configurations (3,600 trials, 27,846 edits, 49,536
versions checked for RA-linearizability, 27,846 determinism fork pairs),
1,872 trials fail. Trials per class (a trial counts once per check and
class), with the smallest shrunk trace:

| Class | Kind | Check | Trials | Smallest trace |
| --- | --- | --- | --- | --- |
| label-divergence | defect | convergence / conservation | 1,287 / 1,400 | 3 requests |
| past-boundary | defect | convergence / conservation | 133 / 137 | 3 requests |
| concurrent-move | defect | convergence | 1 | 4 requests |
| stale-merge | defect | RA-linearizability / convergence | 68 / 2 | 3 requests |
| removed-anchor | defect | RA-linearizability | 23 | 4 requests |
| order-mismatch | defect | RA-linearizability | 34 | 3 requests |
| RA-linearizability at a replica that also rejected a record | consequence of label-divergence or past-boundary | RA-linearizability | 25 + 6 | 5 requests |
| list-order | delivery-model artefact | convergence | 296 | 4 requests |
| format-carry, and the same carry under concurrency (bold-flags) | specification reading | local meaning / RA-linearizability | 5 / 13 | 3 requests |
| rejected, not explained by either criterion | unexplained | convergence, conservation / RA-linearizability | 3 / 1 | 5 requests |
| unclassified | unexplained | RA-linearizability | 4 | 7 requests |

The smallest traces come from the regressions where those are smaller than
the campaign's shrunk representative; the shrinker's results are minimal
under its reductions, not globally. The three alternative configurations add
`removed-anchor` and `order-mismatch` failures under `splitPlacement:
'source'`, 53 `bold-flags` trials under `inherit: 'issue'`, and 103
`duplicate-marker` trials with record-model clocks. None appears in the
default configurations.

### Verdicts on the claims

| Claim | Verdict | Falsified by |
| --- | --- | --- |
| B1 convergence | refuted | label-divergence and past-boundary (a rejected record is never integrated, and later records that depend on it are held for good); concurrent-move; stale-merge (2 trials); list-order (artefact of peer-to-peer delivery) |
| B2 RA-linearizability | refuted | stale-merge, removed-anchor, order-mismatch; a further 4 trials unclassified |
| B3 local meaning | holds, except for one reading | 5 format-carry trials out of 27,846 checked edits, all insertions directly after a split at the end of bold text; under the record-model clocks (harness artefact) 51 trials |
| B4 conservation | refuted, through rejections only | every conservation failure in the default configurations has a rejected record; no trial hides or duplicates a character at a replica that integrated every record |
| B5 determinism | holds | 34,778 fork pairs, no disagreement, including opened replicas |

The remaining residue is four trials with rejections and four
RA-linearizability failures. The rejections carry the past-boundary message
(`Failed to find target text slice after backfilling`) after concurrent
splits at 0 with insertions at 0, where the boundary marker was already
known to the issuer, so the structural criterion does not claim them. The
RA-linearizability failures order two concurrent insertions after one
character differently from every admitted view, at a block that a merge
and a split concurrently restructured. Their shrunk traces are in
`summary.json`.

## Defect classes

Each class has a declared regression with a control that changes one
ingredient ([regressions.mjs](../experiments/notion-production-blocks/regressions.mjs)),
and a self-contained reproduction that imports only the library
([repro/](../experiments/notion-production-blocks/repro/README.md)).

### label-divergence

**Minimal trace** (seed `abc`, 3 requests). A splits at 1; B splits at 2; A
types X at 0 of block 1; exchange. Expected at both replicas: `a | Xb | c`.
Observed: A `a | Xb | c`, B `a | b | c`. B rejects A's insertion with
`Cannot backfill prev item that is not a text item`. Control: B receives A's
split before splitting, and both show `a | Xb | c`.

**Mechanism.** Each slice of a text instance has a search label. Every split
replaces the split slice's label `L` by two child labels in a binary
subdivision (458789 `updateSearchLabelAfterSplit`, using 663360). A
receiver locates an operation's slices by label: it applies a text
operation only within the slices whose labels lie in the range of the
operation's label, that label and its descendants (121141, function `TA`).
Labels are therefore a function of the order in which a replica applied the
splits of an instance, not of the set of splits. In the trace, A's slice
`[A:4 b]` is `d` at A and `T` at B, and at B the label `l` names B's slice
`[B:4 c end]`. The insertion is addressed to `l` with origin `A:4`, which no
slice in that range holds at B. The same happens to splits, merges and
annotations (`splitTextSliceResult must exist`, `Unable to apply annotation
operation due to start missing`, `Insertion origin not found in text slice`).
Once labels differ they stay different, and every later operation addressed
to the affected slices can fail. A sequencing replica that applies B's split
before A's rejects A's insertion in the same way (regression `label-divergence
at a sequencing replica`).

**Detected by** convergence and conservation (the record is never
integrated). Within the class, the classifier requires an addressed item that
lies within the label's range at the issuer and outside it at the receiver.

### past-boundary

**Minimal trace** (seed `a | b | c`, 3 requests). A splits b at 0 twice; B
merges b into a; exchange. Expected at both: `a | empty | b | c`. Observed:
A `a | empty | b | c`, B `a | b | c`. B rejects A's second split with
`splitTextSliceResult must exist`. Control: one split, and both show
`a | b | c`.

**Mechanism.** A split inserts a marker item after its origin
(300957 `getOperationsForSplitAtIndex`). A merge first splits the source at
its start with a marker reserved 20 ticks ahead
(`getOperationsForSplitForMerge`, `reserveTicks(20)`). Concurrent markers
after one origin are ordered by identifier. At B, b's start is followed by
B's merge marker `B:22`, which ends the slice that holds the origin. A's
second marker `A:3` sorts after `B:22`, so its integration point lies past
the end of that slice, and the handler finds no split result. The label
range covers the origin, so this is a different mechanism from
label-divergence. The same rejection hits a merge's own split when two
replicas merge one block concurrently and both markers reserve the same
counter (regression `past-boundary in a merge`; only conservation fails,
because the rejected merge moves an empty slice). An insertion at a block's
start concurrent with a merge of that block is rejected the same way (seed
`ab | cd`: A splits cd at 0 and types T into the emptied block, B merges cd
into ab; B rejects T with `Failed to find target text slice after
backfilling`; regression `past-boundary for an insertion`).

### concurrent-move

**Minimal trace** (seed `a | b | c`, 4 requests). B merges b into a, and A
receives it. B splits `ab` at 1 and merges the new block back. Concurrently
A splits `ab` at 1. After the exchange A shows `ab | empty | c` and B shows
`a | b | c`. No record is rejected, and every version at each replica is
RA-linearizable. Controls: B does not merge back (both `a | empty | b | c`);
A sees B's records before splitting (both `a | b | c`).

**Mechanism.** Index 1 of `ab` is the end of a's root node, so both splits
are `splitNodeEnd`. Each emits only `moveTextSliceIntoBlock` of the slice
that starts at B's merge marker, into its own new block (300957, 701590).
The move handler moves that slice from wherever it now is (971340). At A,
A's move runs first and B's second, then B's merge returns b to a. At B, B's
move and merge run first, and A's move arrives last and takes b into A's
block. The move applied last wins, and nothing orders the two moves.

### stale-merge

**Minimal trace** (seed `a | b | c`, 3 requests). A merges c into b; B also
merges c into b and then splits `bc` at 1; exchange. In every order of the
three requests the second merge of c finds c a tombstone and does nothing:
admitted = { `a | b | c` }. Observed at both: `a | bc | empty`. Control: B
does not merge c itself (both `a | b | c`).

**Mechanism.** A merge's operations are a split of the source at its start
and a move of the resulting slice, named by its start item, under the
target's last slice (701590 `LT`). The move handler locates the source slice
by identifier wherever it is. It proceeds when the source block is already
removed (971340 tags the span `merge_from_deleted_block` and continues). At
B, A's merge arrives after B removed c and split c's text into a new block.
It splits c's instance again and moves the slice now holding c back under
b. The text survives; the later split is undone. The same mechanism moves
empty fragments of a removed block. A later split at the end of the block
can then move only such a fragment, which the searches also report under this
class.

### removed-anchor

**Minimal trace** (seed `ab | cd`, 4 requests). A splits cd at 0 and merges
the empty block into ab (`ab | cd`). B splits cd at 0 and creates a block
after its block 1 (the original cd block). At A: `ab | empty | cd | empty`.
Admitted: { `ab | empty | empty | cd` }. Control: A does not merge.

**Mechanism.** `listAfter` with an anchor that is no longer in the list
appends at the end (929891, through 75332 `Te`). `moveTextSliceIntoBlock` repositions a split's
block after the block holding the moved text only when that block is alive
(971340). Both of B's blocks name the merged block as their anchor, so at A
they go to the end of the page.

### order-mismatch

**Minimal trace** (seed `a`, 3 requests). A creates a block after block 0
and types Y at 0 of block 0; B splits block 0 at 0; A's records reach B. B
shows `empty | empty | Ya`. Admitted: { `empty | Ya | empty`,
`Y | empty | a`, `Y | a | empty` }. Control: A sees the split first.

**Mechanism.** The page's content is an array: a block listed after another
lands immediately after it when the operation is applied. Text items
concurrent at one origin are ordered by identifier. At B, Y sorts after the
split marker and lands in the split's block, which needs the insertion
before the split. A's block, listed when it arrives, precedes the split's
block, which needs the split before the creation. A created the block
before typing. No order satisfies all three. Every block's content is
explained; only the order of the blocks is not. The class does not depend
on the placement reading: the trace fails under both `holder` and `source`.

## Artefacts and readings

| Name | Kind | Trace | Effect | Status |
| --- | --- | --- | --- | --- |
| list-order | delivery model | concurrent `create after 0` at two replicas, each typing into its block | A `a \| Y \| X`, B `a \| X \| Y`; each display is a linearization; only convergence fails | The page's content is an array edited by `listAfter`; Notion orders record lists at its server. Not counted as a defect |
| split placement | specification reading | A splits b at 0; B merges b into a and splits `ab` at 2 | `a \| b \| empty \| c` | Admitted under `holder`, the default; refuted under `source` (the demo reading). In the searches, the `removed-anchor` and `order-mismatch` failures found under `source` and absent under `holder` are of this kind |
| inheritance | specification reading | A types V after c; B bolds c | `ab \| [c][V]`: the mark extends over the concurrent insertion at its right boundary | Admitted under `apply`, the default; refuted under `issue` (class `bold-flags`). Text-layer behaviour |
| format-carry | specification reading | Bold c, split after it, type X in the new block | `[X]` bold: inserted text takes the formatting that precedes it in the text instance, across the block boundary | Local meaning and RA-linearizability fail against the positional contract (plain X). Editors commonly carry formatting over Enter; the contract does not say so |
| duplicate-marker | harness | Sequential: split `abc` at 2, block 1 at 0, block 0 at 1, merge block 3 | `ac \| b \| empty` instead of `a \| b \| c` | Only with the library's record-model clocks (`liveClock: false`); the editor's per-instance clocks give the contracted result |

## The demo catalogue on the production path

The five demo schedules, re-expressed exactly as the demo instance's
positional schedules (`experiments/notion-ra-pbt/regressions.mjs`), with
predicted and observed verdicts:

| Case | Demo defect | Production display at the critical step | Predicted | Observed | Detecting properties |
| --- | --- | --- | --- | --- | --- |
| N-001 | split at 0 moves only a subtree (`empty \| X \| a`) | `empty \| Xa`, split gives `empty \| empty \| Xa` | pass | pass | none |
| N-001, six requests | the same (`empty \| b \| a`) | `empty \| ab` (the demo's own layout), split gives `empty \| empty \| ab` | pass | pass | none |
| N-002 | bold changes neither character of `ba` | `empty \| ab`, bold gives `empty \| [a][b]` | pass | fail: the bold is rejected at the other replica, which shows `empty \| ab` | convergence, conservation (label-divergence) |
| N-003 | bold reaches a character in another block | `ab \| c`, bold gives `[a][b] \| c` | pass | fail: as N-002, other replica `ab \| c` | convergence, conservation (label-divergence) |
| N-004 | merge into a removed block hides the document | `a \| bc` (demo: `empty \| abc`), final `abc` | pass | pass | none |
| N-005 | delayed merge hides x | `empty \| x \| empty` (demo: `empty \| empty \| x`), final `empty \| x` | pass | pass | none |

On N-001 and N-004 to N-005 the production builders avoid the demo's defects
on the same requests. On N-002 and N-003 they avoid the demo's defects too.
The two concurrent splits of one block that the schedules need are exactly
what makes the replicas' labels diverge, and the bold, issued at one replica
against its labels, is rejected at the other. The replays in the main tree
compared local effects and the seed text, not convergence after a complete
exchange, so they could not see this. Control: when B receives A's split
before splitting, N-002 converges on `empty | [a][b]`.

## Scope

- The operations come from the original request builders and the shipped
  handlers. Block creation and removal, record transport and the fixture
  stores are the harness's. The merge's removal (`set alive false`,
  `listRemove`) is not conditioned on the move having happened, as in the
  demo. No class found here depends on that, and the N-005 schedule, whose
  demo failure came from it, keeps its text.
- Records are applied with the shared record handlers (971340). The live
  client applies its own optimistic operations through a separate path
  (946729, with an in-memory record cache), and receives server state as
  record values. Neither is exercised.
- Delivery is causal and peer to peer. Each defect class shows at one
  replica that applied causally ordered records, so a sequencing server
  receiving them in that order would show the same. What a live client then
  does with a rejected transaction is outside the experiment. The
  `list-order` artefact needs replicas that apply list operations in
  different orders.
- These are findings about the extracted editing code under this harness,
  not observations of the live service.

## Library gaps

`ra-pbt/src` is unchanged; each gap is worked around in the instance or
the runners.

1. `runCampaign` keys shrunk representatives by check and record kinds, so
   all the classes here (all `merge+split`) would collapse. The campaign
   groups by (check, class) and shrinks with a class-preserving predicate, as
   the demo campaign does.
2. A check failure carries no record-level evidence. The executor's steps
   (a `deliver` applies many records) are coarser than the mechanisms. The
   adapter takes an observer, and the classifier re-executes the schedule
   with it.
3. `conservation` has no initial state. The adapter reports the seed's
   characters as inserted by every record.
4. Convergence compares whole displays and cannot discount block order,
   which this layer's delivery model leaves unordered. Classification
   separates `list-order`.
5. `localMeaning` compares the whole display. The specification therefore
   fixes the inheritance of bold on insertion explicitly rather than leaving
   it unspecified.
6. The determinism check forks two replicas before every edit. With one VM
   context per production client this exhausts memory. The shared runtime
   avoids it.
7. The exported library has no slice or label inspection, no block creation
   or removal, and its `tree` uses record-model clocks. The instance reads
   slices from serialised values, creates and removes blocks with record
   commands, and parses trees with the editor's clocks.

## Open questions

- **Addressing by derived names.** Label-divergence and past-boundary
  share a cause: an operation addresses state by a name (a search label, an
  integration point among siblings) that each replica derives from the
  order it applied concurrent splits, not from the operations. Hypothesis: if
  labels were a function of the split markers' identifiers, both rejection
  classes would disappear and no new class would appear. A patched variant,
  as the demo's corrected merge was, would test it.
- **Moves without an order.** Concurrent-move and stale-merge are both moves
  of a slice named by identity, applied wherever the slice is, with the last
  applied winning and no check that the source block is still the one
  intended. Is a replicated tree-move discipline (undo, apply, redo in a
  global timestamp order) enough here, and does it keep RA-linearizability
  under the block specification?
- **Composition.** Order-mismatch is a failure of composition. The text,
  ordered by identifiers, and the block list, ordered by application, are
  each explicable, but no single order explains both. Which placement rule
  for the list (for instance, ties broken by the same identifiers) makes the
  product of the two RA-linearizable?

## Reproduce

From the repository root, with Node 26 and Python 3. The export must live
outside the repository.

```sh
P=/Users/kc/repos/sal/experiments/notion-production-client   # the production-client tree (main repository)
npm ci --prefix $P --ignore-scripts
python3 $P/download.py --cache /tmp/notion-production-sources
NOTION_PRODUCTION_CACHE=/tmp/notion-production-sources npm test --prefix $P   # 19/19
node $P/extract.mjs /tmp/notion-production-sources /tmp/notion-production-library
export NOTION_PRODUCTION_LIBRARY=/tmp/notion-production-library
node ra-pbt/instances/notion-production-blocks/verify-sources.js
node --test ra-pbt/instances/notion-production-blocks/spec.test.js        # 15/15
cd experiments/notion-production-blocks
node regressions.mjs              # results/regressions.json; exit 0 when every case holds
node campaign.mjs                 # results/campaign.json, results/summary.json; --quick for a smoke run
node run.mjs --texts '["a","b","c"]' --profile structure --partial --replicas 2 --trials 100 --shrink
for f in repro/*.mjs; do node "$f"; done
cd ../../ra-pbt && npm test       # 48/48
```

`verify-sources.js` pins the export used for the results above. A different
export, for instance after a change to the production-client harness files,
fails verification.
