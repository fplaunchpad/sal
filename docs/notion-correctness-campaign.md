# Notion demo correctness campaign

## Research question

After concurrent block restructuring, do valid local editing requests retain
their ordinary sequential meaning? This campaign concerns the hash-pinned
public educational demo, not Notion production or security properties.

Candidate claim: for a reachable document D and an in-bounds request q, the
display immediately after issuing q equals the independent visible-list edit
q(D). A single reproducible disagreement falsifies this claim. Convergence is
a separate question; replicas can agree on an incorrect edit.

The reality oracle is the seven JavaScript modules pinned in
`experiments/notion-oracle/sources.json`. The executable specification imports
no demo code. Existing Lean interval and split counterexamples check semantic
counterparts, not source execution. New counterparts will be added only when
they expose a useful semantic distinction.

## Experiment design

Generate valid client requests on distinct replica sessions. Exchange complete
causal archives between rounds; never fabricate transaction payloads. Probe
fresh copies of each reached document with insertion, deletion, split,
merge-block and bold requests. Use ASCII text to avoid conflating indexing
units. Check text for insertion (format inheritance is deliberately unspecified)
and text plus bold flags for the other operations. Validate all bounds before
issuing requests. Preserve rejected shrink attempts rather than silently
clamping them into different requests.

Keep new root causes separate from variants of N-001 (partial suffix split),
N-002 (empty formatting interval) and N-003 (over-wide formatting interval).
Record seeds, state and request counts, positive controls, minimal replayable
actions and expected/actual values. Search is finite evidence, not completeness.

## Results

With complete causal exchanges between rounds, the search found variants of
the three known failures and no new root cause. The persistent-replica search
with partial delivery, described [below](#offline-replicas-and-partial-delivery),
found two new bugs that lose text (N-004 and N-005). The other useful result is a six-request setup for the split bug using
only splits and block merges after creating the initial text. No subsequent
insertion or deletion is needed.

| Run | Tested joined states | Local edit checks | Disagreements |
| --- | ---: | ---: | --- |
| Concurrent, seed 17002, 250 trials | 2,584 | 68,871 | 99 split; 153 missed bold; 48 outside-selection bold |
| Concurrent, seed 17005, 100 trials | 1,117 | 30,626 | 61 split; 44 missed bold; 17 outside-selection bold |
| Sequential, seed 17004, 60 trials | 600 | 12,367 | None |
| Split/merge only, seed 17003, 100 trials | 1,000 | 10,210 | Known split failure reproduced; individual failures not counted |

These are 122,074 local edit checks, not distinct histories: each state is
probed many times, and both concurrent runs include the same directed split
suite. Insertion, deletion and local block-merge probes found no disagreement.
The two concurrent runs skipped 66 and 33 oversized states respectively; they
retained every failing probe from the tested states. The sequential run skipped
none. Every generated setup request passed the bounds checks.

The structural run also checked character conservation at all 1,000 joins:
no character loss or duplication was observed. The other runs passed 4,301
checks that reversed and repeated receipt of the same archive preserves the
display. These are auxiliary checks; the source sorts transactions before
replay, so they are not a convergence proof. Nor does the sequential run prove
that concurrency is necessary for failure.

## Smaller split reproduction

Positions and block numbers below are zero-based. `merge(i)` appends block i to
its immediate predecessor. `empty` denotes an empty displayed block.

Start with one block containing `ab`.

1. Session S splits block 0 at position 0 twice, reaching
   `empty | empty | ab`.
2. Two sessions start from that common state. A splits block 2 at position 1,
   then merges block 2 into its predecessor. B concurrently merges block 2
   into its predecessor. After exchange, the display is `empty | a | b`.
3. Session C merges block 2 into its predecessor, reaching `empty | ab`.
4. Split block 1 at position 0.

**Expected:** `empty | empty | ab`. **Observed:** `empty | b | a`.
The first three steps contain six setup requests; the fourth is the failing
request. The independent specification requires the entire displayed suffix
`ab` to move to the new block. The source instead moves the subtree containing
`a` and leaves sibling `b` behind. This is a variant of N-001, not a new bug.

The passing control creates `empty | ab` directly and issues the identical
split. It produces `empty | empty | ab`. Thus the failure depends on the
underlying structure left by prior edits, despite identical displayed text.
The [regression](../experiments/notion-correctness/regressions.mjs) asserts both
outcomes and their disagreement; the [saved record](../experiments/notion-correctness/results/six-step-split.json)
contains the action trace, final generated transaction and control results.
Greedy shrinking minimises representatives under the recorded reductions;
no globally shortest trace is claimed.

## Classification and evidence

| Symptom | Root cause | Existing formal counterpart |
| --- | --- | --- |
| Split moves only part of the displayed suffix | A structural subtree need not equal a displayed suffix (N-001) | `NotionSplitSpec.minimized_split_zero_rejects_ordinary_contract` |
| Bold misses selected text | Display order reverses the endpoints of an underlying instance interval (N-002) | `NotionFormattingCounterexample.two_character_reversal` |
| Bold changes unselected text | The underlying interval includes characters displayed elsewhere (N-003) | `NotionFormattingCounterexample.noncontiguous_selection_overformats` |

The diagnostic replayed all 422 failing probes from the two concurrent runs;
every observed output matched the prediction from the source's subtree or
interval rule. This supports the
classification independently of symptom names; it does not replace the
independent list oracle used to detect incorrect edits. The original three
regressions, their control, the new split regression, and hand-derived controls
for every operation run before each experiment.

The two existing Lean modules rebuilt successfully (469 build jobs). They
prove the stated restricted semantic counterparts. The new six-request
JavaScript setup is executable evidence, not a newly mechanised replay proof.
No new Lean counterpart was needed to distinguish the observed root causes.

See the [runner and reproduction instructions](../experiments/notion-correctness/README.md)
and [saved results](../experiments/notion-correctness/results/). The finite
search covers ASCII text, bold formatting and complete causal exchanges
between rounds; it does not establish completeness or exclude further bugs.
This complete-exchange search left the paper and artifact claims unchanged; the
partial-delivery results below add two bugs to them.

## Offline replicas and partial delivery

**Question.** Does local edit correctness fail in new ways when persistent
replicas keep editing different views while only some messages have arrived?
Each generated transaction records the issuer's known transactions; a replica
receives a request only after its predecessors, and all transactions of one
request together. The falsifiers are a valid local request whose effect
disagrees with the independent list specification, and a split or block merge
that changes the multiset of visible characters. Equal-archive convergence is
checked separately.

| Run | Edits | Deliveries | Edits issued while some remote requests had arrived and others had not | Failures |
| --- | ---: | ---: | ---: | --- |
| Network, seed 27001, 100 trials of 40 steps | 2,859 | 6,667 | 1,180 | 1 split (N-001) |
| Network, seed 27002, 100 trials of 80 steps | 5,296 | 12,365 | 3,537 | 10 split (N-001); 1 missed bold (N-002); 6 empty document (new) |
| Offline split/merge only, seed 17102, 12 trials of 110 steps | 913 | 1,826 | not recorded | 6 local; 8 character-conservation (new) |

Every network trial synchronised at the end, and all replicas then showed the
same display. In the network runs, the source-based classifier explained every
split and bold failure by the N-001 and N-002 rules, and none of the
empty-document failures.

### N-004: five requests hide the whole document

Shrinking one seed-27002 failure gives five requests over the blocks
`a · b · c`. A merges `c` into `b`, splits that block at zero, and merges `bc`
back. B concurrently merges `b` into `a`, receives A's first two requests
(`empty · abc`), and merges `abc` into its predecessor (`abc`). When A's last
merge arrives, B shows no block; `abc` is still stored, but only in removed
blocks. A merge locates its target by the end item of a text slice, without
checking that the block now holding that slice is alive, and a merge has
already removed that block.

### N-005: a delayed merge hides a character

Shrinking a seed-17102 conservation failure gives four requests over `x`. A
splits at zero. B concurrently splits at one and merges the empty block back.
A receives only B's split and merges `x` into the empty block before it. When
B's held merge arrives, `x` disappears. The merge's move would create a cycle,
so the source restores the slice as a deterministic no-op, but the same
transaction still removes the block that now holds `x`. Instrumenting the two
code paths separates the causes: N-004 never reaches the cycle no-op, and
N-005 never moves text into a removed block.

**Evidence.** The permanent [regressions](../experiments/notion-oracle/regressions.mjs)
assert both failures, that the hidden characters are still stored, and passing
controls that change one ingredient: two for N-004 and three for N-005. The
traces are in [results](../experiments/notion-correctness/results/)
(`network-loss-diagnosis.json`, `offline-conservation-minimised.json`,
`offline-conservation-regression.json`, `offline-structural-17102.json`). Both
failures need the demo's merge-block request, whose block removal is separate
from its move. Their Lean counterparts are in `NotionMergeLossCounterexample` (see
[the bug catalogue](notion-bugs.md)). The search is finite and does not exclude
further bugs.

## Block merge design gate

The [merge design experiment](../experiments/notion-merge-design/README.md)
reruns these harnesses on a patched copy of the demo whose merge moves the
source's whole slice tree to the end of the tree holding the slice at which
the request was anchored and derives removal from that move. All 162,373
archive comparisons, deduplicated within each harness, agree with the
specification, with no split failure and no text loss; N-001, N-004 and N-005
do not occur, while the bold failures N-002 and N-003 persist. Restoring
independent removal brings text loss back. Keeping the demo's placement,
directly under the anchored slice, loses no text but lets trees branch, so
N-001 returns; attaching at the holder tree's end avoids both. The [design note](notion-merge-block-design.md) gives the
specification, and [the correspondence overview](notion-core-correspondence.md#block-merge)
lists the Lean results.
