# Block merge design: executable gate

This experiment tests the block merge of
[notion-merge-block-design.md](../../docs/notion-merge-block-design.md) on a
patched copy of Notion's pinned public demo, before any Lean is written. It
also tests two candidate alternatives: slice-following, which keeps the
demo's own targeting, and anchor-absorb, which uses the demo's recorded
anchor only to choose the tree that absorbs the source. It reports a verdict for each hypothesis, runs negative
controls, and records where the design note's claims are not borne out.

## Goals and hypotheses

The question is whether the design's merge gives every reachable display a
sequential meaning. Under that merge, the source block's whole slice tree
attaches under the last node of the tree holding the target's root. Liveness is
derived from the tree, and merged blocks stay in the display order as
tombstones. The hypotheses H1 to H4 are those of the design note:

- **H1 (RA-linearizability).** For every reachable archive, the display equals
  the identity specification folded over the decoded commands in replay order.
- **H2 (conservation).** No reachable display loses or duplicates a visible
  character relative to that fold.
- **H3 (local effect).** The issuer's own merge has the positional meaning.
  The target shows its old text followed by the source's, and the source is
  gone.
- **H4 (obligation correspondence).** Making removal independent of the move,
  as the demo does, reintroduces text loss in both the N-004 and the N-005
  shape. No other single change to the design does.

The design gives `ab · cd`, with the second block merged into the first while
the first is split after `a`, the display `acd · b` when the split replays
first. No sequence of the client requests (split the first block after `a`;
merge the second block into its predecessor) gives that display: both
sequential orders give `a · bcd`
([review-client-serialisations.json](results/review-client-serialisations.json)).
The demo's targeting gives `a · bcd`. Slice-following is the demo's targeting
with the design's derived removal: the issuer records the end item of the
target's last slice, and on replay the source's whole tree becomes the last
child of the node that ends there, wherever that node now lives. Its
hypotheses:

- **H5 (slice-following).** Slice-following agrees with its specification
  (`sliceFollow` below) on every archive (H1), conserves text (H2), meets the
  local positional contract for every request (H3), and gives the review's
  case the sequential result `a · bcd` in both replay orders. Falsifiers: an
  archive that disagrees with `sliceFollow`, a lost character, a local request
  whose result differs from the positional contract, or a litmus final that
  differs from its hand-derived value.
- **H6 (slice-following controls).** Making removal independent of the move
  under slice-following loses text, as under absorb.

Anchor-absorb records the same anchor as slice-following. On replay it finds
the node that ends there, takes the root of that node's tree as the holder,
and attaches the source's whole tree under the holder's last preorder node,
as absorb does. The anchor chooses the holder tree; placement is the tree's
end. Its hypothesis:

- **H7 (anchor-absorb).** Anchor-absorb agrees with `sliceFollow` on every
  archive (H1), conserves text (H2), meets the local positional contract for
  every request (H3), keeps every slice tree a chain (0 branching archives,
  so the N-001 split failure cannot occur), and gives the review's case
  `a · bcd` in both replay orders. Falsifiers: an archive that disagrees with
  `sliceFollow`, a lost character, a local request whose result differs from
  the positional contract, an archive in which some slice node has more than
  one child, or a litmus final that differs from its hand-derived value.

## What is in this directory

| File | Role |
|---|---|
| `design-patch/patch.py` | Exact-anchor patches of the pinned `document.js` and `replica.js`, one set per variant. Third-party source is not committed. |
| `identity-spec.mjs` | Independent sequential specification and the decoder from transactions to atomic command groups. The specification covers create, insert, delete, split and merge over retained identity slots, following `NotionCoreSpec.lean`. It imports no demo code. |
| `ra-check.mjs` | Folds the specification over an archive in replay order (counter, then session) and classifies the result against the display as agree, stuck, conservation or placement. It imports no demo code. |
| `ra-hook.mjs` | Preloaded with `node --import`. It checks every distinct archive whose document a harness builds, in every specification mode. It also checks every issued deletion against the positional contract, and records block-order inversions, slice-tree shape, and whether each disagreement occurs in an archive whose slice forest branches. |
| `spec-controls.mjs` | 58 hand-derived checks of the specification and decoder. Each value check has a companion check that rejects the tempting degenerate behaviour or the rival meaning's value. |
| `gate.mjs` | Reissues N-001 to N-005 as client requests. For each it reports the contract, the expected and observed outcomes, and whether the demo failure's precondition was reached. It also runs specification mutants that the comparison must detect. |
| `litmus.mjs` | The merge litmus histories (a) to (i), under every schedule. |
| `ra-shrink.mjs` | Shrinks network histories that disagree with the variant's own specification mode. |
| `run.py` | Fetches and hash-verifies the pinned modules, builds every variant, runs all harnesses in parallel, and writes `results/`. |

### Specification modes

- `absorb` is the specification. The holder of the target is the block whose
  slots contain the target's root slot. If the source is alive and the holder
  exists and differs from the source, the holder's slots become
  `holder.slots ++ source.slots`. The source then stays in the list as a
  tombstone: not alive, with no slots. Otherwise the document is unchanged.
- `skip` is the earlier meaning: a no-op unless the target itself is alive.
- `removed` is `absorb` with the merged source deleted from the list instead
  of tombstoned.
- `sliceFollow` is the meaning proposed for slice-following. The decoded merge
  carries an anchor: the instance of the target's last slice at issue time and
  that slice's end item, a split marker or `end`. The anchor is a position,
  the end of the slice that ends there. For `end` it is the position after the
  last slot of the instance; for a marker `m` it is the position immediately
  before `m` in the instance. The specification records these positions as
  invisible end slots: a created block is `[i/start, i/^end]`, and a split at
  origin `o` with marker `m` leaves `i/^m` immediately after `o` in the block
  that keeps the prefix. The holder is the block whose slots contain the
  anchor's end slot. The merge is a no-op when the source is not alive or the
  holder is the source. Otherwise the source's slots are appended at the end
  of the holder, and the source becomes a tombstone.
- `sliceFollowAnchor` is `sliceFollow` with the source's slots inserted
  immediately after the anchor's end slot instead of at the holder's end. It
  is a diagnostic.

The anchor cannot be read as the slot `i/m`. That slot heads the slice that
starts at `m`, while the demo attaches under the slice that ends at `m`, its
left neighbour. Under that reading, splitting `abc` after `a` and merging the
new block back would find the source itself as holder and do nothing.

On `ab · cd` with the first block split after `a` first, the end of `t` lies
in the split-off block, so the merge gives `a · bcd` under both placements. On
a holder that absorbed `U` after the anchor (litmus (h)), the end placement
gives `abZcdYW`, as the implementation does, and the anchor placement gives
`abcdYWZ`. On litmus (i) the implementation gives `abZWcdYX`, which neither
placement gives: see the results.

### Variants

| Variant | Mode it implements | Change from the design |
|---|---|---|
| `demo` | (none) | The unmodified pinned demo. |
| `design` | absorb | None. A merge emits one `mergeBlock{sourceBlockId, targetBlockId}` with one clock tick. On replay it walks from the target's root to the root of the tree holding it, and attaches the source's root under that tree's last preorder node. It is a no-op when the source has a parent or when that root is the source's own. |
| `skip` | skip | A no-op whenever the target is not alive. |
| `no-source-check` | absorb | No source liveness check: a merged source is detached from its host first. |
| `remove-independently` | absorb | Each merge transaction also carries `removeBlock`, which hides the source whether or not the attachment happened. |
| `skip-remove-independently` | skip | The skip rule plus the independent `removeBlock`. |
| `design-order-splice` | absorb | A merge also deletes the source from `blockOrder`, as the demo's `removeBlock` does, so a block later created after it goes to the front. |
| `slice-following` | sliceFollow | The demo's targeting. A merge emits one `mergeBlock` with one clock tick, carrying `targetTextInstanceId` and `targetTextSliceEndItemId` of the target's last preorder node, as the demo's move does. There is no split at the root's start, no clock reservation and no `removeBlock`. On replay `#findNodeEndingWith` searches every tree, and the source's root becomes the last child of the node found. It is a no-op when the source has a parent or when that node lies in the source's own tree. |
| `slice-remove-independently` | sliceFollow | `slice-following` plus the independent `removeBlock`. |
| `anchor-absorb` | sliceFollow | The request is that of `slice-following`. On replay, after the source liveness check, `#findNodeEndingWith` resolves the anchored node; the holder is the root of that node's tree. It is a no-op when the holder is the source's root; otherwise the source's root becomes the last child of the holder tree's last preorder node. |

In every non-demo variant, `BlockRecord.alive` is a getter that is true iff the
title root has no parent. `blockOrder` keeps merged blocks and `aliveBlocks`
filters them out. Slice lookups and the partition invariant walk only parentless
roots, and the invariant also requires every block's root to be reached exactly
once.

### Harnesses

The committed harnesses of [notion-correctness](../notion-correctness/README.md)
are copied unchanged into each variant's working directory, with one exception.
In `campaign.mjs`, the calibration line asserting that the demo's bold bugs
reproduce is replaced by a comment; those counts are reported instead. The runs
are:

- network search, seed 27002 (100 trials, 80 steps);
- offline structural search, seed 17102 (12 trials, 110 steps);
- complete-exchange searches, seeds 17002 (250 trials) and 17005 (100);
- sequential run, seed 17004 (60 trials);
- structural run, seed 17003.

The positional contract for local requests, including merge, is
[positional-spec.mjs](../notion-oracle/positional-spec.mjs).

### Litmus histories

Two replicas P and Q start from one archive. Each history runs:

- with both session namings, which flips which concurrent transaction replays
  first;
- with both delivery orders;
- with one replica issuing every valid positional request on its view while
  the other replica's transactions are held (before receiving anything) or
  after receiving them.

Final displays of the base schedules are hand-derived for `absorb`, and for
`skip`, for the slice-following implementation and for anchor-absorb where
they differ. "P first" means P's concurrent transaction replays first.

- (a) split S at k ‖ merge S into T, for k = 0, 1, 2. Result: `['ab'+'cd'[:k], 'cd'[k:]]` in either order, under every meaning.
- (b) merge S into T ‖ merge T into U, from `a|b|c`. Absorb and slice-following give `['abc']` in both orders. Skip gives `['ab','c']` when T's merge replays first.
- (c) merge S into T ‖ a forged `mergeBlock` of T into S, which no client request can issue; under slice-following and anchor-absorb it is anchored at the end of S's instance. Result: `['ab']` or `['ba']`; whichever merge replays second hits the cycle case. Under anchor-absorb, when S's merge replays first the anchored node is S's root, whose tree is rooted at T, the forged merge's source.
- (d) insert at 0 of S ‖ merge S into T, with S nonempty and with S empty. Results: `['abXcd']` and `['abX']`.
- (e) after a merge, delete a range across the S/T boundary ‖ split at k = 0..4. Result: the identity-retaining split/delete outcome.
- (f) create after S ‖ merge S into T. Result: `['abcd','Z']`, with the new block where S was.
- (g) the review's case, from `ab|cd`: split T after `a` ‖ merge S into T. Slice-following gives `['a','bcd']` in both orders. When the split replays first, the merge's anchor, the end of T's instance, is the slice holding `b` in the new block F, so `cd` follows `b`. When the merge replays first, `cd` hangs under T's root, and the split moves `b` with `cd` below it. Absorb gives `['acd','b']` when the split replays first and `['a','bcd']` otherwise. Anchor-absorb gives `['a','bcd']` in both orders: when the split replays first, the anchored node is F's root, a lone node, so `cd` goes under it; otherwise it goes under T's root, as under absorb. The positional sequential result is `['a','bcd']` in both orders.
- (h) merge U into T ‖ merge S into T, both anchored at the end of T. From `ab|cd`, P creates U after T, types `Z` and merges U; Q types `YW` at the end of S and merges S. Both merges have counter 9. P first: U becomes the child of T's root; S's anchor is the same node, so S becomes its second child and renders after U: `['abZcdYW']`. Q first: `['abcdYWZ']`. Absorb, skip and anchor-absorb chain the second source under the first, with the same text. Under anchor-absorb the second merge's anchored node is T's root, and the end of T's chain is the first source's root. T's root has two children only under slice-following.
- (i) as (h), with P then creating V after T, typing `W` and merging V (counter 12, anchored at the end of U's instance), and Q typing `YX`. P first: T's root has children U then S, and V hangs under U, so it renders before S: slice-following gives `['abZWcdYX']`. Absorb and skip append V at the end of T's chain: `['abZcdYXW']`. Anchor-absorb gives the same: V's anchored node is U's root, whose tree is rooted at T, so V goes to the end of T's chain. Q first: `['abcdYXZW']` under every meaning.

In (a), (b), (d), (e) and (f) every merge's anchored node is the target's
root, which no concurrent split separates from the rest of the target's tree,
so anchor-absorb gives the absorb finals.

## Results

Run with Node v26.3.1.

**Calibration.** The demo calibration scripts all exit 0. The demo variant
reproduces the committed counts exactly:

- network 27002: 10 `split:placement`, 6 `structure:empty`, 1 `bold:missed`;
- offline 17102: 6 local failures and 8 conservation failures;
- campaign 17002: 153 / 48 / 99;
- campaign 17005: 44 / 17 / 61.

So preloading the check changes no history.

**RA check.** Counts are over all distinct archives built by the harnesses of a
variant, compared with its own mode, deduplicated within each run. Column
meanings:

- `=absorb`, `=skip`, `=sliceFollow`: archives that agree with that meaning.
- `stuck*`: archives that are stuck in the `removed` mode.
- `inv`: pairs of blocks displayed in opposite orders in different archives.
- `xdel`: cross-instance deletions that agree with the positional contract.
- `branch`: archives in which some slice node has more than one child;
  `max ch.` is the largest number of children of any node.

| Variant | Own mode | Archives | Agree | Stuck | Conservation | Placement | =absorb | =skip | =sliceFollow | stuck* | inv | xdel | branch | max ch. |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| demo | (absorb) | 163586 | 98351 | 42046 | 622 | 22567 | 98351 | 93020 | 102649 | 48770 | 20551 | 3248/3248 | 63633 | 4 |
| **design** | absorb | 162414 | **162414** | 0 | **0** | **0** | 162414 | 139237 | 17996 | 42267 | 0 | 3085/3085 | **0** | 1 |
| skip | skip | 163400 | 163400 | 0 | 0 | 0 | 148288 | 163400 | 17956 | 46513 | 0 | 2974/2974 | 0 | 1 |
| no-source-check | absorb | 162256 | 155346 | 0 | 0 | 6910 | 155346 | 135639 | 18072 | 43162 | 0 | 3056/3056 | 0 | 1 |
| remove-independently | absorb | 162390 | 162298 | 0 | 92 | 0 | 162298 | 139202 | 17996 | 42267 | 0 | 3081/3081 | 0 | 1 |
| skip-remove-independently | skip | 154296 | 139477 | 0 | 6103 | 8716 | 148104 | 139477 | 18002 | 36812 | 0 | 2956/2956 | 0 | 1 |
| design-order-splice | absorb | 164149 | 135149 | 0 | 0 | 29000 | 135149 | 120492 | 18100 | 44579 | 40606 | 3167/3167 | 0 | 1 |
| **slice-following** | sliceFollow | 162373 | **161587** | 0 | **0** | **786** | 140397 | 125400 | 161587 | 42750 | 0 | 3154/3154 | **2844** | 3 |
| slice-remove-independently | sliceFollow | 162349 | 161413 | 0 | 108 | 828 | 140395 | 125380 | 161413 | 42750 | 0 | 3150/3150 | 2844 | 3 |
| **anchor-absorb** | sliceFollow | 162373 | **162373** | 0 | **0** | **0** | 140576 | 125580 | 162373 | 42750 | 0 | 3154/3154 | **0** | 1 |

Archives without an anchored merge agree with `sliceFollow` only when they
contain no merge, which is why the absorb variants agree with it on about
18000 archives. All 786 `sliceFollow` disagreements of `slice-following` occur
in archives whose slice forest branches; on chain-shaped archives it agrees
with `sliceFollow` everywhere. `sliceFollowAnchor` disagrees on 1376
archives, also all branching.

Anchor-absorb agrees with `sliceFollow` on all 162373 of its archives, and no
slice node in any of them has more than one child. The absorb specification
disagrees with it on 21797 archives. `sliceFollowAnchor` disagrees with it on
1651 archives, all chain-shaped: in these, visible text follows the anchor in
its holder, as in litmus (h), and the source goes after that text.

**Local positional contract and conservation.** Failure counts by signature:

| Variant | network 27002 | offline 17102 (local, conservation) | campaign 17002 | campaign 17005 | sequential 17004 | structural 17003 |
|---|---|---|---|---|---|---|
| demo | split 10, empty 6, bold 1 | 6, 8 | bold 201, split 99 | bold 61, split 61 | 0 | split 1 |
| design | bold 1 | 0, 0 | bold 154 | bold 108 | 0 | 0 |
| skip | bold 2 | 0, 0 | bold 157 | bold 97 | 0 | 0 |
| no-source-check | bold 5 | 0, 0 | bold 151 | bold 109 | 0 | 0 |
| remove-independently | bold 1 | 0, 3 | bold 154 | bold 108 | 0 | 0 |
| skip-remove-independently | bold 4 | 0, 51 | bold 147 | bold 108 | 0 | text loss 85 |
| design-order-splice | bold 4 | 0, 0 | bold 209 | bold 129 | 0 | 0 |
| slice-following | split 4 | 2 (split), 0 | bold 155 | bold 43 | 0 | 0 |
| slice-remove-independently | split 4 | 2 (split), 12 | bold 155 | bold 43 | 0 | 0 |
| anchor-absorb | 0 | 0, 0 | bold 155 | bold 43 | 0 | 0 |

No merge request failed its positional contract in any variant. For example,
the design passed 6807 merge probes in campaign 17002, and slice-following
and anchor-absorb 6805 each. The litmus histories of the design and of
anchor-absorb each pass 13396 local checks with no failure; slice-following
fails 44 of them, all splits, in (h) and (i).

**Recorded bugs, reissued as requests.** PASS means the contract holds.

| Variant | N-001 | N-001 six-request | N-002 | N-003 | N-004 | N-005 | N-005 persistent |
|---|---|---|---|---|---|---|---|
| demo | FAIL | FAIL | FAIL | FAIL | FAIL | FAIL | FAIL |
| design | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |
| skip | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |
| remove-independently | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |
| skip-remove-independently | PASS | PASS | FAIL | FAIL | FAIL* | PASS | FAIL |
| slice-following | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |
| slice-remove-independently | PASS | PASS | FAIL | FAIL | PASS* | FAIL | FAIL |
| anchor-absorb | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |

\* Under any merge that takes one tick and leaves no left-over slice, the N-004
request history does not reach the demo's precondition. B's view before its
last merge is `a · bc`, not `empty · abc`. Litmus (b) is the targeted
equivalent.

**Litmus.** The design matches all 64 hand-derived absorb finals, with no
divergence, exception or specification disagreement. `skip` differs from the
absorb finals exactly in (b) when T's merge replays first, in both delivery
orders (`['ab','c']`). `remove-independently` loses everything in (c) when the
forged merge replays first. `skip-remove-independently` loses text in (b)
(`['ab']`) and in (c). `design-order-splice` puts the new block at the front in
(a) and (f).

`slice-following` matches all 64 hand-derived slice-following finals, with no
divergence or exception. It differs from the absorb finals in exactly two
histories, in both delivery orders, both when P replays first:

| Litmus | slice-following | absorb |
|---|---|---|
| (g) split T after `a` ‖ merge S into T | `['a','bcd']` | `['acd','b']` |
| (i) U and S into T, then V anchored at U | `['abZWcdYX']` | `['abZcdYXW']` |

The unmodified demo gives the slice-following final in every litmus history
it can run ((c) needs the forged `mergeBlock`, which it does not know), and
fails the same 44 local split checks in (h) and (i).
`slice-remove-independently` loses everything in (c) when the forged merge
replays first.

`anchor-absorb` matches all 64 hand-derived anchor-absorb finals, with no
divergence, exception or specification disagreement. It differs from the
absorb finals only in (g) when the split replays first, in both delivery
orders, where it gives `['a','bcd']`. It differs from the slice-following
finals only in (i) when P replays first, where it gives the absorb final
`['abZcdYXW']`.

**Specification sensitivity.** On design archives the absorb specification
agrees with the display. Mutants that ignore merge, or that put the source
first, report placement disagreements. The skip meaning reports a placement
disagreement on the history of litmus (b).

**Shrunk witnesses.** Fixed points of `ra-shrink.mjs` for network 27002 are
stored in each variant's `network-27002-shrink` entry. The
`remove-independently` witness has 24 events from `ab | cd`. Its last merge
names a target that, unknown to the issuer, had been merged into the first
block. A later split of that block, issued before the target's root, carried
the root into the block the issuer then merged. So the holder is the source
(the cycle case), the move is skipped, and the independent removal hides
`🙂`. The `slice-following` placement witness has 40 events; the
`slice-remove-independently` conservation witness has 24.

## Verdict per hypothesis

- **H1 holds on every archive checked.** All 162414 design archives agree with
  the absorb specification. The `removed` reading is stuck on 42267 of them,
  always at `create after a block that is not in the document`. That is a split
  of S concurrent with a merge of S, with the merge replayed first, and it is
  why merged sources must stay in the list as tombstones.
- **H2 holds.** The design shows 0 conservation disagreements, 0 conservation
  failures in the offline and structural searches, and 0 `structure:empty`.
  Conservation also holds by construction: every slice node lies in exactly one
  parentless tree, and every parentless root is displayed.
- **H3 holds.** There are 0 merge failures of the positional contract in all
  searches and litmus histories.
- **H4 is partly refuted.** Making removal independent of the move does lose
  text: 92 conservation disagreements and 3 offline conservation failures.
  However, under absorb this happens only through the cycle case, which is the
  N-005 shape. The N-004 shape, a merge into a merged-away target, never skips
  under absorb, so it cannot lose text this way: the N-004 history and litmus
  (b) pass. Both shapes return only when independent removal is combined with
  the skip rule (`skip-remove-independently`). In that combination there are
  6103 conservation disagreements, 51 offline conservation failures and 85
  structural text losses, and both regressions and litmus (b) and (c) fail. The
  second half of H4 holds for the single changes tested: `skip`,
  `no-source-check` and `design-order-splice` lose no text.
- **H5 is refuted.** Slice-following conserves text (0 conservation
  disagreements, 0 conservation failures in every search), gives the review's
  case `a · bcd` in both orders, gives every issued merge its positional
  meaning, and passes N-001, N-004 and N-005. It fails in two other places:
  - It disagrees with `sliceFollow` on 786 archives, all with a branching
    slice forest.
  - It fails the positional contract for split: 4 network and 2 offline
    `split:placement` failures, and 44 local split failures in litmus (h) and
    (i).

  Both failures have one cause. Two merges issued concurrently into the same
  target record the same anchor, so the anchor node gets two children. Slice
  trees are then no longer chains (2844 branching archives, up to 3
  children). A split moves the split node's right part and its children, not
  the later siblings of its ancestors, so it no longer moves the whole
  displayed suffix. This is N-001. In (h), after both merges have been
  exchanged, a split of `abZcdYW` at 3 gives `abZcdYW · ""` instead of
  `abZ · cdYW`. The demo has the same failure on the same histories.
- **H6 holds.** `slice-remove-independently` has 108 conservation
  disagreements and 12 offline conservation failures, fails N-005 in both
  forms, and loses everything in litmus (c).
- **H7 holds on every archive checked.** Anchor-absorb agrees with
  `sliceFollow` on all 162373 archives, with 0 conservation disagreements and
  0 conservation failures in every search. No request failed its positional
  contract: 0 split failures in every search and 0 of 13396 local litmus
  checks. No archive has a slice node with more than one child. It gives
  `a · bcd` on the review's case in both replay orders, matches all 64
  hand-derived finals, and passes N-001 in both forms, N-004 and N-005 in both
  forms.

## Absorb versus slice-following

The two merges differ in two ways.

**Where the source lands.** Absorb attaches under the last node of the tree
that now holds the target's root. Slice-following attaches under the node
that ends with the item recorded at issue time. When a concurrent split has
carried the target's last slice into a new block, slice-following follows it
there (litmus (g): `a · bcd`, where absorb gives `acd · b`). Slice-following's
result is the one both sequential client histories give. When an earlier
merge attached below the anchor node, slice-following renders the new source
before that earlier source's later siblings, not at the end (litmus (i)).

**Tree shape.** Absorb keeps every slice tree a chain (0 branching archives),
so a split always cuts the whole displayed suffix and N-001 cannot occur.
Slice-following lets two concurrent merges share an anchor node and so builds
branching trees, on which the existing split loses its positional meaning.
The flat slot specification cannot describe these trees either: the source
renders after the anchor node's whole subtree. That is the holder's end when
the subtree is a suffix of the holder (litmus (h)) and the position right
after the anchor when the node has no children. In litmus (i) it is
neither. So `sliceFollow` as proposed is not the meaning of slice-following.

Slice-following therefore fixes the review's case at the price of N-001.

Anchor-absorb separates the two choices. It finds the holder from the anchor,
as slice-following does, and places the source at the holder tree's end, as
absorb does. Placement at a tree's end keeps every tree a chain, whichever
tree holds the source, so the anchor's job is only to choose the tree. On the
gate's archives this merge has the sequential result on the review's case,
keeps chains, conserves text, and has `sliceFollow` as its meaning: on a
chain the end of the anchored node's subtree is the end of its tree, which is
the holder's end in the slot specification.

## Further findings

1. **The liveness check is a choice of meaning, not an obligation.** Both rules
   conserve text and both agree with their own specification on every archive
   (`design` with absorb, 162414 of 162414; `skip` with skip, 163400 of
   163400). They differ on 23177 design archives. The only differing litmus
   final is (b), where skip leaves `ab · c` in one replay order.
2. **The cycle case is reachable without forgery.** A split of the absorbing
   block can carry a merged block's root into a fresh block. A concurrent issuer
   who still sees the merged block alive can then merge that fresh block into
   it. The design's no-op handles this without loss. The case matters only if
   removal is separate from the move.
3. **Under absorb, N-001 disappears and every slice tree is a chain.** In all
   162414 design archives, no slice node has more than one child, so a split's
   right node carries the whole displayed suffix. The design has 0 split
   failures in all searches. The demo has a node with two or more children in
   63633 of its archives; slice-following in 2844. Anchor-absorb, like the
   design, has none.
4. **Order inversions.** With tombstones, no two blocks are ever displayed in
   opposite orders across archives (0 in every tombstoning variant, including
   slice-following). The demo shows 20551 inversions and `design-order-splice`
   shows 40606, from front placement after a removed predecessor. The demo
   needed such front placement for its N-005 cycle.
5. **The source liveness check matters for placement only.** Without it
   (`no-source-check`), merging an already merged source moves it out of its
   host. That loses no text but disagrees with the specification on 6910
   archives.
6. **The bold bugs N-002 and N-003 persist under every variant.** Annotation
   intervals are unchanged, and formatting is outside the specification.

## What the gate does not establish

- It checks finitely many histories: the listed seeds, two to four replicas,
  short ASCII seeds, and a few insertion strings including one astral
  character.
- Its RA claim is agreement with one specific witness order (replay order) on
  those archives, not a proof.
- The block-order and tree-shape observations are diagnostics over the archives
  seen, with blocks identified by their creating transactions.
- Formatting is outside the specification.
- The patched demo is a different implementation from the public demo and from
  Notion's production editor. Nothing here concerns production.

## Rerun

From the repository root, with Python 3, Node.js and curl:

```sh
python3 experiments/notion-merge-design/run.py              # fetches and verifies the pinned modules
python3 experiments/notion-merge-design/run.py --cache DIR  # or uses a directory holding them
python3 experiments/notion-merge-design/run.py --quick --results /tmp/gate-quick
python3 experiments/notion-merge-design/run.py --from-results  # re-trims results/ and reprints the tables
```

`--variants` selects variants; a run of some variants replaces their rows in
an existing `summary.json` and keeps the other rows and the demo calibration.
A full run takes about 50 minutes on 12 cores.
It writes `results/<variant>.json` and `results/summary.json`. Each per-variant
file holds per-harness counts and findings without per-trial traces, the
smallest disagreeing archive per category of the variant's own mode (when it
has at most 40 transactions), and the shrunk network witnesses. To inspect a
patched module, run
`python3 design-patch/patch.py --cache DIR --emit OUT --variant slice-following`.
