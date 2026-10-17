# Block merge design: executable gate

This experiment tests the block merge of
[notion-merge-block-design.md](../../docs/notion-merge-block-design.md) on a
patched copy of Notion's pinned public demo, before any Lean is written. It
reports a verdict for each hypothesis, runs negative controls, and records where
the design note's claims are not borne out.

## Goals and hypotheses

The question is whether the design's merge gives every reachable display a
sequential meaning. Under that merge, the source block's whole slice tree
attaches under the last node of the tree holding the target's root. Liveness is
derived from the tree, and merged blocks stay in the display order as
tombstones. The hypotheses are those of the design note:

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

## What is in this directory

| File | Role |
|---|---|
| `design-patch/patch.py` | Exact-anchor patches of the pinned `document.js` and `replica.js`, one set per variant. Third-party source is not committed. |
| `identity-spec.mjs` | Independent sequential specification and the decoder from transactions to atomic command groups. The specification covers create, insert, delete, split and merge over retained identity slots, following `NotionCoreSpec.lean`. It imports no demo code. |
| `ra-check.mjs` | Folds the specification over an archive in replay order (counter, then session) and classifies the result against the display as agree, stuck, conservation or placement. It imports no demo code. |
| `ra-hook.mjs` | Preloaded with `node --import`. It checks every distinct archive whose document a harness builds, in every specification mode. It also checks every issued deletion against the positional contract, and records block-order inversions and slice-tree shape. |
| `spec-controls.mjs` | 31 hand-derived checks of the specification and decoder. Each value check has a companion check that rejects the tempting degenerate behaviour. |
| `gate.mjs` | Reissues N-001 to N-005 as client requests. For each it reports the contract, the expected and observed outcomes, and whether the demo failure's precondition was reached. It also runs specification mutants that the comparison must detect. |
| `litmus.mjs` | The merge litmus histories (a) to (f), under every schedule. |
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

Two replicas start from one archive. Each history runs:

- with both session namings, which flips which concurrent transaction replays
  first;
- with both delivery orders;
- with one replica issuing every valid positional request on its view, either
  before receiving anything or after receiving the other replica's request.

Final displays of the base schedules are hand-derived for `absorb`, and also
for `skip` where the two differ.

- (a) split S at k ‖ merge S into T, for k = 0, 1, 2. Result: `['ab'+'cd'[:k], 'cd'[k:]]` in either order.
- (b) merge S into T ‖ merge T into U, from `a|b|c`. Absorb gives `['abc']` in both orders. Skip gives `['ab','c']` when T's merge replays first.
- (c) merge S into T ‖ a forged `mergeBlock` of T into S, which no client request can issue. Result: `['ab']` or `['ba']`; whichever merge replays second hits the cycle case.
- (d) insert at 0 of S ‖ merge S into T, with S nonempty and with S empty. Results: `['abXcd']` and `['abX']`.
- (e) after a merge, delete a range across the S/T boundary ‖ split at k = 0..4. Result: the identity-retaining split/delete outcome.
- (f) create after S ‖ merge S into T. Result: `['abcd','Z']`, with the new block where S was.

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
variant, compared with its own mode. Column meanings:

- `other`: disagreements with the other meaning (absorb or skip).
- `stuck*`: archives that are stuck in the `removed` mode.
- `inv`: pairs of blocks displayed in opposite orders in different archives.
- `xdel`: cross-instance deletions that agree with the positional contract.
- `branch`: archives in which some slice node has more than one child.

| Variant | Archives | Agree | Stuck | Conservation | Placement | other | stuck* | inv | xdel | branch |
|---|---|---|---|---|---|---|---|---|---|---|
| demo | 162802 | 97826 | 42046 | 622 | 22308 | 70307 | 48770 | 20551 | 2952/2952 | 62981 |
| **design** | 161630 | **161630** | 0 | **0** | **0** | 23177 | 42267 | 0 | 2789/2789 | **0** |
| skip | 162616 | 162616 | 0 | 0 | 0 | 15112 | 46513 | 0 | 2678/2678 | 0 |
| no-source-check | 161472 | 154562 | 0 | 0 | 6910 | 26617 | 43162 | 0 | 2760/2760 | 0 |
| remove-independently | 161606 | 161514 | 0 | 92 | 0 | 23188 | 42267 | 0 | 2785/2785 | 0 |
| skip-remove-independently | 153512 | 138693 | 0 | 6103 | 8716 | 6192 | 36812 | 0 | 2660/2660 | 0 |
| design-order-splice | 163365 | 134365 | 0 | 0 | 29000 | 43657 | 44579 | 40606 | 2871/2871 | 0 |

**Local positional contract and conservation.** Failure counts by signature:

| Variant | network 27002 | offline 17102 (local, conservation) | campaign 17002 | campaign 17005 | sequential 17004 | structural 17003 |
|---|---|---|---|---|---|---|
| demo | split 10, empty 6, bold 1 | 6, 8 | bold 201, split 99 | bold 61, split 61 | 0 | split 1 |
| design | bold 1 | 0, 0 | bold 154 | bold 108 | 0 | 0 |
| skip | bold 2 | 0, 0 | bold 157 | bold 97 | 0 | 0 |
| remove-independently | bold 1 | 0, 3 | bold 154 | bold 108 | 0 | 0 |
| skip-remove-independently | bold 4 | 0, 51 | bold 147 | bold 108 | 0 | text loss 85 |

`no-source-check` and `design-order-splice` show only bold failures in these
harnesses. No merge request failed its positional contract in any variant. For
example, the design passed 6807 merge probes in campaign 17002, and its litmus
histories pass 6736 local checks with no failure.

**Recorded bugs, reissued as requests.** PASS means the contract holds.

| Variant | N-001 | N-001 six-request | N-002 | N-003 | N-004 | N-005 | N-005 persistent |
|---|---|---|---|---|---|---|---|
| demo | FAIL | FAIL | FAIL | FAIL | FAIL | FAIL | FAIL |
| design | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |
| skip | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |
| remove-independently | PASS | PASS | FAIL | FAIL | PASS* | PASS | PASS |
| skip-remove-independently | PASS | PASS | FAIL | FAIL | FAIL* | PASS | FAIL |

\* Under any merge that takes one tick and leaves no left-over slice, the N-004
request history does not reach the demo's precondition. B's view before its
last merge is `a · bc`, not `empty · abc`. Litmus (b) is the targeted
equivalent.

**Litmus.** The design matches all 52 hand-derived absorb finals, with no
divergence, exception or specification disagreement. `skip` differs from the
absorb finals exactly in (b) when T's merge replays first, in both delivery
orders (`['ab','c']`). `remove-independently` loses everything in (c) when the
forged merge replays first. `skip-remove-independently` loses text in (b)
(`['ab']`) and in (c). `design-order-splice` puts the new block at the front in
(a) and (f).

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
`🙂`.

## Verdict per hypothesis

- **H1 holds on every archive checked.** All 161630 design archives agree with
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

## Further findings

1. **The liveness check is a choice of meaning, not an obligation.** Both rules
   conserve text and both agree with their own specification on every archive
   (`design` with absorb, 161630 of 161630; `skip` with skip, 162616 of
   162616). They differ on 23177 design archives. The only differing litmus
   final is (b), where skip leaves `ab · c` in one replay order.
2. **The cycle case is reachable without forgery.** A split of the absorbing
   block can carry a merged block's root into a fresh block. A concurrent issuer
   who still sees the merged block alive can then merge that fresh block into
   it. The design's no-op handles this without loss. The case matters only if
   removal is separate from the move.
3. **N-001 disappears, and every slice tree is a chain.** In all 161630 design
   archives, no slice node has more than one child, so a split's right node
   carries the whole displayed suffix. The design has 0 split failures in all
   searches. The demo has a node with two or more children in 62981 of its
   archives.
4. **Order inversions.** With tombstones, no two blocks are ever displayed in
   opposite orders across archives (0 in every tombstoning variant). The demo
   shows 20551 inversions and `design-order-splice` shows 40606, from front
   placement after a removed predecessor. The demo needed such front placement
   for its N-005 cycle.
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

`--variants` selects variants. A full run takes about 30 minutes on 12 cores.
It writes `results/<variant>.json` and `results/summary.json`. Each per-variant
file holds per-harness counts and findings without per-trial traces, the
smallest disagreeing archive per category of the variant's own mode (when it
has at most 40 transactions), and the shrunk network witnesses. To inspect a
patched module, run
`python3 design-patch/patch.py --cache DIR --emit OUT --variant design`.
