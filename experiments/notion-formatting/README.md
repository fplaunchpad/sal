# Offline bold-formatting source oracle

Download the hash-pinned public demo once, then run from the repository root:

```sh
python3 artifact/paper1/scripts/reproduce-notion.py --download /tmp/notion-formatting-sources
python3 experiments/notion-formatting/run.py --cache /tmp/notion-formatting-sources
```

The runner requires the seven cached modules pinned by
`experiments/notion-oracle/sources.json`; it has no network or fetch path. It
checks every source hash, copies modules into temporary workspaces with the
existing merge-design helper, and runs the unmodified demo and corrected merge
design. It checks the cache again afterwards. Only JSON results in this directory
are written persistently. The cached source remains unchanged.

`probes.mjs` has hand-derived positive expectations and a distinct rejected
output for each probe. It tests endpoint insertion growth, tombstone bounds,
split/merge mark preservation, concurrent insertion, transaction-level toggle
preparation over multiple instances and repeated instance segments, Lamport
arbitration, missing/reversed anchors, and subtree-exit `after` anchors. It also
captures the precise N-002 and N-003 failures with their archives and source
operations. The existing gate independently reissues those cases and its passing
N-002 control.

`candidate-planner.mjs` is a separate proposed preparation algorithm: it groups
selected stable IDs into maximal runs in global instance visible order, then
emits the same before-next-visible intervals. `candidate-probes.mjs` applies its
transactions as ordinary source operations in temporary workspaces and checks
current exact coverage plus boundary-growth controls. It does not replace
`Replica.toggleBold`. Its 21 source-applied cases per variant distinguish
N-002/N-003 correction from unchanged source behaviour; a bounded gate checks all
304 nonempty four-ID selections, their permutations, and unselected deletion
masks with add/remove values. These finite checks are not a refinement proof.

`fixture-types.d.ts` describes the exported JSON interface. Per-instance records
contain tagged scalar IDs, full RGA preorder including split markers and
tombstones, scalar entry/exit positions, sorted annotation operations, resolved
anchor positions, covered preorder indices, and resolved visible bold flags.
Replica records also carry the original source-compatible transactions and
display. These exports are inputs to an independent formal oracle; they are not
a proof that an importer or a later model faithfully implements the source.

## Atomic-selection obstruction

The candidate's immediate coverage does not imply atomic formatting under
concurrency. A source-issued trace splits one selection into two intervals
whose priorities straddle a concurrent removal. The actual result is `10011`
on character identities `abcde`; every atomic ordering keeps `b` and `d`
equally formatted, so none explains that result.

```sh
python3 experiments/notion-formatting/run-atomic-fracture.py --cache /tmp/notion-formatting-sources
lake build Sal.MRDTs.Metatheory.NotionFormattingLedger
```

[`results/atomic-fracture.json`](results/atomic-fracture.json) records complete
requests, transactions, both receipt orders and all six atomic formatting
orders. The runner uses the separate candidate planner with the source's
annotation operations and clock reservations, under both corrected merge
variants. Harmless empty-block requests align clocks; no annotation IDs or
toggle verdicts are forged. This is an obstruction to the proposed repair,
not a new original-demo bug. The Lean witness independently checks a reachable
typed caller, fresh allocations and the actual finite-carrier query; its
bootstrap correspondence to JavaScript is manual.

See [`docs/notion-formatting-atomicity.md`](../../docs/notion-formatting-atomicity.md)
for the invariant excluding all atomic histories and the proposed shared
transaction-priority repair.

## Repaired shared-priority protocol

The separate repaired path now has a positive
[rich-text protocol certificate](../../docs/notion-rich-text-certificate.md).
`atomic-priority-patch.py` changes only temporary source copies: annotation
arbitration uses the enclosing transaction ID while segment IDs stay distinct.
`atomic-priority-adapter.mjs` uses the unchanged maximal-run planner and actual
source allocation. The pinned source's `toggleBold` body stays unchanged.

```sh
sh scripts/check-notion-rich-text.sh /tmp/notion-formatting-sources
```

This checks the Lean ledger, original N-002/N-003 cases, old per-segment
obstruction and repaired source tests. Logs and complete fresh results are
written to a new temporary directory. For just the repaired source tests:

```sh
python3 experiments/notion-formatting/run-atomic-priority.py --cache /tmp/notion-formatting-sources
```

The saved [repaired results](results/atomic-priority.json) include 44 directed
positive/negative controls per merge variant. The generated gate exhausts all
30 Boolean patterns of lengths one to four, every nonempty selected interval
and insertion gap, both session orders, equal and unequal clock priorities,
and both delivery orders. A separate direct character/gap machine checks
12,384 base cases and 70,992 later insertions probing every resulting gap:
83,376 paired controls per variant, with zero discarded cases. The old
per-segment compiler is run as a failing control. Expected selection verdicts
and flags are independently calculated.

These finite source checks validate the temporary repair; the general result
is the separate Lean protocol theorem. Neither establishes JavaScript
extraction or production Notion equivalence.

See `docs/notion-formatting-design.md` for the research question, exact source
claims, counterexamples, and the independent model. This experiment leaves
the pinned source unchanged. Typed planner proofs and the separate executable
integration are documented in the research note; runtime checks alone
establish no protocol-level guarantee.
