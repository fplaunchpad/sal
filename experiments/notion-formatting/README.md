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

See `docs/notion-formatting-design.md` for the research question, exact source
claims, counterexamples, and staged integration work. This experiment changes no
formatting implementation and establishes no protocol-level guarantee.
