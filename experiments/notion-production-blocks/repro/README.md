# Reproductions: production Notion block layer

One self-contained script per defect class found by the ra-pbt search over
the production block-editing code ([the note](../../../docs/notion-production-blocks.md)).
Each script imports only the exported production library, named by
`NOTION_PRODUCTION_LIBRARY`, runs the defect schedule and a control that
changes one ingredient, and exits 0 when the defect reproduces and the
control behaves as expected. The library is Notion's proprietary code and
lives outside this repository; see the note for how to obtain and verify it.

```sh
export NOTION_PRODUCTION_LIBRARY=/path/to/exported/library
node ra-pbt/instances/notion-production-blocks/verify-sources.js
for f in experiments/notion-production-blocks/repro/*.mjs; do node "$f" || echo "FAILED $f"; done
```

| Script | Class | Seed | Schedule | Expected | Observed | Control |
| --- | --- | --- | --- | --- | --- | --- |
| [label-divergence.mjs](label-divergence.mjs) | A record is rejected because slice labels depend on the order of concurrent splits | `abc` | A splits at 1; B splits at 2; A types X at 0 of block 1; exchange | `a \| Xb \| c` at both | A `a \| Xb \| c`, B `a \| b \| c`; B rejects the insertion | B receives A's split before splitting: both `a \| Xb \| c` |
| [past-boundary.mjs](past-boundary.mjs) | A split (or an insertion) is rejected because its new item integrates past a concurrent merge marker | `a \| b \| c` | A splits b at 0 twice; B merges b; exchange | `a \| empty \| b \| c` at both | A `a \| empty \| b \| c`, B `a \| b \| c`; B rejects the second split | One split: both `a \| b \| c` |
| [concurrent-move.mjs](concurrent-move.mjs) | Two concurrent splits move the same slice; the last move applied wins | `a \| b \| c` | B merges b, A receives it; B splits `ab` at 1 and merges the new block back; A splits `ab` at 1; exchange | the same document at both | A `ab \| empty \| c`, B `a \| b \| c` | A sees B's records first: both `a \| b \| c` |
| [stale-merge.mjs](stale-merge.mjs) | A late duplicate merge of a removed block moves its text again | `a \| b \| c` | A merges c; B merges c, splits `bc` at 1; exchange | `a \| b \| c` at both | `a \| bc \| empty` at both | B does not merge c: both `a \| b \| c` |
| [removed-anchor.mjs](removed-anchor.mjs) | A block listed after a removed block goes to the end of the page | `ab \| cd` | A splits cd at 0, merges the empty block; B splits cd at 0, creates a block after block 1; B's records reach A | `ab \| empty \| empty \| cd` | `ab \| empty \| cd \| empty` | A does not merge: `ab \| empty \| empty \| empty \| cd` |
| [order-mismatch.mjs](order-mismatch.mjs) | Block order follows application order, text division follows identifiers | `a` | A creates a block after block 0, types Y at 0 of block 0; B splits block 0 at 0; A's records reach B | one of `empty \| Ya \| empty`, `Y \| empty \| a`, `Y \| a \| empty` | `empty \| empty \| Ya` | A sees the split first: `Y \| empty \| a` |

"Expected" is the result of some order of the requests under the block
specification (`ra-pbt/instances/notion-production-blocks/spec.js`), derived
by hand in each script's header. Block creation and removal, record transport
and the fixture stores are the harness's; the operations are emitted by the
original request builders and applied by the shipped record handlers. These
are findings about the extracted editing code under the harness's delivery,
not observations of the live service.
