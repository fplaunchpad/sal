# Reproductions on the exported production library

Each script imports only the exported library (`common.mjs` loads
`vendor/notion-production/index.mjs` (or `$NOTION_PRODUCTION_LIBRARY/index.mjs`), Notion's code under its own notice
written by `experiments/notion-production-client/extract.mjs`) and runs two
or three in-process clients with explicit delivery. Each prints its expected
outcome next to the observed one, includes a control that changes one
ingredient, and exits 0 when every expectation holds.

```sh
export NOTION_PRODUCTION_LIBRARY=/path/to/a/fresh/export   # optional
node experiments/notion-production-text/repro/run-all.mjs
```

| Script | Class | Shape | Observed | Control | Status |
| --- | --- | --- | --- | --- | --- |
| `NT-1.mjs` | NT-1 | one replica: `d`, bold it, type `e` after it | `d* e*` (positional semantics: `d* e`) | type `e` before `d`: `e d*` | specification artefact: the positional request semantics has no inheritance rule |
| `NT-2.mjs` | NT-2 | `s1` types `c`, then `f` before it; `s2` types `x` into an empty block | `f x c` on both | `x` typed after `c` arrived: `x f c` | specification result: refutes the two-sided list rule |
| `NT-3.mjs` | NT-3 | `a`; one replica bolds it while the other types a plain `h` after it, in both session orders | `a* h*` on both, either order | `h` typed before `a`: `h a*` | specification artefact of the interval reading; admitted by the anchored reading |
| `P-1.mjs` | P-1 | a deletion delivered before the insertion it deletes | `a` stays visible on the receiver, no error | causal order: empty | outside the delivery contract (deliver after causal predecessors) |
| `P-2.mjs` | P-2 | a bold delivered before the insertion of its anchor | refused with `Unable to apply annotation operation due to start missing` | redelivered after the insertion: `a*` | outside the delivery contract; recoverable by redelivery |
| `P-3.mjs` | P-3 | an insertion delivered before its origin's insertion, the bold and the deletion of a predecessor | backfilled from `prevItems`; `b* z*` before and after the rest arrives | causal order: `b* z*` | the shipped out-of-order mechanism; converges |

`x*` is a bold `x`. Ids are `[session, counter]`; sessions are `s1`, `s2`,
`s3`, and the counter is a Lamport clock, compared before the session.
