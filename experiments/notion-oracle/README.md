# Notion demo: specification-discovery probes

These probes exercise the readable JavaScript modules served by Notion's
[official interactive demo](https://www.notion.com/front-static/crdt-demo/index.html?embed=1),
linked from its [CRDT article](https://www.notion.com/blog/how-notion-handles-concurrent-editing-with-crdts).
They are observations for learning candidate specifications, not a formal
verification of Notion's production implementation. No production-code
correspondence or open-source licence has been established. Third-party source
is not committed here; `sources.json` records its URLs and SHA-256 hashes.

Run `python3 experiments/notion-oracle/run.py` with Node and curl installed.
The runner fetches and checks the snapshot, then prints literal transactions,
local views and views after exchange. `observations.jsonl` records the first
run on 14 October 2026, independently reproduced. Outputs are not used as
hand-derived expected values for Lean SPOTs.

Starting with `abcd`, split at index 2 concurrently with the following edit:

| Edit | Split / edit session | Observed blocks |
|---|---|---|
| Insert X at 2 | A / B | abX · cd |
| Insert X at 2 | B / A | ab · Xcd |
| Insert X at 1 | A / B | aXb · cd |
| Insert X at 3 | A / B | ab · cXd |
| Delete original range [1,3) | A / B | a · d |

Both issuing replicas after exchange and fresh receivers accepting the two
transactions in opposite orders agree in each probe. The demo reconstructs
documents by sorting transactions before replay, so this is a limited finite
check, not an independent convergence proof.

The first pair refutes always-left and always-right rules for concurrent edits
at a split boundary. A candidate explanation is an ID-ordered split marker;
deletion appears to retain the identities selected before splitting. Further
traces should test concurrent splits, split/merge, and formatting across the
boundary. The sequential specification must be stated independently, then
challenged with these traces and proved against a faithful MRDT model.
