# Notion production text: experiments

Drives the `ra-pbt` instance `ra-pbt/instances/notion-production-text/`
over the editing code shipped in production Notion clients, at the text
layer of one block (insertion, deletion, bold). The results and their
reading are in `docs/notion-production-text.md`.

## The library

The code is proprietary and is never stored in this repository. It is
exported from the public assets by `experiments/notion-production-client`
of the main tree, into a directory outside the repository:

```sh
P=experiments/notion-production-client # from the repository root
python3 $P/download.py --cache "$CACHE"              # 63 public assets, SHA-256 pinned
NOTION_PRODUCTION_CACHE="$CACHE" npm test --prefix $P  # 19 extraction and replay controls
node $P/extract.mjs "$CACHE" "$LIBRARY"               # the export; must not exist yet
export NOTION_PRODUCTION_LIBRARY="$LIBRARY"
export NOTION_PRODUCTION_CACHE="$CACHE"               # optional: enables the level 2 check
```

`ra-pbt/instances/notion-production-text/verify-sources.js` runs before
and after every command below. Level 1 checks that the export lies outside
the repository and that each of its six files has the SHA-256 pinned in
`ra-pbt/instances/notion-production-text/sources.json` (the export's own
asset manifest among them). Level 2, when `NOTION_PRODUCTION_CACHE` is set,
also checks every asset against the manifest and every one of the 4,335
module bodies against its byte range in its asset.

## Commands

```sh
node spec-tests.mjs                          # 14 hand-derived blocks, each with a not-equal companion
node run.mjs --mode regressions              # 24 predicted verdicts, controls included
node run.mjs --mode search --seed 31 --trials 200 --bold --local inherit --output /tmp/x.json
node run.mjs --mode replay --input results/campaign/bold-both-31.json
node campaign.mjs list                       # the 19 campaign runs
node campaign.mjs run bold-inherit-31        # writes results/campaign/bold-inherit-31.json
node campaign.mjs summarise                  # writes results/campaign.json
node out-of-order.mjs --seed 41 --trials 200 --output results/out-of-order.json
node repro/run-all.mjs                       # the plain-library reproductions
```

Search options: `--bold` adds bold toggles, `--opened true` opens replicas
from another's snapshot, `--partial` delivers single records (the adapter
still delivers causally), `--rule gap|left|both`, `--reading
anchored|interval`, `--local positional|inherit`.

| File | Role |
| --- | --- |
| `spec-tests.mjs` | tests of the specification, independent of the library |
| `regressions.mjs` | hand-derived schedules: Y-001 to Y-005 re-expressed, NT-1 to NT-3, controls for T4 and T5, the causal buffer, identities, source verification, the probe classes |
| `search.mjs` | the ra-pbt campaign loop, returning to the event loop after each trial |
| `run.mjs` | search, replay and regressions |
| `campaign.mjs` | the named runs and their summary |
| `out-of-order.mjs` | the probe without causal buffering (not part of the main claims) |
| `render.mjs` | compact rendering of failures |
| `repro/` | one script per class against the exported library alone |
| `results/` | `campaign/*.json`, `campaign.json`, `out-of-order.json` |

The campaign loop yields to the event loop after every trial because the
shipped code arms millisecond timers (cache expiry in its grapheme
segmentation) that keep a client's module context reachable until they
fire; a loop that never yields holds every client it created.
