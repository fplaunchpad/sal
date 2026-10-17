# Notion demo correctness campaign

This experiment asks whether a local edit still has its ordinary sequential
meaning after concurrent block restructuring. It exercises the pinned public
demo through valid client requests, then compares each edit with an independent
list specification. The [findings](../../docs/notion-correctness-campaign.md)
record the results and a smaller reproduction of the known split bug.

## Reproduce

Requirements: Python 3 and Node.js. Run from the repository root. Obtain the
seven public demo modules listed in
[sources.json](../notion-oracle/sources.json); the runner verifies every hash
before execution. For example, download a fresh cache with:

```sh
python3 - <<'PY'
import json, hashlib, urllib.request
from pathlib import Path
cache = Path('/tmp/notion-correctness-cache')
cache.mkdir(exist_ok=True)
for m in json.loads(Path('experiments/notion-oracle/sources.json').read_text())['modules']:
    data = urllib.request.urlopen(m['url']).read()
    assert hashlib.sha256(data).hexdigest() == m['sha256'], m['file']
    (cache / m['file']).write_bytes(data)
PY
```

Subsequent runs are offline. Output paths must be new files.

```sh
# The smaller split regression, plus all original regressions and controls.
python3 experiments/notion-correctness/run.py --cache /tmp/notion-correctness-cache \
  --mode regressions --output /tmp/notion-regressions.json

# Generate histories, retain every failing probe, minimise a representative
# of each symptom, and check reversed/repeated receipt of each tested archive.
python3 experiments/notion-correctness/run.py --cache /tmp/notion-correctness-cache \
  --mode search --seed 17002 --trials 250 --output /tmp/notion-search-17002.json
python3 experiments/notion-correctness/run.py --cache /tmp/notion-correctness-cache \
  --mode search --seed 17005 --trials 100 --output /tmp/notion-search-17005.json

# Sequential controls and split/merge-only conservation checks.
python3 experiments/notion-correctness/run.py --cache /tmp/notion-correctness-cache \
  --mode sequential --seed 17004 --trials 60 --output /tmp/notion-sequential.json
python3 experiments/notion-correctness/run.py --cache /tmp/notion-correctness-cache \
  --mode structural --output /tmp/notion-structural.json

# Reproduce saved minimal representatives and diagnose every saved failure.
python3 experiments/notion-correctness/run.py --cache /tmp/notion-correctness-cache \
  --mode replay --input experiments/notion-correctness/results/concurrent-17005.json \
  --output /tmp/notion-replay.json
python3 experiments/notion-correctness/run.py --cache /tmp/notion-correctness-cache \
  --mode classify --input experiments/notion-correctness/results/concurrent-17005.json \
  --output /tmp/notion-classification.json
```

Persistent replicas with partial causal delivery, and the two text-loss
reproductions found there (N-004 and N-005 in
[the bug catalogue](../../docs/notion-bugs.md)):

```sh
python3 experiments/notion-correctness/network-run.py --cache /tmp/notion-correctness-cache \
  --seed 27002 --trials 100 --steps 80 --output /tmp/notion-network-27002.json
python3 experiments/notion-correctness/network-run.py --cache /tmp/notion-correctness-cache \
  --input experiments/notion-correctness/results/network-loss-diagnosis.json \
  --diagnose --output /tmp/notion-network-diagnosis.json
python3 experiments/notion-correctness/offline-run.py --cache /tmp/notion-correctness-cache \
  --mode structural --seed 17102 --trials 12 --steps 110 --output /tmp/notion-offline-17102.json
python3 experiments/notion-correctness/offline-run.py --cache /tmp/notion-correctness-cache \
  --mode regression --output /tmp/notion-offline-regression.json
```

`network-run.py` runs `network-controls.mjs` first; its final block asserts the
five-request document loss. The permanent copies of both regressions are in
[../notion-oracle/regressions.mjs](../notion-oracle/regressions.mjs).

Exit success means the experiment ran and its controls passed; known bugs are
expected to reproduce. Search failures appear under `counts.failures` and
`failureStates`; `findings` holds the minimised representatives. In `classify`
output, `findings` instead lists failures not explained by the tested root-cause
predictions. An empty classification list does **not** mean no bugs were found.
`--mode minimize --input FILE` repeats shrinking and replay on representatives.

## How the checks work

- [campaign.mjs](campaign.mjs) enumerates paired splits and subsequent block
  merges, then generates ten rounds per trial with two requests per branch.
  Concurrent trials use two branches, or three every fourth trial; sequential
  trials use one. Every branch has a distinct session and starts with the
  preceding round's complete causal archive. Seed documents cycle through
  `abc`, `ab | cd`, and `a | b | c`.
- Every tested state is probed with all insertion/split positions, all nonempty
  deletion/bold intervals, and every available merge into the preceding block.
  Insertions use `X`. States with more than nine blocks or a block longer than
  ten characters are counted as skipped; history generation continues.
- [positional-spec.mjs](../notion-oracle/positional-spec.mjs) imports no demo
  code. It specifies local edits on displayed lists. Insertion compares text
  only because formatting inheritance is unspecified here. Other edits compare
  text and bold flags. This does not require concurrent numeric positions to
  have a sequential interpretation.
- [campaign-lib.mjs](campaign-lib.mjs) validates requests, replays histories and
  shrinks representative failures. It removes setup requests, seed blocks or
  characters, and reduces block/position parameters. It preserves the symptom
  and rejects invalid histories. A fixed point under these reductions is not
  a proof of global minimality. All failing probes remain available even though
  only one representative per symptom per run is minimised.
- [classify.mjs](classify.mjs) checks source-state explanations for every saved
  failure: splitting moves a structural subtree, while formatting follows
  intervals in underlying text-instance order. This diagnostic deliberately
  depends on source structure; it is separate from the independent edit oracle.
- [structural.mjs](structural.mjs) uses fixed seed 17003 and 100 trials of ten
  rounds with three branches and two split/merge requests each. It checks
  character conservation at each join and probes local splits/merges. It saves
  one representative per symptom, not every failed probe.
- [controls.mjs](controls.mjs) checks hand-derived list edits, formatting
  preservation and invalid bounds. [regressions.mjs](regressions.mjs) pins both
  the six-request split failure and a successful edit on the same displayed
  text reached without concurrent restructuring. Every invocation also runs
  the three original bug regressions and their passing control.

## Formal evidence

```sh
lake build Sal.MRDTs.Instances.NotionFormattingCounterexample \
  Sal.MRDTs.Instances.NotionSplitSpec
```

These existing Lean files prove restricted semantic counterparts of the split
and interval failures. They do not verify execution of the JavaScript traces.
This campaign found variants of known problems, so it adds executable evidence
and controls without adding redundant Lean examples or changing paper claims.
Its scope is correctness of the public demo; it establishes no correspondence
with Notion's production editor.
