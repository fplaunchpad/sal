# Bounded testing of replicated implementations

The testing support checks executed implementations against independent
sequential specifications. Its findings are bounded experiments with named
versions and model choices. Passing runs do not prove universal laws or verify
Yjs, Automerge, Loro, the public Notion demo, or this handwritten runtime.
No garbage-collection result is claimed here.

The end-to-end witness search checks a linear extension of the integrated
records' full causal dependencies. It has no implementation `rc`/`lo_E` hook
and does not use `spec.rc`. It is a bounded causal-history conformance check,
not a generic checker of the paper's implementation-dependent order. A missing
causal witness alone therefore does not refute the paper's criterion.
Standalone concurrent-library counterexamples compare the measured outputs
with their explicitly stated sequential specifications. The separate law
layer transcribes VC1–VC5 and the conflict-relation conditions, with bounded
state generation and the inconclusive-result distinctions described below.

## Offline core checks

Python 3, Node.js 18 or newer, and npm are required. From the artifact root:

```sh
python3 scripts/check-pbt.py
```

This runs the dependency-free `ra-pbt` suite, the selected runtime tests, and
independent specification tests. The runtime regression
`runtime/test/ingest.test.js` covers binary deltas computed against a stale
receiver summary: a repeated add followed by its removal must leave the set
empty, retain the add's canonical local node, and add nothing on replay. It
also covers implicit content ids, parent back-references, merge histories,
and endpoint validation in both ingest implementations. The exported runtime
contains the fix; the earlier adapter's filtering of known commits is not
needed for the runtime to accept overlapping deltas.

Eight portable runtime test files are supplied. The rest of the development's
runtime suite, deployment demos, packaging gates and benchmarks are omitted;
the standalone package does not claim to reproduce that larger test count.

Results and command logs go to `results/pbt/`. These generated files, allowed
dependency installations and experiment output directories are excluded from
the integrity check; shipped sources and lockfiles remain checked.

## Pinned external implementations

Install the exact locked releases and run the asserted regressions:

```sh
python3 scripts/check-pbt.py --install
python3 scripts/check-pbt.py --external
```

The first command needs network access for npm acquisition; the second is
offline. Installation uses `npm ci --ignore-scripts`. Each instance verifies
the installed version, lockfile URL/integrity and selected executable file
digests against its `sources.json`, both before and after the regressions.
The pinned targets are Yjs 13.6.31, Automerge 3.5.0 and Loro 1.17.1. These
third-party packages are acquired separately, not redistributed in the bundle.
All findings are relative to the specifications supplied with the adapters.
Automerge includes distinct anchor and marker readings; Loro's position and
attribute policies are explicit parameters. A mismatch under one such reading
is not an unconditional violation of every possible rich-text specification.

Self-contained reproduction scripts and npm lockfiles are also supplied in
each `experiments/*-oracle/repro/`. For example:

```sh
cd experiments/yjs-oracle/repro
npm ci --ignore-scripts --no-audit --no-fund
node run-all.mjs
```

Individual reproduction scripts intentionally exit nonzero when a defect is
observed; `run-all.mjs` is an informational version comparison, not an automated
pass/fail gate. The asserted adapter regressions above are the checked runner.
The Yjs `repro/v14/` variant pins `@y/y` 14.0.0-rc.29 separately; run its own
`npm ci --ignore-scripts` before `node run-all.mjs`. It is not the pinned
13.6.31 target of the adapter campaigns or the Lean counterparts below.

## The public Notion demo and older corrected model

The PBT instance requires the original seven-module manifest at
`experiments/notion-oracle/sources.json` and the exact patcher at
`experiments/notion-merge-design/design-patch/patch.py`; both are supplied.
Acquire the hash-pinned demo once, then run without network access:

```sh
python3 scripts/reproduce-notion.py --download /tmp/notion-public-demo
python3 scripts/check-pbt.py --notion-cache /tmp/notion-public-demo
```

The runner verifies the cache and produces the source variants under
`results/notion-pbt-sources/`. This checks `demo` and the older `anchor-absorb`
merge design. That design is separate from the current rich Lean model and
does not certify a replacement implementation. In particular, agreement on
sampled structural merges does not fix the demo's independent formatting
problems. The source licence and production correspondence of the public
educational demo remain unconfirmed; only source acquisition is automated.

To inspect the current law reporting directly:

```sh
NOTION_RA_PBT_SOURCES="$PWD/results/notion-pbt-sources" \
  node experiments/notion-ra-pbt/run.mjs --mode laws --model anchor-absorb \
  --texts '["x"]' --profile structure --observation bag --seed 1 \
  --trials 20 --size 8 --output results/notion-laws.json
```

Law results distinguish `pass`, `fail`, `inconclusive`, `vacuous`, and
`not-applicable`. The law CLI exits 0 for checked passes plus inapplicable
properties, 1 for a counterexample, and 2 for unresolved/vacuous results.
A finite commutation pool's failure to find a witness is inconclusive; a
bounded specification search may also be inconclusive. Inspect status and
the checked, inconclusive, vacuous and skipped counters. Do not infer a pass
from an empty failure list. These distinctions are exercised by the core suite.

## Checked semantic counterparts and recorded evidence

Two additional Lean modules are imported and their selected roots audited:

| Module under `Sal/MRDTs/Instances/` | Checked scope |
| --- | --- |
| `YjsMarkerCounterexample.lean` | Fixed measured item lists and a one-key marker renderer give a merged result different from both sequential range-format orders; explicit closer controls explain the difference. |
| `YjsDeleteSetCounterexample.lean` | A restricted delivery predicate admits the specified delete-only update before a missing causal predecessor; fixed item lists produce a view outside the three closed versions, with a late-arrival control. |

Their checked roots use `by decide`; the generated `Sal/Artifact/Paper.lean`
audits their full axiom closures against the same standard-axiom allowance as
the other artifact roots. They do not formalize Yjs's integration algorithm,
extract its source, or establish correspondence with the JavaScript library.
The JS source verifiers, hand-derived expected outputs and negative companions
provide separate experimental evidence.

`recorded/pbt/` preserves top-level experiment JSON evidence. For external
campaign summaries it retains aggregate counters and every stored shrunk
representative, removing the large per-trial record lists. Raw campaign
subdirectories, console logs, redundant no-failure dumps, downloaded packages,
and identifying posted-report drafts/history are omitted. `selection.json`
records the input hashes and transformation. Search and campaign scripts remain
available to generate fresh raw output; run them from their experiment directory
and consult their command headers. Search/replay may exit 1 when they find or
reproduce a counterexample, which is different from a broken regression runner.

Recorded Notion law files predate the corrected inconclusive-status reporting
and are historical observations. Their old `pass` booleans must not be used as
checked-law verdicts; rerun the current law CLI for statuses. The counts and
representative schedules are retained for traceability, not relabelled as new
measurements. Recorded evidence is not a claim that this newly exported bundle
has already completed a fresh combined Lean/external-dependency build; follow
the commands above and `scripts/check.sh` to validate the current snapshot.
