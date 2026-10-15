# Every Version Tells a Story — supporting artifact

This is a standalone Lean source package for the paper's framework, MRDT
implementations and sequential specifications. It also includes reproducible
experiments for three bugs in Notion's public CRDT demo and the data and scripts
behind the implementation table. No original Sal checkout, Git history, browser,
Overleaf account or private credentials are needed.

Start with [the claim-to-theorem map](docs/claims-and-theorems.md) and
[the datatype guide](docs/datatypes.md). The package preserves the selected
source files unchanged; `provenance.json` records their hashes and the source
revision. The proofs cover the precise assumptions in their Lean statements.
The different certified proof families are explained in the map, rather than
presented as instances of one unrestricted theorem.

## Quick start: check the sources and proofs

Requirements: Python 3, Git, and Lean's `elan`/Lake tools. `lean-toolchain` pins
Lean 4.28.0; `lake-manifest.json` pins Mathlib, Blaster and their dependencies.
The package contains our Lean sources, not the compiler or third-party packages.
Initial toolchain/package/cache acquisition needs network access. Do not run
`lake update`: use the supplied dependency lockfile.

From this directory:

```sh
python3 scripts/check-manifest.py
elan toolchain install leanprover/lean4:v4.28.0
lake exe cache get
sh scripts/check.sh
```

`check-manifest.py` verifies the shipped files, the 444 source hashes used by
the table, and every local Lean import. `check.sh` then builds
`Sal.Artifact.Paper`, compiling the included proofs and checking every selected
root for dependencies on axioms. The only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`; an unfinished proof fails this audit.
Expect `PAPER_CHECKED` records and a successful Lake build. On a repeated build
Lake may reuse the checked outputs rather than print every record again.

The artifact-specific entry point is
[Sal/Artifact/Paper.lean](Sal/Artifact/Paper.lean). It imports the paper's source
closure, not the repository-wide development ledger. Inspect theorem types in
an editor with Lean support to see the exact event, state and issuance premises.
Some required AegisSheet metadata helpers reside in GC-named modules; those
files are retained as unchanged build dependencies. GC results and experiments
are outside this artifact's claims.

## Reproduce the Notion issues

Offline execution needs Python 3 and Node.js 18 or newer; source acquisition
also needs curl. The public demo's
seven JavaScript modules are downloaded separately and checked against pinned
SHA-256 hashes; they are not redistributed here.

```sh
python3 scripts/reproduce-notion.py --download /tmp/sal-notion-demo
python3 scripts/reproduce-notion.py --vendor-cache /tmp/sal-notion-demo
```

The second command is offline. A successful run reports **three reproduced
bugs and one passing control**; success means the bugs are present, not fixed.
[The reproduction guide](docs/notion-reproduction.md) gives the request
sequences, expected/observed results, source boundaries and Lean counterparts.
The findings concern the pinned public educational demo, not Notion production.
Saved observations are in `notion/recorded-observations.jsonl`; the command
executes the requests afresh rather than returning this file.

## Reproduce the paper's code counts

After the Lean build, run:

```sh
python3 measurements/measure.py --repo . --out /tmp/sal-instance-counts
python3 measurements/measure_metatheory.py --repo . --out /tmp/sal-metatheory-counts
python3 scripts/compare-counts.py --instances /tmp/sal-instance-counts \
  --metatheory /tmp/sal-metatheory-counts
```

Compare the generated `measurement.json` with
`measurements/current-counts.json`, and `sal-metatheory-count.json` with
`measurements/metatheory-counts.json`. The checked-in files preserve the
paper's measurement; output filenames and metadata formats differ, while
per-row counts and the selected generic theorem totals can be compared.
The counting scripts differ from the repository scripts only in their artifact
entry-point imports and revision lookup. Their support modules contain the
unchanged case descriptions, Lean audit command and comment stripper, with
repository-only audit runners omitted. These changes are recorded in
`provenance.json`.

Counts use nonblank, noncomment lines in complete declaration ranges, with
roles assigned once per row. Proof columns include supporting definitions and
lemmas. Shared framework code is excluded from datatype rows; dependencies
shared between rows are counted in each row. Row sums are not repository totals.
These are dependency footprints, not handwritten proof-body sizes or author hours.
There are 24 paper rows covering 26 selected configurations; the three grow-only
set representations share one row. [The datatype guide](docs/datatypes.md)
explains the row selection and the issuance/execution columns.

## Recorded validation

[validation.json](validation.json) records the checked environment and results:
a clean build of all supplied Lean sources with 242 root audits, an exact match
of all 24 table rows and 444 measured source hashes, the generic theorem counts,
and a fresh download followed by offline reproduction of the three demo bugs.
The clean build reused the pinned third-party Lake package cache; it did not
reuse any compiled Sal output. Full initial dependency acquisition was not part
of this validation run.

## Contents and scope

| Path | Contents |
| --- | --- |
| `Sal/` | Lean operational semantics, metatheory, automation, selected implementations/specifications and proofs |
| `Sal/Artifact/Paper.lean` | Paper-specific build and axiom-audit entry point |
| `docs/` | Claim map, datatype guide and Notion reproduction instructions |
| `measurements/` | Paper table, exact selected roots, source hashes and counting scripts |
| `notion/` | First-party regression fixtures, independent local specification, pinned source manifest and recorded observations |
| `scripts/` | Integrity/build checks and Notion runner; counting-script support modules |
| `manifest.json`, `provenance.json` | File integrity, original source revision and packaging changes |

The two `scripts/*paper1-automation*.py` modules supply helpers for the
measurement scripts; use the commands above. The native Notion runtime source is included because it is part
of the paper's measured support, but native compiler/JSON execution is separate
from the mathematical theorem. The theorem map records this boundary.

The package makes no whole-program extraction claim for the public demo or
production Notion. The operation-label transport presents already-certified
configurations with pointwise `ops`; it is not an unrestricted execution theorem
for arbitrary additional operation arguments. See the claim map for the other
specific scope qualifications.
