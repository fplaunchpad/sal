# Every Version Tells a Story — supporting artifact

This is a standalone Lean source package for the paper's framework, MRDT
implementations and sequential specifications. It also includes reproducible
experiments for five bugs in Notion's public CRDT demo and the data and scripts
behind the implementation table. No development checkout, Git history, browser,
Overleaf account or private credentials are needed.

Start with [the numbered paper-to-source index](docs/paper-index.md),
[the claim-to-theorem map](docs/claims-and-theorems.md) and
[the datatype guide](docs/datatypes.md). The package uses neutral module names and omits author identities, project repository
links and project revision identifiers. Renaming preserves proof structure and source
line numbers; `provenance.json` records the packaged source hashes. The claim map explains the assumptions used by each proof family.

## Quick start: check the sources and proofs

Requirements: Python 3, Git, and Lean's `elan`/Lake tools. `lean-toolchain` pins
Lean 4.28.0; `lake-manifest.json` pins Mathlib and its dependencies.
The package contains the Lean sources. The compiler and pinned dependencies
are acquired separately.
Initial toolchain/package/cache acquisition needs network access. Do not run
`lake update`: use the supplied dependency lockfile.

From this directory:

```sh
python3 scripts/check-manifest.py
elan toolchain install leanprover/lean4:v4.28.0
lake exe cache get
sh scripts/check.sh
```

`check-manifest.py` verifies the shipped files, the 444 measured source hashes,
and local Lean imports. It also rejects unexpected files outside the documented
build/output directories (`.lake/`, `results/`, `vendor/notion/`, and Python
bytecode caches). `check.sh` builds `Sal.Artifact.Guide` and audits the
252 selected declarations and all their transitive axiom dependencies. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted; a `sorry` in any
of these dependency chains fails the audit.

This audit does not cover every declaration compiled by the build. In
particular, other concrete examples use `native_decide`; compiling them is
separate from auditing the 252 selected declarations. Expect `PAPER_CHECKED`
records and a successful build. Repeated builds may reuse checked outputs.

For an annotated reading path, open
[Sal/Artifact/Guide.lean](Sal/Artifact/Guide.lean). Its comments connect the
paper definitions and theorems to checked declarations. The build entry point is
[Sal/Artifact/Paper.lean](Sal/Artifact/Paper.lean). It imports the paper's source
closure, not the repository-wide development ledger. Inspect theorem types in
an editor with Lean support to see the exact event, state and issuance premises.
Some required AegisSheet metadata helpers reside in GC-named modules; those
files are retained as build dependencies. GC results and experiments
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

The second command is offline. A successful run reports **five reproduced
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
entry-point imports, neutral module names and revision lookup. Their support modules contain the
same case descriptions, Lean audit command and comment stripper, with
repository-only audit runners omitted. These changes are recorded in
`provenance.json`.

Counts use nonblank, noncomment lines in complete declaration ranges, with
roles assigned once per row. Proof columns include supporting definitions and
lemmas. Shared framework code is excluded from datatype rows; dependencies
shared between rows are counted in each row. Row sums are not repository totals.
These counts include supporting declarations, not just handwritten proof bodies.
There are 24 paper rows covering 26 implementations; the three grow-only
set representations share one row. [The datatype guide](docs/datatypes.md)
explains the row selection and the issuance/execution columns.

Table citation keys use neutral aliases.
[table-references.bib](measurements/table-references.bib) identifies the cited
works by title, year and DOI or URL; `CertifiedMRDTs2022` names the 2022
paper *Certified mergeable replicated data types*.

## Recorded validation

[validation.json](validation.json) records the checked environment and results:
a clean build of all supplied Lean sources with 252 root audits, an exact match
of all 24 table rows and 444 measured source hashes, the generic theorem counts,
and a fresh download followed by offline reproduction of the five demo bugs.
The clean build reused the pinned third-party Lake package cache; it did not
reuse any compiled project output. Full initial dependency acquisition was not part
of this validation run.

## Contents and scope

| Path | Contents |
| --- | --- |
| `Sal/` | Lean operational semantics, metatheory, automation, selected implementations/specifications and proofs |
| `Sal/Artifact/Paper.lean` | Paper-specific build and axiom-audit entry point |
| `docs/` | Numbered paper index, claim map, datatype guide and Notion reproduction instructions |
| `measurements/` | Paper table, exact selected roots, source hashes and counting scripts |
| `notion/` | First-party regression fixtures, independent local specification, pinned source manifest and recorded observations |
| `scripts/` | Integrity/build checks and Notion runner; counting-script support modules |
| `manifest.json`, `provenance.json` | File integrity and packaging changes |

The two `scripts/*paper1-automation*.py` modules support the counting scripts.
The [claim map](docs/claims-and-theorems.md) states the proof assumptions and
distinguishes the Notion model from the external demo reproductions.
