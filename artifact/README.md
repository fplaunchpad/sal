# Paper artifact packaging

`paper1/` contains the maintained documentation and runner templates; their
source links resolve inside the exported bundle. Export a
standalone source tree and archive from the checked paper measurements:

```sh
python3 artifact/export-paper1.py --out /tmp/paper-artifact --archive
```

The exporter refuses an existing output directory and changed measured sources.
It copies the paper's measured Lean files and their complete local import closure,
adds a paper-specific build/axiom-audit entry point, and includes the table
measurement and public-demo bug reproductions. It never copies `.git`, local
credentials, `_references`, caches, or unrelated working files. Required
GC-named dependencies are retained; no GC result is an artifact claim.

It also includes the bounded `ra-pbt` harness and adapters, Yjs/Automerge/Loro
and older Notion PBT reproductions, locked acquisition manifests, compact
recorded evidence, the original Notion manifest and exact design patcher, and
current runtime source with eight portable test files. Two Yjs semantic
counterexamples are added to the checked Lean roots; this does not verify the
external libraries or their integration algorithms. Installed packages, raw
campaign dumps/logs and identifying posted-report drafts/history are omitted.
The standalone `scripts/check-pbt.py` runner separates offline core checks from
explicit third-party acquisition. See its exported reproduction guide.

The result has its own Lake configuration, pinned dependencies, documented
commands and file hashes. Third-party Notion demo sources are acquired separately
through a hash-checked downloader. No distribution licence is added or changed.
The export uses neutral project and module names, removes repository revision
identifiers, and checks for author identities and identifying URLs. Archive
owner metadata is cleared. An unused legacy tactic macro and its dependency
are omitted. Original Lean line numbers are preserved for
the numbered paper-to-source index. Exported sources must be rebuilt after renaming.

Do not edit exported Lean files. Make changes in the development, update the
paper's measurement if its sources change, and export again. Validation reports
belong alongside the generated archive. `dist/` is intentionally not committed.
