# Certification structural-invariant campaign baseline

Captured all 378 Sal Lean source files from the current worktree before this campaign changed production source. `manifest.json` records SHA256 hashes. This includes existing dirty sources and unrelated EfficientORSet GC experiments without editing them.

`cases.json`, `Audit.lean`, and `kernel.log` preserve the complete kernel closure for TreeMove, AegisSheet, the embedded invariant-certified RGA, and native issuance-certified RGA comparison. `prior-production-audit.json` and `freshness.json` establish that all original 119 closure source files were covered by the prior exact-source production build (340 hashes; zero mismatches).

`campaign-measurement.json` is the conservative complete declaration union: 9005 concrete and 6751 shared nonblank/noncomment source lines. Datatype-specific Automation modules are concrete. The descriptor heuristic is secondary; the complete concrete union is the conservative metric.

Run `python3 scripts/measure-paper1-certification-invariants.py` from the repository after rebuilding the final Ledger. Additional instance or generic roots are repeatable `--root` / `--generic-root` arguments. The report includes all declaration kinds, whole changed modules (including retained helpers), whole new modules, and statement/definition review. The concrete metric includes executable/model declarations and must not be described as pure proof lines. No elapsed-effort claim follows from line counts.

To reproduce the baseline build independently, use this directory as an isolated Lake project with the pinned dependency revisions in `lake-manifest.json`, run `lake build Sal.MRDTs.Paper1.Ledger`, then `lake env lean Audit.lean`. Required source files are durable here; no `/tmp` fallback is needed.

Expanded same-endpoint audit also includes changed production sequential correctness bundles and embedded public sequential/chain proofs. These roots were rebuilt in the isolated baseline project with separate outputs; `baseline-rebuild-summary.json` records success, and `freshness.json` verifies the snapshot stayed unchanged. The embedded Paper1 invariant certificate and production independent sequence projection are reported separately.
