# Project notes for agents

- `PRIORITIZED_REMAINING_WORK.md` is the only development task list.
- `Sal/MRDTs/Metatheory/RefactorLedger.lean` is the production theorem ledger.
- Run `scripts/check-mrdt-refactor.sh` before pushing. It builds the Lean ledger,
  rejects historical framework dependencies and unproved production theorems,
  and runs the complete JavaScript runtime suite.
- Historical conditioned, rehoming, Shesha, and emulation experiments are on
  `archive/conditioned-mrdts-2026-08-21`; do not restore them to the production
  tree.
- Keep `README.md` synchronized with the actual branch contents.

- SPOT files (concrete-execution tests) are PASS+FAIL shaped, like good unit
  tests: every SPOT block carries at least one `≠`/`¬` companion pinning the
  tempting degenerate behavior (read constantly true or empty, delete a
  no-op, merge a projection of an input, display echoing the candidate id
  list, the rival design's verdict). Expected values are hand-derived,
  never `#eval`'d from the implementation under test (a self-fulfilling
  oracle). Negatives that need inversion on an inductive relation belong to
  the ReadSide theorem layer, not SPOTs.
