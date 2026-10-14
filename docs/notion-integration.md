# Integration report for the paper session

Research branch: `research/notion-mrdt`, isolated from `paper1` at `3dcc537`.
The original working tree, Overleaf manuscript, formal-reference PDF and public
Site were not edited. No GC changes or downloaded Notion sources are included.

The new [research record](notion-research.md) documents a negative result for
the unchanged published demo's unrestricted local editing contract: honest
split/merge histories make a split-at-zero leave part of the suffix behind,
and make bolding a reversed two-character block format neither character.
The pinned executable traces reproduce these failures. Lean checks restricted
semantic counterparts, not JavaScript source equivalence.

The split/insert/delete-only result remains incomplete. The independent
JavaScript slot specification passes 4,500 bounded comparisons; 18,053 local
request checks also pass on its separate reachable-state corpus. Lean proves
retained-identity split/delete laws and a generic finite-store five-VC
convergence shell, including ordinary and recursive bases. No Notion document
history certificate or universal client-preparation theorem is claimed.

The branch is suitable as reproducible research evidence. It must not add
Notion to the paper's verified datatype inventory. Any paper discussion should
state the demo/production boundary and distinguish the full-contract negative
result from the open core milestone. No manuscript edits are proposed here.

Independent Sol6.1 source/oracle/proof review is recorded in
[notion-review.md](notion-review.md); its minimizer and projection-comment
findings were corrected. Run `scripts/check-notion-research.sh` for the three
Lean modules, directed oracle, minimized regressions, independent model and
mutation controls. `scripts/check-mrdt-refactor.sh` remains the required
production gate. The research gate passed: three Lean modules, 575 directed
cases, four regression records, 4,500 differential comparisons, two mutation
checks and two semantic controls. The production gate passed with 3,694 Lean
jobs, 18 public contracts, 187 runtime tests and 569 benchmark records. The exploratory merge-enabled `--reachable` command exits 1
when it rediscovers the failure; the permanent regression gate exits 0 when
that counterexample and its positive controls reproduce.

Only `PRIORITIZED_REMAINING_WORK.md` records outstanding development work.
