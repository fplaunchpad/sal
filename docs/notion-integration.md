# Integration report for the paper session

Research branch: `research/notion-mrdt`, isolated from `paper1` at `3dcc537`.
The original working tree, Overleaf manuscript, formal-reference PDF and public
Site were not edited. No GC changes or downloaded Notion sources are included.

The unchanged published demo fails the full ordinary local editing contract.
Honest split/merge histories make split-at-zero leave part of the suffix behind,
and make bolding a reversed two-character block format neither character.
Pinned executable regressions and restricted kernel-checked semantic counterparts
preserve these findings. They concern the educational demo; production-source
correspondence is not established.
The [permanent bug catalogue](notion-bugs.md) records N-001 (split suffix),
N-002 (selected bold missed), and N-003 (unselected bold in another block),
with literal traces, reproduction commands and minimization limits.

The core split/insert/delete milestone remains open, with a more substantial
checked intermediate result:

- `NotionCoreSpec` defines the independent block/retained-slot machine and proves
  universal local insertion, deletion and split preparation effects.
- `NotionCoreInvariant` derives structural well-formedness from admitted
  executions and proves progress separately. Its guards concern fresh names,
  existing anchors and empty split targets, not desired answers.
- `NotionRunAllocation` derives whole-run clock bounds, disjoint ID ownership
  and child dominance from allocation/receipt. Sessions use UTF-16 code units.
  The sibling comparator bridge connects dominance to immediate RGA splicing.
- The physical interval model has independent transition and rendering functions.
  Transition projection and `NotionCoreSourceHistory.history_sound` preserve
  every query in a guarded history of atomic command groups. Origin safety can
  be derived from accepted ownership and projected address uniqueness.
- The transaction-set five-VC chain still proves storage convergence for ordinary
  and recursive bases. It has no Notion document-history certificate.

The structural connection now includes a finite physical
origin tree now searches for its insertion origin and derives the global preorder
splice coordinate. A raw endpoint/owner table extracts its materialized intervals
by actual scans and derives coverage and unique ownership across repeated edits.
Source-selected preparation now proves successful local insertion, deletion and
split effects in the physical interval model, including the inherited leaf
boundary at zero. The typed physical replay bridge injectively encodes UTF-16
session identities as unordered semantic names and connects tree insertion to
raw endpoint replay. It does not identify source keys with Sal event labels.

The latest increment derives whole-version mint-past closure and provider-item
availability in actual source-key-sorted prefixes. It distinguishes item births
from create/delete reservations. A raw parent-table interpreter now extracts a
complete ordered forest under derived uniqueness, known-parent and counter-rank
invariants; literal run integration preserves the tree's parent edges. A separate
slice-tree induction preserves root/leaf shape and empty inactive title roots
through actual search, split, detach and append operations. Its enumeration is
source map search order, with displayed block order still separate.

The remaining correspondence is still global. Source payload decoding must
establish item births and selected references, and the raw parent-table,
incrementally ordered tree, slice forest and endpoint ownership must describe
the same execution together with displayed block order. Raw isolated receipt
permits unresolved origins; the adaptation's whole versions preserve closure.
Independent payload values are opaque atoms, so rendering and string
encoding remain explicit. The Sal witness still needs finite event enumeration,
required order and specification visibility together with the source history.
Neither ordinary nor recursive Notion document correctness is claimed.

The oracle now includes 5,348 additional comparisons covering multiscalar runs,
Unicode session ties, clock gaps, deleted anchors and repeated splits, all with
zero discarded histories. It checks 43,005 block shapes/title owners, 62,849
retained-slot intervals and 19,844 physically empty title roots. The preserved
fabricated `Z@10` run / `A@11` insertion shows why first-ID sorting alone fails;
the honestly issued `A@12` control succeeds. The fabricated trace is explicitly
not a reachable-client counterexample. Four additional targeted fixtures check real bootstrap grouping, all-deleted
leaf selection, lone-surrogate atom/string indexing, and receipt before
dependencies. Three direct source-primitive fixtures additionally check the
hidden-origin tree splice and integrate-before-route ownership for both
existing intervals. The earlier 4,500 model comparisons,
575 directed cases and 18,053 bounded local-effect checks remain separately
scoped evidence.
The new structural instrumentation checks all 40 causal ideals of one nine-event
network: 238 full-transaction prefixes and 646 actual RGA entry calls. It preserves
controls for dependency omission, duplicate allocators sharing a session,
child dominance and non-item reservations, plus a witness refuting an unnecessary
global-maximum clock premise.

Independent Sol6.1 review is recorded in [notion-core-review.md](notion-core-review.md)
and [notion-review.md](notion-review.md). The new review caught and corrected a
Unicode ordering mismatch and distinguishes each model theorem from source
correspondence. The [research record](notion-research.md),
[proof boundary](notion-proof.md), and [source correspondence analysis](notion-core-correspondence.md)
provide theorem and assumption details.

Run `scripts/check-notion-research.sh` for all Notion research modules, directed
oracle, known-failure regressions, independent model comparisons and mutation
controls. Run `scripts/check-mrdt-refactor.sh` before pushing; the production
ledger deliberately does not register an unfinished Notion document certificate.
Both gates passed for this increment: all 20 Notion modules (3,431 Lean jobs),
all nine research result groups, the production build (3,694 Lean jobs),
18 exact public contracts and their axiom audit, 187 runtime tests, and validation
of 569 stored benchmark records. Known-failure regression assertions passed by
reproducing the documented failures. This is not a claim of semantic review or
Notion certification by the production gate.
The merge-enabled exploratory `--reachable` command exits 1 when it rediscovers
the known failure; permanent regression success means that failure reproduces.

This branch is suitable as research evidence, not an addition to the paper's
verified datatype inventory. No manuscript edits are proposed. Only
`PRIORITIZED_REMAINING_WORK.md` records outstanding development work.
