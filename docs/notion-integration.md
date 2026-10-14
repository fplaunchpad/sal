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

The structural connection includes a finite physical
origin tree that searches for its insertion origin and derives the global preorder
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
source map search order, with displayed block order represented separately.

The new parent coupling derives sorted traversal from exact raw parent edges,
unique IDs and ordered siblings, including after actual recursive insertion.
Typed atomic payloads derive item births and clock reservations; their emitted
archives derive item freshness and same-instance provider transactions in the
actual sorted replay prefix. The controls distinguish wrong sibling order,
wrong-instance origins, overlapping reservations and newest-first replay.

The combined typed interpreter now executes these operations together and
passes kernel-checked concrete controls. Canonical-prefix graph invariants
supply exact extracted edges and insertion readiness; typed provenance also
derives successful checked row integration. Given structural physical cells
and the next-endpoint relation, actual checked slice extraction succeeds and
returns the intended interior, including under an empty inactive title.
Directed source checks validate endpoint adjacency in 144 instances and
canonical label encoding on 8,191 bounded paths plus twelve repeated splits.

The remaining correspondence is still global. The source's actual selection
must establish item-provider membership for typed emission. Deletion-aware
prefix rows, slice forest and endpoint ownership must describe the same
execution together with displayed block order. The new creator results are
retrospective; they do not replace that joint progress invariant. The typed
interpreter takes ordered transactions; source constructor sorting and runtime
validation still need the complete correspondence proof. Name/range decoding and
search-label uniqueness/runtime validation also remain source boundaries. Raw isolated receipt
permits unresolved origins; the adaptation's whole versions preserve closure.
Independent payload values are opaque atoms, so rendering and string
encoding remain explicit. The Sal witness still needs finite event enumeration,
required order and specification visibility together with the source history.
The item-only typed admission counterexample is now kernel checked: unseeded
START insertion creates no title, so a later split cannot find a slice. A
separate creator-aware relation excludes it. Actual replay now derives block
and instance creators, and actual create/insert/split preparation derives
metadata guards from that provenance. This is a source-preparation increment,
not a proof of future replay success. Honest concurrent splits also refute
requiring replay origin ownership to equal the original requested block.
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
Three additional pinned-source controls validate same-instance birth ownership,
empty-request clock preservation and pending-tombstone birth behavior. The
pending-delete case is a fabricated raw primitive control; the other two use
honest requests. None is an additional confirmed demo bug.

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
Both gates passed for the actual-client and creator-provenance increment:
35 Notion modules (3,446 Lean jobs), thirteen research result groups, the production
build (3,694 Lean jobs), 18 exact public contracts and their axiom audit,
187 runtime tests, and validation of 569 stored benchmark records. Known-failure regression assertions passed by
reproducing the documented failures. This is not a claim of semantic review or
Notion certification by the production gate.
The merge-enabled exploratory `--reachable` command exits 1 when it rediscovers
the known failure; permanent regression success means that failure reproduces.

This branch is suitable as research evidence, not an addition to the paper's
verified datatype inventory. No manuscript edits are proposed. Only
`PRIORITIZED_REMAINING_WORK.md` records outstanding development work.
