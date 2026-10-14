# Notion demo: specification-discovery probes

These probes exercise the readable JavaScript modules served by Notion's
[official interactive demo](https://www.notion.com/front-static/crdt-demo/index.html?embed=1),
linked from its [CRDT article](https://www.notion.com/blog/how-notion-handles-concurrent-editing-with-crdts).
They are observations for learning candidate specifications, not a formal
verification of Notion's production implementation. No production-code
correspondence or open-source licence has been established. Third-party source
is not committed here; `sources.json` records its URLs and SHA-256 hashes.

Run `python3 experiments/notion-oracle/run.py` with Node and curl installed.
The runner fetches and checks the snapshot, then prints literal transactions,
local views and views after exchange. `observations.jsonl` records the first
run on 14 October 2026, independently reproduced. Outputs are not used as
hand-derived expected values for Lean SPOTs.

Starting with `abcd`, split at index 2 concurrently with the following edit:

| Edit | Split / edit session | Observed blocks |
|---|---|---|
| Insert X at 2 | A / B | abX · cd |
| Insert X at 2 | B / A | ab · Xcd |
| Insert X at 1 | A / B | aXb · cd |
| Insert X at 3 | A / B | ab · cXd |
| Delete original range [1,3) | A / B | a · d |

Both issuing replicas after exchange and fresh receivers accepting the two
transactions in opposite orders agree in each probe. The demo reconstructs
documents by sorting transactions before replay, so this is a limited finite
check, not an independent convergence proof.

The first pair refutes always-left and always-right rules for concurrent edits
at a split boundary. A candidate explanation is an ID-ordered split marker;
deletion appears to retain the identities selected before splitting. Further
traces should test concurrent splits, split/merge, and formatting across the
boundary. The sequential specification must be stated independently, then
challenged with these traces and proved against a faithful MRDT model.

## Extended oracle: 14 October 2026

The initial runner, traces and five observations remain reproducible unchanged.
The extended suite uses the same seven SHA-256 pins in `sources.json` and never
commits downloaded demo source.

Run these commands from the repository root:

```
python3 experiments/notion-oracle/run.py --systematic
python3 experiments/notion-oracle/run.py --reachable --core
python3 experiments/notion-oracle/run.py --reachable
python3 experiments/notion-oracle/run.py --minimize
python3 experiments/notion-oracle/run.py --trace regressions.mjs
python3 experiments/notion-oracle/run.py --trace identity-check.mjs
python3 experiments/notion-oracle/run.py --trace identity-controls.mjs
python3 experiments/notion-oracle/run.py --trace core-adversarial.mjs
python3 experiments/notion-oracle/run.py --trace allocation-controls.mjs
python3 experiments/notion-oracle/run.py --trace preparation-boundary.mjs
python3 experiments/notion-oracle/run.py --trace physical-replay-controls.mjs
python3 experiments/notion-oracle/run.py --trace replay-prefix-instrumentation.mjs
python3 experiments/notion-oracle/run.py --trace payload-provenance-controls.mjs
python3 experiments/notion-oracle/run.py --trace search-label-controls.mjs
python3 experiments/notion-oracle/run.py --trace endpoint-adjacency-controls.mjs
python3 experiments/notion-oracle/run.py --trace client-provenance-controls.mjs
python3 experiments/notion-oracle/run.py --trace delete-group-controls.mjs
```

The full reachable run intentionally exits 1 when it discovers the saved local
split counterexample; the regression runner exits 0 when the known failures and
its positive control reproduce. `--minimize` reads the original saved reachable
failure and reissues requests with fresh client preparation after each removal.
It never deletes arbitrary transactions and calls the resulting state reachable.

`systematic.mjs` records 575 cases. It checks every split and insertion boundary
of `abcd`, every nonempty deletion interval, swapped sessions, and three clock
arrangements (equal, split greater, edit greater). Clock skew uses unused valid
clock reservations, not hidden edits. It checks both receipt orders and repeated
delivery, all pairs of concurrent split positions, formatting across a split,
both causal edit/split directions, and merge against split/insert/delete/bold in
either source or destination. The public client exposes merge-driven slice
movement but no general block-movement request; arbitrary forged movement
messages are outside this suite.

`positional-spec.mjs` is an independent sequential visible-list specification.
It imports no demo module. Local expectations use visible list split/splice and
selected-character bold toggling. The concurrent split/delete contract retains
the original selected character identities; its expected blocks follow directly
by intersecting the original deletion interval with either side of the split.
All 300 such cases agree. This does not establish a sequential-history bridge
for the generated identity-addressed messages, nor validate insertion inheritance
inside existing bold spans (the initial local insert controls are unformatted).

`transaction-set.mjs` adapts replication to three-way merge: the base must be a
payload-preserving subset of both inputs; merge takes the union of identified
transactions and rejects conflicting payloads. Issuance and interpretation use
the pinned demo client and document. The suite compares observations with the
demo after delivery and checks an additional nested merge. That correspondence
check is deliberately separate from independent specification agreement. It is
finite evidence, not proof of the five VCs or of recursive-base correctness.
The recorded `nestedMergeAgreement` checks another ordinary union against an
ancestor base. It does not construct or test recursive virtual merge bases.

`identity-spec.mjs` adds the separate retained-slot message specification.
`identity-check.mjs` decodes generated messages into its semantic commands and
checks a candidate ID-sorted witness against demo observations. It covers three
xorshift32 seeds (`0x134ab912`, `0x514a2d19`, `0xabcdef01`), 50 trials per seed,
six fork/join rounds, and two requests per branch. Its 4,500 comparisons cover
every local step and join; empty deletion requests count as no-op steps, with
zero discarded histories. Initial text is ASCII `abc` and inserted text is `X`.
This bound does not cover all Unicode strings, session orders, clock skews, or
unbounded histories; the systematic suite separately varies IDs and clocks.
The same decoder/witness comparison detects injected no-op deletion and
suffix-retaining split mutants on chosen control histories. An additional
demo-independent `identity-controls.mjs` checks retained hidden anchors and
detects suffix-dropping split and no-op deletion mutants using hand-derived
expected states. Neither control injects mutation flags into the specification.

The deterministic reachable generator uses xorshift32 seed `0x514a2d19`, 80
trials, seven fork/join rounds each, and two valid client requests per branch.
It checks all positions of local split/insert/delete after each join. With only
split/insert/delete generation, 560 states and 18,053 checks pass; this is bounded
evidence, not a universal claim. Allowing block merge discovers the first failure
at state 243, check 5,545. `reachable-observations.jsonl` preserves that literal
history. `minimized-observations.jsonl` records 70 replay/shrink attempts and a
one-minimal seven-request setup under deletion of the fixed requests. Its seed
text shrinks from `abcd` to `a`. This is not a proof of global minimality.
The minimizer repeats request removal to a fixed point after shrinking the text,
so its one-minimal claim applies to the final seed.

## Direct failures of ordinary local editing

The [permanent bug catalogue](../../docs/notion-bugs.md) records N-001 through
N-003 with their contracts, literal evidence, minimization limits and formal scope.

`regressions.mjs` reissues concise histories and checks both the observed anomaly
and its disagreement with the independent local contract. These expectations
are semantic controls, not observations promoted into Lean test oracles.

* **Split:** Start with `a`. Split at zero, then insert `X` in the empty first
  block. Concurrently merge the second block twice using different transaction
  identities, then join. Concurrently split the resulting `Xa` at zero and one,
  then join. Merge the split-at-zero block into the preceding block. The visible
  state is `empty · aX`. Splitting `aX` at zero produces `empty · X · a` rather
  than `empty · empty · aX`. The requested suffix is not moved as a whole.
  The saved `beforeStructure` shows `a` below the first child of a common
  ancestor and `X` below its later second child. In pinned
  `text-slice-tree.js:82`, `splitTextSliceTreeNode` partitions the selected
  slice node and transfers that node's children to the new right node. In
  `document.js:140`, `moveTextSliceIntoBlock` detaches only that right-node
  subtree. Neither operation transfers later sibling branches of ancestors.
  Thus the right part containing `a` moves, while the later visible `X`
  remains in the old block. `afterStructure` records this separation.
* **Selected bold:** Start with `ab`, concurrently split at zero and one, then
  join: `empty · b · a`. Merge `a` into `b`: `empty · ba`. Toggle bold on all of
  `ba`. Neither character becomes bold. The positional range maps to equal
  annotation anchors in the underlying text-instance order.
* **Unselected bold:** Start with `abc`, concurrently split at one and two,
  then join: `a · c · b`. Merge `c` into `a`: `ac · b`. Toggle bold on all of
  `ac`. The unselected `b` also becomes bold. The implementation groups selected
  characters by text instance and emits an interval covering the intervening
  unselected character in that instance.

These measured failures concern the pinned public demo and a faithful
transaction-set adaptation. They prevent an unrestricted local-preparation
theorem for the ordinary visible split/bold contract on those reachable states.
They do not establish a defect in Notion production, and they do not refute the
restricted split/insert/delete-only milestone. Fixing the demo semantics would
create a different implementation requiring a separate correspondence claim.

## Core correspondence challenge

`core-adversarial.mjs` extends the same independent decoder/spec comparison to
multiscalar insertions, Unicode sessions, empty text, deleted anchors, repeated
zero-position splits, unused clock reservations, fresh block creation and three
concurrent branches. Three fixed seeds generate 360 joined states; 420 directed
pairs and four deleted-anchor histories supply boundary cases. All 5,348
comparisons pass, with zero discarded histories. The suite detects a mutant
that truncates multiscalar runs. Its UTF-16 control distinguishes JavaScript
session order from Unicode scalar order.

The same run checks 43,005 block shapes and title owners, 62,849 retained-slot
intervals and 19,844 physically empty title roots. Every observed core block has
at most two nodes, one child and one populated slice. These are bounded checks
of a proposed source invariant, not an inductive proof. Exact seeds and bounds
are in `core-adversarial-observations.jsonl` and `suite-summary.json`.

`allocation-controls.mjs` preserves a deliberately fabricated message that
shows why transaction-first sorting alone is insufficient. A `Z@10` run `ab`
contains internal child `Z@11`; inserting `X` after `Z@10` with fabricated
`A@11` produces `abX`, whereas immediate semantic splicing gives `aXb`.
The honest control receives the complete run and issues `A@12`, producing
`aXb`. This is an allocation proof diagnostic, not a reachable-client failure.
The new Lean allocation proof uses whole-run receipt to exclude that case.

The research gate also builds the independent core machine, local-effect and
invariant proofs, grouped history language, allocation/sibling-order lemmas,
and physical interval projection/refinement. These artifacts still lack the
complete pinned-source replay extraction and Sal document-history bridge.

## Source preparation boundary

`preparation-boundary.mjs` has four directed controls for obligations exposed by
the new source preparation proofs. The real demo bootstrap creates the block
and initial run in one transaction; its first item shares the transaction key.
An all-deleted attached block selects the inherited leaf boundary at zero,
not its unused title root. Both are asserted against pinned source calls.

Two other controls distinguish input and execution domains. Separately inserting
lone high and low UTF-16 surrogates displays one emoji but retains two indexed
atoms; splitting at one separates the surrogates. The independent model's opaque
atom values can represent this, but parsing the concatenated string into Unicode
scalars would change its indexing contract. No string-domain restriction has
been added. The receiver also accepts a dependent insertion before the block
and origin arrive, initially rendering no blocks and later reconstructing `aX`.
It does not itself check causal closure or query readiness. These fixtures are
explicit source-boundary diagnostics, not new counterexamples to the retained
atom specification on its intended dependency-closed executions.

`physical-replay-controls.mjs` checks three hand-derived primitive fixtures
against the pinned source. Insertion after a hidden nonroot origin places the
new run before its old child subtree and before a later root sibling. Two
integrate-before-route controls locate a freshly inserted marker in the left
or right existing interval according to its origin. Both old endpoint rows
remain unchanged during that transient routing check. These controls exercise
the trusted tree/endpoint semantics without claiming whole-client reachability.

## Sorted-prefix structural instrumentation

`replay-prefix-instrumentation.mjs` observes actual pinned RGA insertion entry
points without replacing integration or traversal. It checks all 40 causal
ideals of one nine-event honest network, reconstructing 238 full-transaction
prefixes. It checks origin presence, fresh IDs, physical coverage, 661 old-child
comparisons and 398 internal-child complete-run dependencies. The saved JSONL
contains the complete literal transaction/dependency ledger.

The network covers the real grouped bootstrap, Unicode sessions, overlapping
run clocks, internal run origins, split markers, duplicate receipt and no-event
empty requests. It distinguishes a delete transaction's reservation from an
actual RGA item. Deliberately broken missing-dependency, shared-session and
child-dominance controls are detected. A preserved witness has a new first ID
below an unrelated stored item, showing why global maximum dominance is too
strong. This is finite structural evidence, not a source-replay or RA theorem.


## Typed payload provenance controls

`payload-provenance-controls.mjs` checks three hand-derived PASS+FAIL cases
against the pinned source. Two honest histories distinguish same-instance item
birth from global ID membership and prove empty insert/delete requests leave
both clock and transaction archive unchanged. A raw RGA fixture deliberately
deletes a future ID, then distinguishes tombstoned text birth from an undeleted
split marker. That fixture tests primitive semantics, not honest issuance.
`payload-provenance-observations.jsonl` preserves the literal inputs and outputs.
These controls do not add to the three confirmed bugs in `docs/notion-bugs.md`.

The five `delete-group-controls.mjs` records check inherited-instance deletion
with concurrent runs from emoji and U+E000 sessions. The source range codec
sorts IDs differently from physical selection, preserves the selected set,
and excludes markers and prior tombstones. Equal, reversed, and beyond-end
nonnegative ranges reserve no clock ticks. Expected IDs and ranges are
hand-derived; this is a focused control, not an additional confirmed bug.

The extended `replay-prefix-instrumentation.mjs` also compares full stored rows
and pending-target Sets with independent literal transaction decoding: 293
instance tables and 1,534 rows (27 tombstoned) across the existing 238 prefixes.
`replay-table-observations.jsonl` saves the three new output records; the older
campaign record remains historical. A separate raw pending-before-birth check
is not counted as an honest-client history. No-op-delete and wrong-instance
mutations must fail. This remains finite source evidence, not replay progress.


## Atomic split phases

Run `python3 experiments/notion-oracle/run.py --trace split-phase-controls.mjs`
to observe two honestly issued split histories around unchanged pinned
primitives. The hand-derived `ab` split at index 1 distinguishes the phases:
marker integration preserves the old partition; tree splitting retains
coverage while duplicating the old owner; detachment temporarily removes
coverage; append restores final per-instance ownership, including the new
empty title cell. Treating the post-split state as final is rejected. A second
trace splits an all-deleted inherited interval and keeps its empty titles.
`split-phase-observations.jsonl` records literal transactions and snapshots.
These are internal atomic phases, not additional confirmed editor bugs.
