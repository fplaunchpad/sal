# Executable refinement of the structural Notion core

## Enquiry

Goal: connect the executable being measured to
`NotionCoreStructuralMRDT`, preserving the existing honest client protocol.
The prior theorem proves a structural finite-fact model; the JavaScript adapter
is separately tested. Differential agreement is not a refinement theorem.

Candidate claim: an abstraction function from retained executable state to
`StructuralFacts.State` commutes with receipt and direct merge, and executable
query equals `StructuralMRDT.query` on every honest reachable state. The
relation must cover the actual program being run, not a manually transcribed
model whose connection to that program is assumed.

A falsifier is a reachable state whose maintained origin-child index disagrees
with its row map, whose marker/cut ownership disagrees with fact decoding, or
whose query differs despite equal abstract facts. Duplicate receipts, late
lower-key arrivals, shared mutable inputs, allocator gaps and merge aliasing
are directed adversarial cases.

The formal oracle will be kernel-checked initial/receipt/merge/query refinement
and invariant preservation. The reality oracle is the unchanged hash-pinned
Notion demo under honest generated requests, plus hand-derived PASS+FAIL
controls. Timings must run the resulting connected executable, not promote
historical measurements of an unconnected adapter to a formal result.

## Representation obligations

- A row identity names exactly one immutable origin/kind/content tuple within
  its physical instance. Origin-child indexes enumerate those rows exactly,
  grouped by origin and sorted in descending item order.
- Retained deletion targets match erased facts; deletion never removes a row
  needed as an insertion or split anchor.
- Every split marker has its immutable destination owner. START ownership is
  the instance's creator. Physical traversal determines boundary intervals.
- Creation links are unique by block identity. The default display computation
  is the proved creation-link fold; tree display is an explicit unproved
  optimization until its equivalence is established.
- Archive identity checking and allocator state are metadata distinct from
  semantic facts. The checked issuance boundary shows facts alone cannot
  recover source counters. Issuance continues through the original client.
- A whole transaction is externally atomic. Any rejection/exception behavior
  must be excluded by a proved input-domain condition or leave state intact;
  no proof may silently treat partial mutation as atomic success.

## Runtime boundary decision

The working implementation compiles the indexed core from Lean and calls it
from a persistent JavaScript harness. Pure receipt,
merge and query definitions are shared by execution and refinement proofs.
The Lean native compiler, C compiler/runtime and JSON byte parser remain trusted
execution infrastructure. The demo-to-typed codec is validated against literal
fixtures and the pinned source; its full translation theorem is not assumed.
The old handwritten JavaScript adapter remains a comparison artifact.

## Evidence status

The previous structural theorem and measurements are preserved at commit
`1b8ffa3`. The executable representation, honest receipt/merge acceptance,
and query theorems now check. The combined constructive endpoint built in a
3,529-job build. The final research gate passed; evidence is recorded below. Work
is tracked only in `PRIORITIZED_REMAINING_WORK.md`.

## First checked component

`NotionCoreRuntimeIndex.traverse_correct` proves that traversal through explicit
origin buckets equals the existing parent-table traversal when every bucket
contains exactly the sorted child identities. `represents_erase` proves that
tombstoning preserves this invariant without rebuilding buckets. A kernel
PASS+FAIL control retains a deleted parent and its child and rejects an empty
index. The 569-job component build passed; its theorem axioms are `propext` and
`Quot.sound`, and the control uses no axioms.

The native runtime now executes the checked Lean lookup/bucket algorithms.
`RuntimeStateProofs` establishes invariant preservation for receipt and direct
merge; `RuntimeAdapterProofs.represents` discharges the query representation
conditions from the concrete state invariant. The handwritten JavaScript
implementation remains a separately tested comparison.


## Executable boundary progress

`RuntimeWire` provides the exact JSON AST decoder used by the native driver.
Kernel controls cover distinct UTF-16 session units and text iterator atoms,
and reject unsupported payload kinds. These controls are examples, not a
universal parser round-trip theorem.

`RuntimeMetadata` retains the full prepared transaction archive and the
reference `Peer` receipt/clock structure. Receipt and explicit local gaps
preserve its archive/reservation and clock-bound invariant; metadata merge
receives the other archive without copying an unpublished clock gap.
`RuntimeEngine` checks repeated transaction identity before receiving and
validates archive compatibility around direct core merging. The pure error
return prevents partial state assignment by the driver. `RuntimeRefinement.receive_refines` and `merge_refines` now prove that
successful operations preserve the concrete index invariant, allocator invariant,
and equality between abstract core facts and the retained archive fact image.
The 3,203-job component build passed with only standard Lean axioms.
`RuntimeHonestProgress.receive_honest`, `merge_honest`, and
`receiveMany_honest` additionally derive acceptance from the original honest
network and archive provenance. No conflict-compatibility or successful-result
premise is required.

`RuntimeMain` exposes a persistent JSON-lines process and reports native elapsed
nanoseconds around execution. It decodes typed requests before timing and
serializes replies afterwards. The pinned-client harness records IPC wall time
separately; source request preparation remains outside receipt measurements.
The native target built successfully (6,858 jobs). The first native smoke run passed 528 query comparisons across 20 generated
honest cases, six literal wire fixture groups, and merge/fork clock-gap controls.
The full retained run subsequently passed 200 seeded cases and 10,008 query
comparisons. Five-repeat measurements are summarized below.

The first driver review found a protocol discrepancy: cloning the complete
engine copied unpublished local clock gaps. The driver now forks by merging
into an empty engine, retaining the source facts while reconstructing allocator
metadata from receipts. The retained clone-after-gap regression control passes: source clock 8,
new replica clock 2, rejecting inherited clock 8.
This was a defect in the new executable wrapper, not a counterexample to the
verified fact model.


## Research statement and exact boundary

The research question is whether Notion's create/insert/erase/split semantics
can be implemented by direct immutable-fact integration while retaining the
original positional issuance discipline and independently verified document
answer. The executable result separates two claims: successful execution
preserves a representation relation, and honest inputs are accepted. The
second is established independently to rule out an implementation that rejects
every request.

The representation relation `RuntimeEngine.Refines` asserts that the native
core satisfies its key, bucket and count invariants, its metadata satisfies
reservation/clock bounds, and enumeration of its core equals the fact decoding
of its retained transaction archive. `empty_refines`, `gap_refines`,
`receive_refines` and `merge_refines` establish preservation. The merge proof
relates union of directly enumerated facts to union of transaction sets; the
core merge never decodes transaction payloads into document effects or replays
them. The metadata merge still visits archived transactions and computes their
reservation widths to update allocator observations.

`RuntimeTheorem.registered_query` states: for an original
`NotionCoreProtocol.Reach` execution with injective sessions, a registered
version, and a concrete engine satisfying `Refines` whose archive represents
that version, the executable query equals `NotionCoreMRDT.D.query` of the
registered archive. `closed_version_reference` also relates it directly to
reference machine reconstruction and rendering. These are conditional
representation theorems, not an assertion that arbitrary JSON requests are
honest. The structural MRDT's existing specification/RA theorems apply to the
same answer. The acceptance lemmas derive the checked core compatibility condition from
the original protocol's archive provenance.

The constructive headline `RuntimeEndToEnd.load_closed_version` removes
caller-supplied representation and acceptance assumptions: given an honest
closed version and any list with its transaction set (arbitrary order and
repetition), receipt into the actual empty engine succeeds, preserves all
invariants, retains exactly that transaction set, and returns the reference
reconstruction/rendering answer. Its build reports only `propext`,
`Classical.choice`, and `Quot.sound`. This endpoint does not silently assume
the desired answer or the existence of a successful receipt.

The concrete core retains six indexed collections: immutable births keyed by
physical instance and item ID; erased item keys; cut destinations keyed by
instance and marker; creation predecessors keyed by block; descending child-ID
lists keyed by instance and origin; and row counts keyed by instance. Deletion
preserves anchors. Query projects tombstones during lookup. Counts provide
traversal fuel without enumerating rows first. Display uses the proved sorted
creator fold. No tree-display equivalence is asserted.

The whole engine also retains a prepared-transaction archive and the reference
receipt reservations/clock. Duplicate identity checks inspect this archive.
Thus removal of transaction replay from the core is not archive reclamation.
Local counter gaps survive locally; only observed reservations cross fork and
merge. Request preparation and issuance remain in the original pinned client.

## Measurements

Evidence: `experiments/notion-incremental/native-observations.jsonl` and
`native-summary.json`. Medians of five repetitions, milliseconds; receipt is
the cumulative time of separate one-transaction receipt requests across the
indicated prepared sequence, while query and merge are single operations.
Receipt is not the timing of one native batched request. These are native compiled-core measurements, separate from
the earlier handwritten JavaScript measurements.

| Workload | Prepared receipts | Receipt | Query | Merge |
| --- | ---: | ---: | ---: | ---: |
| Insertion | 32 | 0.091 | 0.039 | 0.018 |
| Insertion | 128 | 0.541 | 0.325 | 0.086 |
| Insertion | 512 | 4.072 | 4.679 | 0.917 |
| Mixed create/insert/erase/split | 32 | 0.087 | 0.251 | 0.019 |
| Mixed create/insert/erase/split | 128 | 0.568 | 5.951 | 0.089 |
| Mixed create/insert/erase/split | 512 | 3.376 | 73.741 | 0.931 |

At size 512 the mixed input contains 304 late arrivals, with 408 rows,
107 cuts and 179 blocks after receipt. The corresponding full JSON/IPC times
are 11.609 ms receipt, 74.020 ms query and 0.949 ms merge. Preparation, typed
request decoding and output encoding are outside the native operation timer;
IPC timing includes transport overhead. Initial input states are constructed
outside operation timing.

The native query is a measured regression relative to the previous reference
query measurement (about 27.15 ms at size 512 mixed), and far slower than the
previous JavaScript indexed creator-fold query (about 0.167 ms). Those are
historical comparison measurements, not contemporaneous paired trials. Native
query recomputes physical traversal and interval extraction per active block
and sorts creation links on every query. The results support direct receipt
and merge execution without replay; they do not support a universal speedup,
a bound on query complexity, or a claim that native compilation itself is
faster. Query optimization is a subsequent research/engineering question.

## Limitations and trusted boundary

The Lean kernel checks the pure algorithm/refinement theorems. Native behavior
additionally trusts the Lean compiler, generated C and its runtime, and the
JSON parser. The demo-to-typed codec has literal Unicode/UTF-16, counter,
split-group and identifier tests plus differential validation; no universal
codec translation theorem is claimed. The theorem is about the typed core and
existing honest protocol, not production Notion, arbitrary malformed traffic,
or unmodeled UI features.

The full oracle run covers 200 seeded insertion/mixed cases and 10,008 query
comparisons, including late and duplicate receipt and direct joins. Six
hand-derived wire groups and the clock-gap control exercise additional
boundaries. These finite tests validate the deployed boundary; they do not
replace universal proofs. Retained process state contains multiple replicas,
so these timings establish no isolated native-memory or garbage-collection
result. No stronger issuance guard, desired-output premise, or tree traversal
law is used to obtain the checked query theorem.


## Completion evidence

| Requirement | Authoritative evidence |
| --- | --- |
| Actual compiled algorithms, retained indexes and metadata | `RuntimeState`, `RuntimeMetadata`, `RuntimeEngine`, `RuntimeMain`; measured binary hash in `native-build.json` |
| Initialization, receipt, batch receipt and direct merge correspondence | `RuntimeRefinement.empty_refines`, `receive_refines`, `receiveMany_refines`, `merge_refines` |
| Acceptance on the unchanged honest domain | `RuntimeCompatibility.archive_compatible`; `RuntimeHonestProgress.receive_honest`, `receiveMany_honest`, `merge_honest` |
| Executable query and constructive nonvacuous endpoint | `RuntimeTheorem.registered_query`; `RuntimeEndToEnd.load_closed_version` |
| Creator-fold display | Computational `RuntimeQuery.display` and checked `display_correct`; tree law remains outside the theorem |
| Preparation and execution timing separation | `RuntimeMain.loop`, `native-harness.mjs`, raw native/IPC timing fields |
| Pinned oracle and measurements | `native-observations.jsonl` (200 cases/10,008 comparisons); five-repeat medians in `native-summary.json` |
| Retained failures and boundaries | Prior structural counterexamples; fork-clock discrepancy above; literal `native-boundary-controls.jsonl` |
| Theorem, measurements and limitations ready for paper use | This research statement and explicit trust/performance limitations |

The boundary controls additionally submit a batch whose earlier valid creation
is followed by a conflicting transaction identity, and merge a conflicting
source. Both requests reject and leave destination statistics and document
unchanged. These are raw-input robustness controls outside the honest-protocol
theorem. The fork clock regression is likewise retained with a literal expected
answer and the prohibited alternative.


Final gate: `scripts/check-notion-incremental.sh` passed a 6,871-job build,
a fresh audit of 107 theorem endpoints (only `propext`, `Classical.choice`,
`Quot.sound`), the existing JavaScript smoke, and a native smoke with 20 cases
and 1,011 query comparisons. The latter also checks wire fixtures, atomic
rollback, and fork/merge allocator-gap controls. Gate logs were retained at
`/private/tmp/notion-native-final-gate-escalated.log` and the reported temporary
check directory. The initial sandbox run passed build/axiom checks but could
not resolve the pinned oracle host; the network-enabled rerun passed all steps.
The measured native binary still matches its recorded SHA-256. Later additions
were proof modules, not changes to the measured computational definitions.
