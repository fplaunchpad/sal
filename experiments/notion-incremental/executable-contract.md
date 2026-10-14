# Executable refinement contract

The completed native refinement connects an executable structured core to `NotionCoreStructuralMRDT.D`, with its checked creator-fold renderer, while preserving the original honest factory/client protocol. The selected runtime route is a compiled Lean core; its JSON-lines wrapper is integrated and validated. `structured.mjs` is currently a separate JavaScript research adapter, not extracted or verified JavaScript. The obligations below distinguish the JavaScript adapter and external codec boundary from the compiled core. Checked native state/query/engine refinements live in the Lean runtime modules; finite pinned-oracle agreement alone does not discharge the external codec or JavaScript simulation obligations.

## Current entry points and trust boundary

`new Structured(transactions)` starts from empty maps and receives each complete transaction. `receive(tx)` integrates a previously unseen transaction, returning true; a byte-order-equivalent JSON duplicate returns false. `merge(other)` directly unions retained structural components and the identity archive. `query()` now selects the creator fold; `query('fold')` is equivalent, and `query('tree')` is an explicitly labeled experimental comparison. Main benchmark records label the query strategy. Existing measurements are preserved: `observations.jsonl` measured the former tree default, while `display-fold-observations.jsonl` separately measured both variants. The new default-switch evidence is `default-fold-smoke.jsonl`.

The supported input boundary is a whole transaction from the existing honest pinned client/factory protocol, with distinct session allocators, complete origin providers, globally fresh run/item IDs, creator-complete closed received versions, and the restricted create/insert/delete/split shapes. Empty pre-factory versions, lower-key independent creation before bootstrap, duplicate deliveries and concurrent late arrivals are included. Local request preparation is delegated to the existing pinned `Replica`; its full replay cost is excluded from receipt timings and remains explicit. No new permissive issuance policy is introduced. Formatting, remove-block editing, merge-block editing, raw orphan deliveries, conflicting identities, and arbitrary fabricated wire operations are outside the current adapter contract.

## Wire and identifier obligations

The runner fetches unchanged modules and checks the existing manifest hashes. Audited `ids.js` hash: `f4d40e440f574e3446b9b40f280d5d4684f6c0556fb9aaadb4d08bec893fd8e5`.

1. IDs must have a nonempty string session and positive safe-integer counter; the entire reserved run must stay within `Number.MAX_SAFE_INTEGER`. `opId` validates an individual ID and `nextId` uses it, but raw transaction IDs, cloned marker IDs and observed clocks are not all revalidated at ingress. `LamportClock.reserve` validates the first counter and width, then increments the clock; it does not independently validate the final counter of a long run. The present contract assumes those bounds, rather than claiming general overflow safety.
2. `compareOpIds` compares counter first, then JavaScript string `<` order. A refinement must encode sessions as UTF-16 code-unit sequences, including surrogate pairs, rather than assume Unicode scalar or locale order. `compareItemIds` also handles the literal START/END sentinels; honest born item IDs are objects, never sentinel strings.
3. `idKey` is either a sentinel string or `session + ':' + canonical positive decimal counter`. Session separators do not inherently cause collisions when counters satisfy the domain above; the embedding still needs an injectivity proof. Generated issued block names are `session + '-block-' + counter`; the fixed initial block is `block-A`. Initial/issued names, sentinels and all title-instance names must remain disjoint as established by the typed wire boundary.
4. Text uses JavaScript string iteration (`[...content]`) for atom allocation, not UTF-16 code-unit indexing. Output joins those iterator atoms verbatim. The Lean atom embedding must cover scalar and unpaired-surrogate iterator values without normalization. Positional indices count returned character atoms.
5. A literal wire transaction must decode to exactly the typed transaction: canonical bootstrap A@1; standalone create; insert run with chained origins; bounded deletion ranges expanded into identity targets; or the atomic create/marker/move split triple with one transaction ID. The adapter ignores pointer, path, opVersion and search-label fields. Their source-shaped consistency must be established by honest issuance and wire decoding, rather than inferred from text answers alone.
6. Archive collision checks use `JSON.stringify` equality, including property insertion order, and JSON cloning strips undefined properties. The refinement domain must specify canonical source-shaped serialization or prove normalization agrees with typed payload equality. Arbitrary objects containing NaN, BigInt, functions, cycles or inconsistent property orders are not supported.

## State abstraction and retained indexes

The proposed abstraction of executable core state into Lean facts is:

- Every immutable physical row contributes `.birth instance row`, preserving ID, origin, text atom/split kind and an initially false deletion flag. Tombstones are separate facts; hidden text rows and split markers remain origin anchors.
- Every retained deleted-ID key contributes `.erased instance id` via the injective wire-ID embedding.
- Every created block contributes `.created block predecessor`; the initial block's creator is exactly A@1, and an issued block retains its source transaction ID.
- Every marker destination contributes `.cut instance marker target`.

The identity archive, sorted child indexes, instance records, block index and instrumentation counters are auxiliary representation. A proof must establish each index contains exactly its primary rows/links, with no duplicate entries and the required descending sibling order. The empty own-title instance of every created block must remain present even after inheriting another instance's interval. Public maps and row fields are currently mutable, and insertion origins may share objects from input payloads; the contract assumes callers do not mutate inputs or state. Encapsulation/copying or an explicit ownership discipline is needed before claiming an arbitrary-caller refinement.

Receipt must establish `abstract(after) = abstract(before) ∪ decode(typed tx)`, duplicate receipt must preserve the abstraction, and direct merge must establish componentwise fact union without interpreting archived transactions. Merge checks existing transaction payloads, rows, cuts and block links for conflicts; receive currently overwrites an already named cut and rejects a repeated create in a distinct transaction. Honest freshness excludes those paths. Conflicting finset facts are permitted by the bare Lean carrier but are excluded by the honest execution result, so an unconditional malformed-state simulation is not claimed.

Operations run synchronously and expose no intermediate query under ordinary JavaScript execution. They are not rollback transactions: an exception partway through receipt or merge can leave earlier mutations committed. Refinement must either assume the proved honest path cannot throw, or use validation/commit behavior that preserves the pre-state on failure. The supported complete split transaction must insert its create, marker and destination together before any observation.

## Query obligations

Physical enumeration uses an explicit stack over maintained descending origin children, starting at virtual START. It must equal `StructuralRows.physical` under the embedding. Origin closure, uniqueness, acyclicity and complete reachability are material: arbitrary cyclic indexes can loop, and orphan rows can be silently omitted. The adapter does not validate those invariants independently.

Ownership starts at the instance's creating block and changes at every physical split marker to that marker's retained destination. This running-owner scan must equal the checked partition reconstruction with stops at the next START/marker boundary. Tombstones stay in physical traversal, only live text is emitted, and deleting a marker never suppresses its ownership effect. Inactive title roots remain semantically present but empty. The restricted normal-tree invariant gives one active populated interval per block, so grouping output across Map instance iteration is independent of insertion order; that justification must be proved rather than extended to unrestricted moves.

Display sorts all immutable create links by ascending creator key and inserts each immediately after its predecessor, or at the front for none/missing. Canonical bootstrap participates at A@1, so it is not forced before lower-key pre-factory creations. Bootstrap-absent versions do not invent an initial block. Display and full text output must encode `StructuralRender.observe`'s successful `some View`; JavaScript currently returns arrays or throws, not Lean `Option`. On honest closed versions the checked theorem establishes successful rendering, but error behavior outside that boundary still needs a stated interface.

The default creator fold matches the checked display algorithm. The optional descending creation-tree traversal has separate finite evidence and local lemmas; it must not silently become the verified runtime algorithm without completing its general equivalence proof. JavaScript's maintained physical indexes likewise require an implementation-level simulation: matching the display algorithm alone is insufficient.

## Allocator and archive metadata

The executable retains full cloned transactions in `transactions`. It does not itself implement a Lamport clock, allocator receipts, mint-past certificates or direct positional preparation. Honest preparation constructs a pinned `Replica` from those payloads, whose `receive` observes `transactionClockMax` and whose requests allocate new IDs. The archive is therefore counted in all memory results and may not be described as eliminated from this executable.

`StructuralIssuanceBoundary.next_counter_not_from_facts` proves that no function of semantic facts alone recovers the original allocator's next counter on all honest reachable states. Its equal-fact erase traces have clocks 3/9 and next counters 4/10. A future archive reduction must retain an allocator watermark/clock or equivalent receipt metadata separately and prove its reservation freshness under receipt and join. This obligation cannot be solved by deriving counters from born rows alone: pure erasure reserves an ID without creating a row. Preserving original reference-client provenance is sufficient for the currently mapped MRDT scope; direct structural preparation is a further optimization requiring its own refinement.

## Measurement counter meaning

Counters are auxiliary mutable instrumentation, ignored by the proposed fact abstraction. They are cumulative per engine state, including construction. Query increments counters even though the logical MRDT query is observationally pure.

| Counter | Exact current event counted |
|---|---|
| `transactionsIntegrated` | A successfully completed, previously unseen `receive`; direct merge archive union does not increment it. |
| `rowsIntegrated` | A fresh physical row added by receipt or direct join; equal duplicate rows do not increment it. |
| `deleteTargets` | Expanded target occurrences during receive, including repeats; it is not the unique tombstone-set size and merge does not increment it. |
| `queries` | Each query call, for either display variant. |
| `rowsVisited` | Reachable physical rows popped during query, including hidden rows and markers. |
| `merges` | Completed direct join calls, including idempotent joins. |
| `mergeRowsExamined` | Every incoming source row scanned during joins, including duplicates. |

There are no present counters for creation-fold comparisons/splices, archive JSON comparisons, cut/delete/block union scans, query bytes, allocation metadata, exception rollback or positional preparation. Timing includes those actual adapter operations where applicable; these counters are partial work evidence, not a total complexity accounting. Long-running counter overflow and thread safety are not established. Historical tree/fold timing files retain their original strategy labels; new main measurements use the default creator fold. Retained heap measurements include the archive and representation, exclude pre-generated workload retention, and show no general memory saving.


## Compiled-core wire bridge checkpoint

`native-wire.mjs` and `native-harness.mjs` preserve the existing pinned client/oracle while communicating with the compiled core through JSON lines. The stable typed schema uses `Id = {counter, session:[UTF16 units]}`, `BlockKey = "initial" | {issued:Id}`, and `Origin = "start" | {item:Id}`. Typed payloads use bootstrap/insert atom lists, create predecessors, expanded erase target IDs, and the atomic split payload. The codec validates whole command group shapes and cross-operation identities rather than accepting an arbitrary mixture of core-looking operations. It checks the whole run's safe last counter and verifies source/typed clock maxima in its fixture corpus.

The process interface sends init, receive, merge and query requests. Successful queries return typed block keys and Nat atom lists, which the bridge converts to pinned wire names/text for differential comparison. Native `elapsedNs` is recorded separately from complete serialization/IPC roundtrip time. Source positional preparation, wire-to-typed conversion, initial state construction and fixture warmup are excluded from the reported operation intervals. Prior replicas remain retained in a benchmark process, so this harness makes no isolated native memory claim.

`native-wire-fixtures.jsonl` records hand-derived typed expectations, including empty bootstrap, lower-key pre-bootstrap creation, split to an inherited instance, an emoji run and its bounded deletion. Controls distinguish UTF-16 session units from source text iterator atoms and reject unsafe IDs, noncanonical decimal names and inconsistent atomic split targets. This codec boundary remains tested/trusted until separately proved. The Lean runtime state/query simulation does not by itself establish that JavaScript parsing and JSON serialization implement these typed conversions.


### Native fork metadata correction

Audit found that the initial native `clone` wrapper copied the entire engine, including an unused local source gap. That mismatched the intended honest fork: the pinned new replica and original source exchange copy received transactions/reservations and derive their clock maximum, rather than import the source's unissued gap. The parent corrected clone to direct-merge the source into an empty engine. The native harness now pins seed `ab` at clock 2, a six-tick source gap at clock 8, and both target merge and clone-after-gap at clock 2, with explicit negatives rejecting clock 8. This was a new native wrapper integration bug caught during audit, not a Notion demo bug or a failure of the checked semantic fact carrier.

### Native atomic-error boundary controls

`native-boundary-controls.jsonl` retains two raw typed robustness tests outside the honest protocol. Receipt of `[valid fresh create, conflicting existing transaction ID]` returns an error and leaves target stats/query unchanged; merge of an independently seeded conflicting identity does likewise. The wrapper preserves the old store when the pure `Except` computation fails, so its batch interface must not expose an earlier successful prefix. The tests pin both positive rejection and negative leakage through archive count, physical rows, cuts, blocks, allocation clock and the literal `ab` query. These do not authorize malformed/conflicting requests in the verified honest-core theorem. This native transactional error behavior is distinct from the JavaScript adapter's earlier mutable partial-exception behavior.
