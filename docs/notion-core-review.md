# Independent review of the Notion core enquiry

This review examines theorem statements and trusted definitions in
`NotionRunAllocation.lean`, `NotionCoreRGA.lean`, `NotionCoreSpec.lean`, and
`NotionCoreSource.lean`. It also challenges the executable retained-slot model
against the pinned public demo. The result supports the core design but does
not establish complete source correspondence or a sequential-history bridge.

## Allocation and child dominance

`reachable_unique_owner` derives nonoverlapping run ownership from serialized
per-session allocation. `reachable_owns` and `reachable_bounded` establish the
clock information used by that proof. Receipt is restricted to published runs;
issuance requires positive width. Repeated receipt is permitted. These are
explicit operational assumptions, not premises asserting the desired editing
result.

`known_run_received` derives complete-run provenance from known item identity
and unique ownership. `internal_child_before_reservation` then uses the maximum
of the complete received run, rather than merely its first timestamp. This is
the right distinction for atomic multicharacter insertion. The negative control
`sorted_first_is_insufficient` demonstrates why ordering transaction-first IDs
alone is inadequate.

`child_dominance` remains conditional on the earlier transaction-first order
and knowledge of the predecessor for internal-run children. The file does not
derive those premises by traversing an actual source origin graph or a sorted
replay prefix. Its `Reach` relation models reservations and receipt, not editing
legality or transaction payloads. It does not identify which requests yield
which runs. The reviewed extension now includes `advance`, `skip`, and a
`Reach.gap` constructor. These add arbitrary nonnegative unused reservations
without changing receipt or publications; the boundedness, ownership, and
provenance inductions include that case. This addresses the deliberate clock
gaps in the runtime oracle.

The review found a real representation mismatch in the initial use of Lean
`String` ordering: Lean puts U+E000 before the emoji U+1F600, while JavaScript
orders its UTF-16 surrogate pair before U+E000. The parent corrected sessions to
explicit UTF-16 code-unit lists and added a kernel PASS+FAIL control.
`core-adversarial.mjs` separately checks the pinned source comparator and both
Unicode-session orientations. The allocator arithmetic allows arbitrary natural
units; correspondence to source strings still requires actual UTF-16 encoding
with units below 65536. Source counter validity additionally uses JavaScript
safe integers, whereas Lean arithmetic is unbounded. These representation
domains must be stated when connecting source executions.

Source compound IDs remain distinct from Sal's outer event timestamps. The
current allocation results do not supply that embedding or show that its order
and freshness obligations hold.

## RGA splice lemmas

`runTree_preorder`, `first_child_run_splice`, and `context_run_splice` correctly
compute preorder after a whole fresh run becomes the first child of an origin.
Their premises do not assert an observation equality. Their important gate is
structural: the new run is already placed first, and the before/after context is
already supplied. The module does not derive first-child position from the
source sibling sorter, extract the context from an origin graph, or establish
source reachability. The comments expose these limits.

## Independent local editing

The core specification contains retained semantic addresses, block order, and
visible characters. It contains no transaction logs, clocks, search labels, RGA
trees, or source calls. Retained addresses support deletion-stable gap commands.
Address uniqueness is load-bearing: it prevents an edit selected in one block
from affecting an identically named character elsewhere.

The local insertion and deletion theorems derive ordinary visible list effects
from address uniqueness and structural preparation. Their existential result is
tied to execution of the stated command and to the requested view, so choosing
the input document as an unrelated witness does not discharge the theorem.
The split client theorem executes create followed by split; fresh block/root
names derive the empty successor preconditions of its command theorem.

`PreparedGap` states membership at a retained coordinate and the visible prefix
length. This is a useful structural preparation obligation, rather than the
whole requested split result. It remains necessary to show that the actual
demo's `locateInsertion` produces such an address. In particular, a source block
with an empty title root and an attached slice can choose the attached slice's
boundary at visible zero, whereas one abstract canonical preparation can choose
the empty root. The visible-gap formulation accommodates either; it does not
prove exact message correspondence by itself.

These initial local-effect theorems do not themselves preserve `WellFormed`
after arbitrary supplied insert runs or markers. A local visible-effect theorem
can hold even if output addresses collide. The later `NotionCoreInvariant`
development, reviewed below, proves preservation under explicit structural
freshness admission. Local clamp calculations for oversized indices are also
broader than the source's accepted insertion/split request domain; actual client
correspondence must establish bounds. Deletion uses start/count in the model
and start/end in the source, requiring the ordinary `count = end - start`
connection on legal ranges.

## Materialized source normal form

The interval representation makes useful progress: physical insertion and
marker splitting project to independent slot insertion and cutting. Deletion
projection is a direct per-atom calculation. These equalities are derived from
the interval operations, rather than assumed as the representation relation.

This is still a materialized interval model. `Block.Normal` expresses local
instance agreement and root-shape conditions; it does not itself establish a
global partition, unique addresses, fresh block ownership, a physically empty
source root, or extraction from the JavaScript endpoint tree. The module states
this trust boundary explicitly. The `located : idxOf origin = position`
premises alone do not prove origin presence: missing origins have `idxOf`
equal to list length, making a clamped calculation possible. A legal source
simulation must additionally derive membership and the appropriate coordinate.

The source audit suggests the stronger concrete invariant: each live no-merge
block has either a root alone, or a permanently item-free title-instance root
with one leaf child in a different instance. Honest preparation selects that
leaf even when every text character is deleted. Source replay and
origin/slice membership still need to establish this invariant inductively.

## Executable challenge and coverage

Run `python3 experiments/notion-oracle/run.py --trace core-adversarial.mjs`.
The runner checks all seven source hashes in `sources.json`; downloaded source
is not committed. The three-line result is preserved in
`core-adversarial-observations.jsonl`.

The directed suite checks 420 split/run-insertion pairs. Initial strings include
empty, ASCII, astral, and combining sequences. Every scalar-index split and
insertion boundary is tested with both ASCII and Unicode session orientations
and clock reservations `(0,0)`, `(9,0)`, and `(0,9)`. Four explicit histories
delete all original anchors and then execute four rounds of three concurrent
zero-boundary splits followed by same-session Unicode insertion.

The generated suite uses xorshift32 seeds `0x134ab912`, `0x514a2d19`, and
`0xabcdef01`: 20 trials each, six rounds, three branches, three sequential
requests per branch. Requests include create, split, multiscalar insert,
range delete, and delete-all. Sessions are reused sequentially within branches
and remain distinct concurrently. Delivery is reversed and repeated at joins.
Checks occur at local transaction boundaries and joins; transient internal
split states are intentionally outside the claimed shape invariant.

The run passes 5,348 source/spec comparisons, 43,005 block-shape and title-owner
checks, 62,849 retained-slot interval checks, and 19,844 checks that two-node
blocks have physically empty title-instance RGAs. Each title instance equals
its owning block ID and title instances are distinct. Retained slots, including
tombstones and split markers, form an interval in the corresponding source
RGA traversal. Observed maxima are two nodes, one child, and one populated slice
per live block. No histories are discarded.

A deliberately broken model truncating each multiscalar insertion run is
detected by the same decoder/spec comparison. The UTF-16 comparator control
also rejects the tempting scalar-order explanation. These controls establish
harness sensitivity, not universal model validity. The finite bounds do not
cover every Unicode string, session encoding, clock range, or arbitrary-length
history, and they do not prove transaction-intermediate observations safe.

## Verification and conclusion

Independent `lake env lean` checks of the four reviewed modules succeed. The
reported allocation dependencies are standard `propext`, `Classical.choice`,
and `Quot.sound`; the reviewed RGA and interval projection calculations report
standard logical dependencies and introduce no new axioms or admissions.

The core now has independently justified local specification results, a
receipt-derived allocation argument addressing internal insertion-run children,
and strong bounded source agreement. The unclosed connection is the complete
source replay/normal-form induction and its integration with Sal's five VCs
and same-witness history bridge. Neither ordinary nor recursive-base natural
editing correctness follows from these modules alone.

## Follow-up: grouped history and document transitions

`NotionCoreHistory.lean` supplies an independent history machine whose updates
are atomic lists of semantic commands and whose queries return the current
document view without changing state. Grouping create/split prevents a query
from observing an intermediate split transaction. Neither state nor admission
contains source clocks or a source replay sorter. `update_runs_iff` equates
accepted groups with execution of the partial semantic machine;
`updates_query_iff` ties the terminal answer to the final state from those same
groups. The PASS+FAIL split history rejects an unchanged-text answer. These
are substantive independent-spec lemmas, but remain equivalences between two
presentations of that spec: they supply neither source execution correspondence
nor an RA witness.

The underlying command machine permits more inputs than honest client issuance,
including arbitrary supplied insertion slots, markers, and empty command
groups. Its history language therefore does not by itself enforce fresh-address
or well-formed-state invariants. The local-effect and future source refinement
claims must retain their explicit structural/issuance gates. This is not an
observed counterexample to the stated history theorems.

`received_transaction_precedes` derives strict source-counter increase from
reachable complete receipt. `source_order_preserves_visibility` uses one
pairwise source-ordered list for both visibility and a restricted specification
visibility relation. This preserves the same-list requirement: the proof does
not switch to another witness for the second relation. However, the theorem
assumes the ordered list and the visibility-to-counter inequality. It does not
enumerate an execution's events, prove that the chosen list is their
permutation, derive its order from a concrete sorter, or show its query admitted
by the independent machine. Complete receipt supplies a useful causal edge
lemma, not yet the whole history bridge.

`NotionCoreSourceDocument.lean` adds document-level projection of materialized
interval commands. `project_create`, `project_insert`, and `project_delete`
compute matching partial transitions. `project_split` and `step_sound` use
block-ID uniqueness, accepted materialized transitions, and `OriginSafe` to
derive the semantic transition; they do not assume an observation equation.
The ownership guard excludes unused empty-title root addresses, preventing the
semantic owner search from selecting an extra wrapper absent from the active
source interval. Accepted source-model splits additionally require an empty
root-only destination. These are structural gates rather than disguised
desired-result premises.

The correspondence is deliberately to the newly defined materialized
normal-form machine. Its insertion uses a list splice and its split uses an
interval cut. It is not yet a translation theorem from the pinned endpoint/RGA
implementation. `OriginSafe`, block uniqueness, empty destinations, and the
physical normal form are not derived there from an actual client execution.
The follow-up `Execution` relation now composes these steps, carrying `Guard`
at each source-model state. `execution_sound` proves that the same decoded
command list executes in the independent machine to the projected final state.
This is a universal guarded trace simulation, stronger than a final-view
equation for one fixture. Its guard is still supplied at every step rather than
derived and preserved by honest issuance. The relation is a flat command trace;
it does not itself establish grouped transaction history, RA event enumeration,
or source endpoint extraction. The hand-derived source split fixture has a
negative control against leaving all text in the original block.

Independent checks of the final grouped-history module, allocation extension,
and source-document module succeed. The source-document `step_sound` and
`execution_sound` report only standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies. No broad oracle runs were repeated for this
follow-up review.

## Follow-up: semantic issuance invariants

`NotionCoreInvariant.lean` closes structural preservation for the independent
semantic machine. Its `FreshRun` requires pairwise distinct inserted addresses
and disjointness from existing addresses. Create admission requires fresh block
and root names. Insert admission requires a known source address and a fresh
run. Split admission requires a known owner, an allocated empty target with a
different block ID, and a fresh hidden marker in the origin's instance.
Deletion can target arbitrary retained addresses; hiding an already hidden or
absent character is harmless for this structural invariant.

These conditions do not assume the output's well-formedness or visible editing
effect. The owner equation is an executable address lookup in the input state,
not a transition or observation equation. Local decomposition premises identify
the selected input block. `trim_preserves_and_fresh` derives ownership transfer:
after removing the suffix, its identities and the new marker are disjoint from
the remaining document. The split proof then uses this derived freshness when
inserting the suffix into its new owner.

`step_preserves` establishes actual `WellFormed` preservation. Importantly,
`admissible_progress` separately proves existence of a successful transition
from a well-formed admitted state. The result cannot be discharged merely by
making every interesting transition fail. `Reach` starts from the empty
document and uses admission plus actual command execution; it does not include
`WellFormed` as a step guard. `reachable_wellFormed` derives the invariant by
induction over that relation.

The hand-derived hidden-origin control constructs a nonempty reachable
execution: create, insert `a,b`, delete `a`, create a successor, and split after
the retained hidden identity of `a`. Its positive view places only `b` in the
successor; its negative control rejects leaving `b` in the original block.
This checks both nonvacuous reachability and permission to use hidden origins.
The freshness control accepts distinct character addresses and rejects reuse
of the invisible root address. These are meaningful PASS+FAIL controls, not
implementation-produced expected values.

The issuance language remains a sufficient semantic discipline, not a model
of the pinned client. In particular, fresh inserted slots may have arbitrary
values, visibility, or instances provided their names are distinct. `WellFormed`
states block-ID uniqueness, global address uniqueness, and a hidden head in
each block; it does not state source allocation provenance, physical interval
ownership, scalar encoding, or an empty-title root shape. The allocation and
source-normal-form results must still be connected to admission. Consequently
this development removes a semantic invariant-preservation gap without claiming
that the JavaScript issuer has been proved to obey it.

The final invariant module independently checks with `lake env lean`. Its
progress, preservation, and reachable-invariant theorems report only standard
logical dependencies. The executable fixtures use a computable bounded-list
freshness decision procedure rather than a noncomputable classical decision.

## Follow-up: grouped physical histories

`NotionCoreSourceHistory.lean` composes the guarded physical trace simulation
with the independent history language. Its physical renderer directly filters
deleted text and split markers from atoms. `render_projection` proves agreement
with the semantic view instead of accepting answer equality as a premise.
`runs_sound` retains exactly the same ordered atomic update groups and queries,
mapping only the command representation. Its query case covers intermediate
answers, not merely one terminal view. `history_sound` then transfers admitted
source-machine histories to admitted independent semantic histories.

The source-machine transition guard is still `Source.Execution`, so each
command's structural guard remains supplied. The theorem does not derive those
guards from the demo issuer, enumerate RA events, select a source replay order,
or connect the actual endpoint implementation to the physical machine. The
nonempty creation/insertion PASS+FAIL history rules out a constant-empty query
explanation. Within its stated materialized-machine boundary, this is genuine
grouped history refinement rather than transaction-set convergence alone.

The final source-history module independently compiles. `history_sound` and
the PASS+FAIL control report only standard logical dependencies. The initially
observed unused-simp warning was subsequently removed.

## Final follow-up: derived source guards and sibling sorting

`NotionCoreSourceGuards.lean` derives the inactive-root separation obligation.
`originSafe_of_active` combines active membership with global projected-address
uniqueness to exclude equality with any attached block's unused title root.
It handles collisions within the same block and in another block. The owner
wrapper derives membership from executable source lookup, permitting hidden
characters and boundary anchors. `accepted_guard` consequently derives the
old source-document guard from projected well-formedness and actual acceptance;
no visible-effect equation or manual `OriginSafe` hypothesis is needed.

Its reachability relation begins empty and carries semantic `Admissible` plus
actual physical source-model transitions. `reachable_invariants` derives both
semantic reachability and projected well-formedness. It does not assume
well-formedness of the next state. This closes the former per-state
well-formedness/origin-safety gap for that admitted source-model language.
Semantic freshness/shape admission remains a caller obligation, and accepted
physical transitions remain part of the execution relation. Semantic progress
alone is not a proof that every intended physical client request succeeds.
The hidden-origin safety/insertion controls reject using the inactive title
root, distinguish insertion before the next visible character from appending,
and include a nonempty reachable allocated-root execution.

`NotionCoreSourceInvariant.lean` explicitly models the counter-first/UTF-16
source comparator and proves its agreement with the descending sibling relation.
Library merge sort is used through sortedness and permutation contracts, so
the theorem does not depend on JavaScript using that sorting algorithm.
`sort_fresh_first` turns child dominance into first-child placement.
Following review, `sort_permutation` and `sort_fresh_enumeration` extend this
to arbitrary map-key enumeration, including freshly inserted keys at the end.

`ChildrenFromRuns` supplies provenance: each old child belongs to a published
run whose first key precedes the new transaction, and internal-run children
have their preceding run item known to the issuer. The allocation theorem
derives child dominance and sorting from this provenance. This premise is not
the desired sorted output, but it still needs establishment from actual source
origin edges and replay prefixes. `sorted_forest_splice` then places the whole
fresh run before the old children's complete subtrees. The counter/session
sorting control has an explicit negative against ascending order; earlier RGA
controls separately distinguish whole-run insertion from appending after the
old subtree.

Both final modules independently compile with standard logical dependencies.
The review found no circular desired-effect premises in these statements.
Together they narrow the remaining source bridge to provenance, normal-form
extraction, and actual-issuer semantic admission, rather than closing those
obligations by assumption under a stronger name. The full same-witness RA
certificate and its ordinary/recursive-base scope remain unestablished for the
natural editor. No broad oracle tests were repeated during this final review.

## Targeted source preparation boundary

The next review increment inspects pinned `document.js:275` (`locateInsertion`),
`replica.js` request preparation, and the actual demo bootstrap. Four focused
fixtures are reproducible with
`python3 experiments/notion-oracle/run.py --trace preparation-boundary.mjs`.
Their literal transactions and observations are saved separately. This is a
targeted boundary check, not a repetition of the broad passing suites.

| Source preparation | Required model connection |
|---|---|
| `blockCharacters` traverses live text items in displayed slice order. | Positional indices count editing atoms, not JavaScript UTF-16 units or grapheme clusters. |
| Positive `locateInsertion` selects `characters[index - 1]`, carrying that item's instance and identity. | A legal natural index in bounds supplies a visible predecessor and its source instance. |
| At zero, the function chooses the first slice with a visible text item; if none exists, it chooses the last traversed slice and its retained start boundary. | Under the root-only/empty-root-plus-leaf normal form, preparation selects the active leaf, including when all characters are deleted. Its origin need not be visible. |
| `deleteText` uses `blockCharacters(...).slice(start,end)`, groups by instance, then compresses selected IDs into ranges. There is no separate `locateRange` helper in the pinned client. | Legal range preparation must establish selected visible identities; decompression/sorting preserves their set. Integer/range legality is an external client domain condition, not enforced uniformly by this helper. |
| `splitBlock` captures one insertion location, then emits create/split/move as one transaction. | The three operations must remain one atomic semantic update; the public view occurs after the entire group, including detachment. |
| `createInitialTransactions` emits create and insert in one transaction, both using first key A@1. | The real bootstrap requires a grouped initial-state connection; the existing two-request `Replica.createBlock` then `insertText` fixtures are a different bootstrap. |

The empty-leaf fixture passes: split `ab` at zero, delete both moved characters,
then prepare insertion at zero in that block. The source selects the inherited
split-marker origin in the original text instance, rather than the unused
fresh title root. The bootstrap fixture separately checks that inserting after
initial `ab` next allocates counter 3. Empty bootstrap text still has a
transaction/create key, even though its insertion creates no text run.
This is an encoding boundary, not an allocation contradiction: a positive
bootstrap reservation of width `max 1 atomCount` can cover that group. The
actual bootstrap decoder and its hard-coded block name still require a
correspondence argument.

The review identifies two domain distinctions that must not disappear in a
source theorem. First, source string spread accepts lone UTF-16 surrogates.
Insert a lone high surrogate, then a lone low surrogate: the displayed string
is the emoji U+1F600, but the source retains two editing atoms. Splitting at
index one separates those surrogates. Thus arbitrary source text cannot be
identified with the Unicode-scalar list obtained by spreading its concatenated
rendered string. A theorem may restrict inserted strings to well-formed UTF-16,
or retain source iterator atoms and a separate rendering function. The current
`Slot.value : Nat` is opaque and can encode isolated surrogate iterator elements;
the formal atom-sequence view does not impose a Unicode-scalar domain or prove
a stringify/parse round trip. No input restriction is silently added here.
The local split fixture explicitly refutes an unqualified contract that first
parses the concatenated displayed string into scalars and then splits that
scalar list: that contract gives `emoji | empty`, while the source gives
`high-surrogate | low-surrogate`. This is a contract/representation distinction,
not a refutation of the retained opaque-atom specification.

Second, `receive` stores identified transactions without requiring causal
dependencies. A receiver given only an insertion whose block and origin have
not arrived accepts it and renders an empty document; after receiving the
bootstrap dependencies, it reconstructs `aX`. Therefore dependency closure and
origin reachability are execution assumptions to derive or enforce, not
validation already performed by the published receiver. The fixture's initial
empty result follows directly from having no created blocks. It does not claim
that dependency-incomplete receipts violate the source's contract.

## Global origin-search review

`NotionCoreOriginTree.lean` replaces supplied preorder contexts with actual
recursive origin search through a finite forest. START remains external.
`insertForest_splice` derives the surrounding physical-list splice from that
search, under the structural requirement that the new first key dominates
existing children of the searched origin. `insert_run_indices` then derives
the concrete retained insertion coordinate by searching the complete physical
preorder. Neither theorem assumes the desired before/after list equation.
Hidden text and split markers remain in the searched tree.

`insertChild_sorted_keys` relates local ordered child insertion to complete
source-comparator sorting when old child keys are ordered. Allocation/run
provenance supplies dominance separately; the module does not assert that
transaction-first sorting alone suffices. Fresh internal run IDs and
disjointness from old IDs are explicit hypotheses of unique-ID preservation,
rather than invariant conclusions silently assumed for the inserted forest.

The fixtures distinguish a hidden nonroot origin from appending after the
forest, a leaf insertion from insertion after a later root, START insertion
from insertion after the first visible character, and split-marker origins
from failure. The missing-origin fixture checks the partial tree domain and
rejects unchanged successful output. It does not claim that the raw source
rejects an orphan: the header explicitly notes its receiver can store
unreachable items. Parent-map-to-forest extraction and dependency closure remain
separate. These are meaningful global search lemmas within the known-origin
fragment, rather than verification of every raw received message.

The final origin-tree module independently compiles with standard logical
dependencies. No broad oracle runs were needed to validate these new statements.

## Source selection and local message effects

`NotionCorePreparation.lean` now implements the source's selector on the
root-only/empty-title-root-plus-leaf representation. Its zero rule selects the
active slice boundary even with no visible text. Its positive rule selects the
preceding visible atom through tombstones. `locate_progress` proves legal
indices return an address, while `locate_prepared` derives the semantic retained
coordinate and visible prefix count. Neither takes the requested edit's output
as a premise. Extraction of that one/two-node representation from source replay
remains separate.

`delete_targets_projection` proves exact selected identity agreement before
same-session ID-range compression. `source_delete_effect` then gives the whole
physical-model document effect and preserves other block views, using address
uniqueness to exclude cross-block deletion. Natural start/stop inputs with
start at most stop share the source's clamping behavior; a scalar-string
roundtrip is not used. Compression/decompression correctness remains a
separate message-encoding step.

`source_insert_effect` uses the actual selected origin's instance and proves
existence and the immediate atom-sequence insertion effect for supplied run
entries. Allocation, contiguous run IDs, and freshness remain external. The
current theorem does not identify arbitrary supplied entries with the exact
`LamportClock.reserve` result or prove their future invariant preservation.
`source_split_message_effect` uses the same selected origin and proves the
independent grouped create/split command effect. Its statement clearly labels
this as preparation/message correctness, rather than claiming extraction of
the physical endpoint/split/move implementation.

The selection fixtures reject the independent helper's unused title-root
choice at zero, a hidden rather than visible predecessor at a positive index,
and deletion of a hidden rather than selected visible identity. They also
check the all-hidden fallback and an oversized-index rejection. These controls
distinguish actual preparation choices without promoting implementation output
into the expected visible editing contract.

The source returns `undefined` without reserving or publishing for empty text
insertion and empty deletion selection. The materialized machine can instead
execute an empty insertion run or empty deletion as a no-op command. Its local
view theorem is compatible with that case but does not establish matching
issuance, clock advancement, or event enumeration for empty requests. Those
requests need an explicit no-event encoding when connecting the real client.

The final `source_split_effect` strengthens that message result to successful
physical normal-form creation followed by splitting, with the exact requested
whole-document view. Creation's projection supplies an actual created state;
`create_empty_target` derives its empty destination. Creation preservation
establishes projected well-formedness, from which the selected active origin
derives safety. `split_progress` then lifts independently proved semantic
split existence to physical transition success by inspecting its domain.
Only after proving that success does transition projection give the output
view. This argument does not assume physical success or the desired physical
answer as a premise.

The split encapsulates marker insertion and slice detachment in one
materialized operation; extraction of the raw JavaScript three-operation
transaction remains open. The immediate-effect theorem does not require fresh
marker IDs and does not conclude final invariant preservation for arbitrary
supplied markers. Connecting its parameters to the actual allocator and
admissible issuer is still necessary for faithful repeated source executions.
The physical zero-split control transfers the remaining visible atom from an
attached block and rejects leaving it in the old block. The frozen preparation
module independently compiles; its printed local-effect dependencies are
standard logical axioms only.

## Endpoint partition extraction

`NotionCorePartition.lean` extracts cells by scanning raw start/next-endpoint
addresses and looking up physical atoms. Its representation records a
structural factorization of physical atoms and endpoint rows, address
uniqueness, and unique cell owners. It does not equate the extracted cells with
the desired result as a premise. `extraction_correct` derives that equation
from the factorization. `physical_unique_owner` and `split_refines` derive the
affected interval from raw origin membership rather than accepting a chosen
owner or surrounding context.

The raw split transition actually locates its cell, splices a marker into the
physical list, and inserts the new endpoint row. It never reads a proposed
materialized output partition. Raw insertion and deletion similarly operate
on physical atoms. Their preservation lemmas relate those operations to the
recovered cells. The later raw `Reach` relation carries input freshness,
instance/kind conditions, and actual accepted raw operations; it does not carry
a materialized partition or output invariant. `reachable_represents` derives
factorization and the property that all interior atoms are text, so split
markers remain exactly interval boundaries. `reachable_extraction` then makes
the actual scan, rather than an arbitrary existential projection, the invariant
partition for every such reachable state.

The sentinel boundary is explicit: this physical list prepends a virtual START
boundary atom, whereas JavaScript's RGA keeps START external. END is an
explicit scan sentinel. Endpoint-table order is physical interval order and
does not assert displayed block order. `semanticCells` is a per-instance
auxiliary document, not the global displayed document with empty title-root
wrappers. Those representations still need an explicit connection.

The endpoint fixture excludes both endpoints while retaining a tombstoned
character, and rejects assigning all following atoms to the first interval.
The tombstone-owner fixture rejects absence. The reachable repeated-operation
fixture performs insertion, deletion, splitting after a hidden identity,
another insertion at that hidden identity, and a repeated START split. Its
positive and negative views distinguish proper suffix transfer from retaining
the visible prefix in the old owner. These are hand-derived controls with
actual raw transitions, rather than views copied from the demo.

The scope remains a raw endpoint/splice machine. Its immediate physical splice
has a separate origin-tree justification, but the module does not itself
extract JavaScript's parent map or compose that justification into sorted replay.
Freshness and source-shaped inputs are supplied by the raw issuance relation;
they are not yet obtained from the real allocator/client. Global block-order
and one/two-node slice-tree preservation, grouped transaction correspondence,
and the complete RA bridge remain separate. This is a genuine derived
endpoint-partition invariant within that boundary, not complete source
verification.

The frozen partition module independently compiles cleanly. The extraction,
ownership, split-refinement, and reachable-scan theorems report only standard
logical dependencies. The targeted preparation runner, syntax check, and
repository whitespace check also pass; previously passing broad suites were
not repeated for this increment.

## Integrate-then-route split order

The source integrates a split marker before searching for its containing
slice. The raw combined split initially locates the old origin before inserting
the marker. `marker_routing_after_insert` now relates these orders: from an
existing factorization, a present origin, and a fresh marker, it derives that
the unchanged endpoint table routes the inserted marker to the same old owner.
Its returned cell includes the transient interior marker. The proof uses
physical insertion preservation and actual endpoint scanning; it does not
assume the post-insertion routing answer.

This transient state need not satisfy `InteriorText`: the endpoint row making
the marker a boundary has not yet been installed. `Represents` deliberately
supports that intermediate interval calculation. The control checks a split
after a tombstone and rejects premature ownership by the fresh destination.
An additional later-interval control routes a marker after `c` to existing owner
11 and rejects constant routing to the first owner 10.
Thus the difference in operation order is addressed within the raw endpoint
model. Source slice-tree routing, instance separation, and final detachment
still need their global correspondence argument.

The parent's pinned `physical-replay-controls.mjs` adds three direct source
primitive observations. Its RGA fixture builds roots `d,a`, the run `bc` under
`a`, tombstones `b`, and inserts `XY` after hidden `b`. The hand-derived
physical order `[2,3,10,11,4,1]` and text `aXYcd` agree with the origin-tree
fixture and reject appending `XY`. Two further fixtures integrate a new marker
before invoking the actual source `textSliceContainsItem`: a marker after
hidden `b` routes left, while a marker after the existing boundary routes
right. Opposite-owner negatives and marker-retention checks distinguish both
interval choices. These validate narrow primitive calculations against pinned
source; they are not complete client-issuance or reachability certificates.
The already passing run was inspected without repeating it.

## Typed physical replay integration

`NotionCorePhysicalReplay.lean` now connects the previously separate origin-tree
and endpoint representations. Source sessions are UTF-16 unit lists. Their
semantic names use `Encodable.encode`, whose injectivity supplies
`localId_injective` and `address_injective`; the event constructor cannot alias
START. The encoding is explicitly a name encoding, not an order embedding.
All source comparison obligations remain on source IDs before encoding.

`physical` augments the encoded tree preorder with the virtual START atom.
`physical_origin_index` proves the corresponding index offset, and
`tree_insert_physical` derives exactly the physical splice used by the endpoint
machine from actual tree insertion. It assumes origin presence and structural
child dominance, not an output-state or rendering equality. The insertion
theorem itself yields a successful physical result; complete parent-map
extraction and source-replay establishment of its premises remain separate.

`tree_insert_partition` and `tree_split_partition` start with an input
physical-state coupling and represented endpoint partition. They derive the
raw accepted transition, preservation of that partition, its actual extracted
cells, and equality of the new physical state with the inserted tree's encoded
preorder. The source insertion transition is named explicitly; fresh source
IDs transport to unique, disjoint semantic addresses. The input coupling is a
representation premise, not the desired output equation. `initial_coupled`
checks it at the empty-instance state.

`tree_marker_routes` additionally transports the integrate-then-route result
to the actual post-marker tree traversal with the old endpoint table. This
closes the earlier order-of-operations mismatch in the coupled tree/endpoint
models. The encoding control distinguishes equal-counter sessions and START;
the physical START control distinguishes actual inserted text from retaining
only the sentinel.

The remaining gap is no longer merely that the tree and partition results live
in different typed universes. They now have explicit typed step-coupling
theorems. What remains is establishing the coupled, ordered, dependency-closed
states from JavaScript parent-map replay and honestly generated transactions,
deriving allocation freshness/dominance and semantic admission on those states,
and connecting global slice/block ordering and the same-witness RA criterion.
The module does not claim these premises already follow from real issuance or
that arbitrary raw received messages satisfy them.

The frozen physical-replay module and the updated marker-routing partition
module independently compile cleanly. All printed integration/routing theorem
dependencies are standard logical axioms. The final whitespace check passes;
no additional oracle runs were performed for this integration review.
