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

## Issuance and sorted-prefix structural challenge

The next candidate claim is structural: a dependency-closed version of honestly
issued core transactions, replayed by source key, has known non-START origins,
globally fresh item IDs, and a new first item greater than every old child of
its origin. Each dependency is a whole transaction known when the issuing
client prepared its request. Honesty additionally requires one persistent,
serialized allocator per session. The falsifier would be one such closed
version/prefix violating any of those checks. The formal oracle is the proposed
mint-past/complete-run issuance model; the reality oracle here instruments the
pinned source's actual RGA entry points during `CrdtDocument` reconstruction.

`replay-prefix-instrumentation.mjs` creates one nine-event directed network,
starting with the actual grouped `createInitialTransactions` bootstrap. Actors
use session A, an emoji, and U+E000. Transactions include overlapping-clock
multicharacter runs, insertion after an internal bootstrap atom, insertion
after the start marker of a moved slice, concurrent split/insertion, and
receipt followed by a later split. Dependencies are recorded from each issuing
replica's entire transaction map immediately before the request. Repeated
delivery is exercised; empty insertion and deletion are checked to publish no
transaction and leave the source clock unchanged.

The harness enumerates every subset of those nine events, retains all 40
dependency-closed subsets, sorts each with the actual source comparator, and
replays every whole-transaction prefix. This gives 238 prefix replays, including
repeated/empty prefixes rather than 238 distinct version sets. At the pinned
`RgaText.insertRun` and `insertSplit` entry points it checks origin presence,
cross-instance item-ID freshness, and strict child dominance. The original
integration/traversal methods still perform the operations. Every completed
integration also has all stored items reachable in actual source preorder.
The run passes 646 RGA-entry checks, 661 old-child dominance checks, 398 checks
that the issuer knew the whole run of an internal child, and nine internal
origin checks. The literal ledger and counts are retained in the separate
observations file.

A distinguishing witness rejects a stronger shortcut: a new U+E000-session
item at counter 4 is integrated with an A-session item at counter 5 already
stored. The former still dominates every relevant child of its own origin.
Hence being greater than every stored item is unnecessary and does not follow
from sorted transaction-first keys. Complete-run receipt, rather than a global
maximum argument over the replay prefix, is needed for internal-run children.

The broken controls detect an unknown-origin message set, a deliberately
non-dominating raw insertion, and two concurrent Replica instances reusing the
same session with different payloads. The latter are both accepted local API
calls but collide on receipt: the public constructor does not enforce the
environmental single-allocator discipline. The missing-origin and dominance
controls are rejected by the instrumentation's structural assertions, not by
a claim that the source itself enforces closure or immediate-splice legality.

This finite experiment supports the exact proposed structural claim on one
adversarial network; it does not prove it for all source executions. Whole
version union can preserve recorded dependency closure, whereas arbitrary raw
individual message receipt need not. A source-to-ghost provenance argument must
still show that selected non-START origins come from known complete insertion
runs or split transactions and derive closure, allocation freshness, and
dominance from issuance. Bootstrap's create and insertion share one key but
create adds no competing RGA item. Empty requests contribute no event. These
are encoding and issuance obligations, not failures of the candidate structural
claim on the tested domain.

## Mint-past issuance and canonical replay review

`NotionCoreIssuance.lean` records each reservation's actual pre-mint received
run list and references. Whole-peer exchange imports a complete received
version; it does not admit arbitrary isolated message receipt. `peers_closed`
derives mint-past dependency closure from those operations, rather than placing
closure in the mint guard. `closed_union` and `closed_intersection` preserve
that property for lists relative to the same global record set. These are
closure results, not an ordinary or recursive-base RA certificate.

`replay` filters the unique globally minted record runs by a version and uses
an actual source-key merge sort. Ghost past/reference fields do not affect
sorting. `replay_ordered` combines sortedness with allocation-derived key
uniqueness to obtain strict order; no ordered-list premise is supplied to the
canonical readiness theorem. `past_in_prefix` uses that order and the complete
past-run maximum bound to show every provider precedes the next transaction.
`replay_ready` consequently places complete referenced provider runs in every
actual canonical replay prefix. `replay_child_dominance` separates first items
from internal children, using sorting for the former and reference-derived
whole-run ownership for the latter. Its internal-child predecessor reference
must still be obtained from actual origin edges.

The review found an important type distinction: allocation `Known` alone
includes create/delete reservation IDs that have no physical RGA item. The
parent refined records with an item-producing tag and strengthened mint
references to `ItemKnown`. `record_reference_births` and `replay_item_ready`
now return a provider explicitly tagged as producing the referenced item.
The metadata control checks allocation knowledge together with absence of
item knowledge. The existing targeted network separately checks that its
received delete transaction key is absent from every actual source RGA item
map. The rerun retains the same nine events and structural counts and adds
only that assertion; no larger network or broad suite is introduced.

The tag is an abstract birth declaration. Source payload decoding must still
show that insertion/split transactions produce their reserved items and
create/delete/empty-bootstrap reservations do not. The model does not inspect
payloads or derive references from `locateInsertion`/range selection; those
remain typed source-to-issuer correspondence obligations. The corrected
readiness theorem must not be described as proving concrete parent-map origin
presence without that connection.

The controls use a reachable complete two-item run, a later referencing mint,
canonical ordering different from receipt order, and a negative dependency
closure example for isolated delivery. They reject unknown references and
metadata IDs as item origins. No desired edit result or final document
invariant appears in issuance guards. Within the explicit session/whole-version
discipline, the claim is substantive source-key/provenance reasoning rather
than set-union convergence alone.

The tagged issuance module independently compiles cleanly. Printed closure,
provider-readiness, and child-dominance dependencies are standard logical
axioms only. The targeted deletion-reservation assertion also passes against
the pinned source; syntax and whitespace checks remain clean.

For the upcoming slice-forest result, creation appends the fresh title in the
search forest. This matches source `this.blocks.set` and `#allNodes` iteration
over `this.blocks.values()`. The separate `blockOrder.splice` controls display
order after the selected block. Appending in the search forest is therefore
not a source-search ordering mismatch; the displayed-order representation and
projection still require a separate list and correspondence argument.

## Parent-map extraction and slice-forest induction

`NotionCoreParentMap.lean` now stores physical items with explicit origin links,
enumerates children from that raw table, sorts their IDs with the source
comparator, and performs lookup during fuel-bounded traversal and extraction.
The structural `ForestModel` uses actual lookup, adjacency-key permutation,
and descending sibling order; it contains no traversal equation.
`extract_model` derives exact forest recovery at a sufficient structural height.
The stronger `extract_raw_model` computes a bound from the table's maximum
counter and derives a model directly from unique IDs and strictly increasing
origin counters, without assuming a chosen forest.

The raw integration reachability relation guards fresh IDs, known parent
membership, and strictly increasing counters. Its induction derives uniqueness,
counter increase, and parent closure. Closed increasing tables have a path from
START for every row, so `reachable_extraction` derives complete stored-row
coverage rather than merely a rooted subset. These are structural input guards,
not the desired extraction or visible editing result. Source issuance still
must establish those guards; the mint reference-counter result supplies part
of that connection but does not itself decode transaction payload rows.

`runRows` matches the actual preceding-item links of a run. The recursive
insertion edge lemmas and `fresh_run_edges_any` preserve exact parent-record
permutation, including START insertions. This is valuable parent-edge coupling,
but `ParentEdges` alone does not imply `ForestModel`: the same parent edges
can be enumerated in the wrong sibling order. Ordered-forest preservation and
its connection to extracted source traversal remain explicit integration
obligations. The tombstone/marker traversal fixture rejects map iteration
order and empty visible text. The orphan fixture shows a stored unreachable row
is omitted by START traversal and lies outside the closed reachability domain,
matching raw source acceptance rather than pretending it rejects the row.

`NotionCoreSliceForest.lean` gives arbitrary rose-tree operations for source
split, recursive marker routing, detachment of the complete child subtree, and
append to a fresh title. The normal form is a predicate on those arbitrary
trees, not built into their transition guards. `splitDetach_normal` derives
which source was selected and why the moved subtree is a leaf at a normal
atomic boundary. `atomicSplit_result` describes the resulting forest from
actual accepted search/detach/append. Its intermediate tree can have another
level, so normal form is asserted only after the transaction's detachment.

The global invariant combines tree shape, unique block profiles, active
instance ownership, and physically empty inactive title instances. Creation,
active-instance update, and atomic splitting preserve it. `Reach` guards fresh
marker/block names, the instance addressed by an update, and actual accepted
split execution; it does not guard output normal form or empty titles.
`reachable_invariant` derives both. The update's physical contents are arbitrary
here: that theorem is a frame argument, not proof of RGA/endpoint validity or
correct text. The separate physical-replay and partition invariants still need
coupling to this forest relation.

The three controls check actual split/detach/append rather than retaining the
right leaf under the old root, establish a concrete reachable split state with
an empty inactive title, and repeat splitting inside an inherited interval.
Their negative views/structures rule out leaving both titles empty or treating
the second split as a no-op. They do not claim global displayed block order.
Search forest order is source Map insertion order; the separate display-order
list still needs projection. Together these developments remove assumed raw
graph coverage and assumed atomic-boundary tree shape in their respective
structural models, while keeping their source/issuance integration scope clear.

The final issuance, parent-map, and slice-forest candidates independently
compile cleanly. Their printed theorem dependencies are standard logical
axioms only; no new admissions or axioms are introduced. The review found no
circular desired-output premises. Whitespace checks pass. The targeted
metadata-item assertion is the only oracle extension in this final review;
the passing broad suites were not repeated.

## Parent traversal coupling and typed payload review

`NotionCoreParentCoupling.lean` closes the earlier gap between an exact
permutation of parent rows and the ordered recursive forest model. Its
`edges_model` derives the model from unique row IDs, exact parent edges, and
recursively descending sibling IDs; the conclusion is not a premise.
`appended_run_traversal` then couples the actual appended parent rows to the
actual accepted recursive insertion and derives their entire traversal equality.
Fresh/disjoint output IDs, origin acceptance, and child dominance remain explicit
inputs. The hidden-origin control gives aXYcd and rejects a misplaced appended
XY. A second control preserves exactly the same edges under the wrong sibling
order and rejects the resulting traversal: edge membership alone is insufficient.
The module independently compiles; printed dependencies are standard logical
axioms only.

The independent review of `NotionCorePayload.lean` finds the typed atomic
expansion aligned with the pinned core dispatch: bootstrap creates then inserts
under the shared A@1 key; split creates, inserts its marker, then moves its
slice. Item-production tags and reservation widths are derived from payloads.
The birth-membership theorem therefore excludes create/delete reservation IDs
without a caller-supplied birth flag. Pending tombstones affect text births;
markers remain hidden split items. The clock fold includes empty bootstrap's
transaction key. Ordinary empty insertion/deletion emits no transaction.

This remains a typed decoder boundary. Source iterator elements are opaque
values, not validated Unicode scalars; concatenated string projection can fuse
separately stored surrogates. Expanded deletion ranges, selected block/instance
identities, source block-name injection, and wire parsing are not derived here.
`prepare_admitted` establishes allocation/issuance admission given known RGA
references; it does not establish block existence, same-instance ownership,
display predecessor validity, or successful source execution. Block-creator
provenance is separate from item references. Pointer/path/search-label fields
are irrelevant to the modeled core dispatch, but actual source mapping rebuilds
can reject duplicate search labels; the observed runtime exception boundary
has not become an unconditional typed execution theorem.

Search enumeration still follows the source blocks Map insertion order, while
displayed order follows its separate blockOrder list. A faithful combined state
needs both lists, with per-instance parent rows and endpoint ownership attached
to active forest leaves and empty inactive title instances. Appending a newly
created title to the search forest cannot itself establish display order.

## Located typed archive provenance

`NotionCorePayloadNetwork.lean` independently builds cleanly (569 jobs).
`replay_located_provider` derives a provider transaction in the actual canonical
prefix whose births contain the requested instance/item pair, with the complete
provider reservation ending before the consumer key. `reference_provenance`
records the provider's receipt at emission and preserves it through archive
extension and whole-version exchange; replay order is derived through the
existing issuance theorem. Neither a free item-production flag nor a provider
ordering premise is introduced. Its printed dependencies are standard axioms.

The remaining trust boundary is explicit in `Reach.emit`: the client supplies
located birth membership for its selected references. This excludes global-ID
membership in an unrelated instance, but does not derive positional selection,
instance/block existence, or source dispatch success from a joint interpreter.
Birth addresses use a false tombstone environment because existence and
instance ownership do not depend on deleted flags, including pending text
births. Empty bootstrap has no item references or births, and remains distinct
from ordinary empty requests.

The pinned runner's three new `payload-provenance-controls.mjs` records pass
with all seven source hashes checked against `sources.json`; literal records
are retained in `payload-provenance-observations.jsonl`. The honest two-instance
history shows its inserted ID in exactly one instance and rejects the other.
A separately labelled fabricated future-target deletion confirms text births
are tombstoned while split markers stay undeleted; it is not claimed honestly
issued or dependency closed. Honest empty insert/delete requests leave the
clock and archive unchanged, and the next key is P@2 rather than P@4. Each
control includes a hand-derived positive and a distinguishing negative. No
broad oracle suite was repeated.

The final typed-network extension was independently rechecked with Lean.
`birthAddresses_deleted` proves instance/ID addresses unchanged for every
pending-tombstone environment; it does not assert unchanged visibility.
`birth_ids_unique` derives per-payload uniqueness from consecutive counters.
`prepared_births_fresh` quantifies over **all** earlier archive entries, not
just the issuing peer's received subset: record publication supplies global
allocation membership, unique reservation ownership forces any collision into
an identical run, and fresh transaction keys exclude that run. Thus unreceived
transactions are covered under the existing single-writer session allocator
model. This adds no freshness premise to the prepared transaction.

The provider conclusion still contains the complete instance/item address,
not merely its globally unique ID. The added controls distinguish wrong-instance
presence, an overlapping reservation key, and reverse replay order. They retain
hand-derived PASS+FAIL structure. No circular desired-state premise or weakened
same-instance conclusion was found; the source-selection and wire boundaries
recorded above remain in force.

## Separate search and display order

`NotionCoreDisplayOrder.lean` models fresh source creation as append to the
search forest and a literal indexed splice in the separate display list.
Absent and missing predecessors both choose index zero, exactly as raw
`#createBlock` does. The existing SourceDocument/CoreSpec creation relation
rejects a missing `some` predecessor, so this new raw fallback is not presented
as an unconditional refinement of that relation. Revival of existing blocks,
source name encoding, truthiness of source strings, and deletion are outside
this fresh-core operation.

Creation derives unique search names and a display/search permutation from
freshness and input alignment. Materialization finds each display ID in the
actual search forest and selects its active leaf. Unique-key lookup is proved
from list membership, and canonical materialization is derived equal to the
forest's active-leaf projection. The display materialization permutation
therefore relates actual lookups to that projection, with no desired display
equality premise. It does not yet render endpoint contents or derive a full
client command trace refinement.

Hand-derived controls distinguish concurrent creates' search order [1,2,3]
from display [1,3,2], reject append-on-missing-predecessor, and exercise actual
SliceForest splitting twice at markers 3 and 4. The second split routes through
an inherited interval even though both destination creations requested the
original block as predecessor. Materialization returns active starts in display
order START, marker4, marker3 and rejects the unused fresh title starts. These
checks separately exercise routing and lookup rather than echoing displayed IDs.
The module checks with standard logical axioms only and no admissions.

## Typed parent provenance and existing-item deletion

The frozen `NotionCorePayloadParents.lean` and `NotionCoreParentErase.lean`
independently check cleanly, with standard printed axioms. `birth_parent`
extracts first/external versus subsequent/internal parent links from literal
payload expansion. For an old internal child, equality with the consumer's
selected origin derives that the preceding old-run ID is a consumer reference;
no additional caller-supplied internal-origin premise is introduced.
`replay_child_before` then uses complete-provider clock bounds for internal
children and transaction ordering for first children. `prefix_ready` derives
the actual recursive readiness predicate from those row edges. It still takes
input table/tree edge coupling and the fresh tree's first ID as explicit
representation assumptions, rather than deriving a combined interpreter.

`prefixRows` enumerates filtered archive entries, newest first, with rows in
payload order. This is not the source RGA Map insertion enumeration. It is a
finite parent-table view used through exact edge membership/permutation;
source traversal sorts children by IDs, so a separate coupling can justify
order-independent traversal under uniqueness. No theorem here asserts literal
Map iteration equality or handles duplicate fabricated archives. Pending-delete
flags remain parametrized; the archive view alone does not maintain that set.

ParentErase maps existing text tombstones while preserving IDs, origin links,
markers, and recursive child structure. The updated traversal equation is
derived through edge coupling, uniqueness, and sibling order, not assumed.
Its controls distinguish retained live descendants from subtree removal and
reject converting a marker to deleted text. Future-target pending deletes are
explicitly outside this update. The updated DisplayOrder split control now
also computes its displayed IDs through the two actual insertions, eliminating
the earlier literal display fixture as a setup premise.

The source search-label experiment was cross-reviewed without rerunning it:
8191 canonical paths through depth 12 and twelve honest split/move
reconstructions are bounded evidence, not a Lean injection theorem. The LL/D
alias distinguishes noncanonical strings from generated canonical labels.
Honest reconstructions execute the source duplicate-label assertion
successfully; that does not reproduce a throwing duplicate-state exception.

## Derived replay graph guards

`NotionCoreReplayGraph.lean` independently checks cleanly with standard printed
axioms. Its global archive-birth uniqueness induction uses the previously
derived freshness against all prior entries, including unreceived transactions.
Instance and version selection are sublists of those IDs, so `prefix_unique`
requires no graph uniqueness premise. Strict counter increase follows literal
run predecessor links, positive issued keys, and external-reference counter
causality; no rank premise is supplied.

Closure has the stronger, appropriate domain: `prefix_closed` requires that
the selected runs are an actual prefix of canonical whole-version replay.
It derives external parents from a located provider in an earlier prefix and
internal parents from births of the same complete atomic payload. The full
instance/item address is retained, and tombstones do not remove parent rows.
Arbitrary selected subsets get uniqueness and increasing edges, but are not
claimed closed. This distinction is preserved in `prefix_graph` and
`canonical_graph`; their conclusions are not caller premises.

The two PASS+FAIL controls test literal prefix row decoding and retained
marker/hidden-parent edges in the inherited instance. They do not themselves
construct Reach witnesses or prove a source Map enumeration equation. The
archive representation and joint-interpreter boundary described above remain.

## Extraction edges and combined-machine draft audit

`NotionCoreExtractionEdges.lean` independently checks cleanly. Its exact
row permutation follows unique table lookup, increasing parent counters,
closed origin membership, and the actual raw extraction. Extracted ID
uniqueness is derived by multiplicity recurrence and backwards counter
induction, rather than assumed. Prefix extraction and readiness then consume
the derived graph guards; callers no longer supply the extracted forest or
its edge-coupling equation. The orphan control correctly demonstrates why
closure is necessary, and the hidden-parent/marker control distinguishes
physical traversal from archive enumeration.

The combined Machine draft was separately audited against pinned dispatch.
Existing-ID integration must compare kind, ID, origin, and content while ignoring
tombstone status; the revised definition does so. Existing-block creation must
return without reordering; the revised definition does so within its typed
same-title domain. The split/insert fixture's hand calculation places C@4
before sibling B@4, hence inserted X on the left of B's split marker. Source
split immediately validates only the two resulting slices; a global forest
bounds check is a stronger malformed-state boundary. Source constructor sorts
transactions, while draft replay consumes supplied order. Its sorted-input,
closed-graph, typed-title, search-label, and whole-construction exception
boundaries must remain explicit. This draft audit is not a frozen-machine
compilation certificate.

The concrete control reduction problem was isolated independently: even
`#reduce sortChildren [A@2,B@4]` leaves mergeSort's well-founded Acc.rec.
This is a kernel reduction obstruction in the sorter, not evidence that the
hand-derived expected text is wrong. Rewriting by proved merge-sort equations
or its proved insertion-sort equality is appropriate; native execution would
not replace the requested kernel evidence.

## Frozen machine and directed endpoint adjacency evidence

The current Machine and MachineRows independently compile cleanly. All printed
machine control dependencies are standard logical axioms, with no native
execution shortcut or admission. The insertion-sort evaluator is proved equal
to the existing merge-sort traversal and makes branching controls kernel
reducible. MachineRows derives actual checked-loop append from fresh/disjoint
IDs and increasing parent counters; an output update equation is not a premise.
The typed-title, ordered-replay, malformed global bounds, source string decoder,
and search-label boundaries identified in the draft review remain explicit.

The new pinned-source `endpoint-adjacency-controls.mjs` saves six literal output
records. It checks 144 instance states over four dependency-closed versions
containing neither, either, or both concurrent splits of a four-atom seed
(including an astral Unicode iterator atom). Directed local followups delete
all visible text, insert a two-atom run after hidden origins, split with an empty
left side, and split an inherited interval again. Grouping stored slice
references by instance and sorting by physical start yields START first and
each stop equal to the next start or END throughout. Source hashes are checked
by run.py; this is bounded directed evidence, not exhaustive validation.
The incomplete individual-receipt control creates an instance without covering
slices and rejects the same coverage condition, confirming the closed-version
domain. No new honestly reachable core counterexample was found.

The quantifier needs care: inactive fresh title instances have no active leaf
in their own instance after attachment, although their stored START-to-END
root covers a physically empty RGA. The tested formulation includes all stored
slice refs and the empty title intervals. A formulation using active leaves
only must restrict to active instances and separately require empty inactive
titles. Search Map order and displayed order are both irrelevant to endpoint
adjacency; physical start order is the appropriate ordering.

## Final checked integration and slice extraction review

The final Machine adds meaningful kernel PASS+FAIL controls for duplicate text
integration preserving an existing tombstone and existing-block creation
preserving placement. These pin the two source semantic mismatches identified
in the draft audit. MachineRows' fresh/increasing append result remains unchanged.
The frozen MachinePrefix and MachineSlices independently check cleanly; their
printed dependencies are standard logical axioms.

MachinePrefix derives fresh transaction row uniqueness and rank, then separates
its IDs from the canonical prior prefix through global reservation ownership
and strict replay order. Old and fresh tombstone environments are independent;
separation does not assume identical deletion flags. The permutation variant
supplies only an input row representation, not a view or accepted-step premise.
It derives acceptance by the actual Machine integration loop, while retaining
the stated remaining obligation to derive that representation for complete
Machine states. Concrete controls test hidden origins, internal run links,
newly tombstoned births, and bootstrap's shared key without metadata births.

MachineSlices derives successful checked extraction from full input physical
factorization, unique addresses, actual instance presence, and the next physical
stop. Its premise is a structural input layout, not the desired extraction
answer. It derives both bound checks and exact interior atoms, including legal
empty interiors. The cell theorem obtains factorization from partition flatten;
that partition relation is still an invariant obligation for full replay.
Empty inactive titles explicitly require their instance and sole virtual START,
and attached-tree extraction combines that empty root with the actual inherited
cell lookup. The controls reject reversed bounds and omission of the physical
stop, rather than merely checking unchecked extraction. Their raw slice fixture
uses text IDs as endpoints; this checks the extraction API boundary and is not
claimed to be a honestly generated split-title shape.

The directed 144-instance adjacency evidence above supports the proposed full
replay invariant without replacing it. Its stored-root versus active-instance
quantifier distinction and incomplete-receipt negative remain necessary. No
additional broad campaign was run during these final component reviews.

## Honest client selection and creator domain controls

Three new directed pinned-source controls in `client-provenance-controls.mjs`
pass with literal records retained and all source hashes checked. Public
`Replica.createBlock('missing')` throws before clock reservation or archive
change. A separately labelled fabricated raw create payload with that missing
predecessor succeeds in CrdtDocument and inserts at the front. Thus the valid
public request domain and raw document-dispatch fallback are distinct; neither
is misreported as the other's rejection behavior.

For both visible and all-deleted inherited intervals, zero-index preparation
selects the original instance's split-marker boundary and excludes the unused
fresh title instance. A following honest insertion materializes in the selected
block. Positive preparation in a locally unsplit abc block selects the visible
predecessor b and its actual text instance, establishing concrete local item
provenance.

The concurrent split control rejects a stronger replay-time block guard:
A splits abc at 1 and B independently splits it at 2. B's local predecessor b
belongs to the requested original block when issued; after A's earlier
canonical split it belongs to A's new block before B replays. Both requests
are honestly issued and locally valid, and the final text is a|c|b. Requiring
replay origin ownership to equal the original requested block would therefore
reject an honest core transaction. Same-instance located birth provenance is
preserved; block ownership can change concurrently. This is a guard-strength
counterexample, not a violation of the ordinary local positional contract.
No broad suite was repeated.

## Creator admission and actual client locator review

CreatorNetwork independently checks cleanly with standard printed axioms.
It strengthens admission over the existing typed archive state rather than
silently changing its earlier Reach relation. Required block and instance keys
obtain metadata creator providers in the saved emission past, hence in the
canonical prior prefix. Metadata creator births remain distinct from RGA item
births. The old-admission countermodel includes actual witnesses for both
unseeded transactions and an actual failed Machine replay; its stronger Reach
exclusion belongs to the theorem layer. Creator presence alone is not claimed
to establish active-gap selection or replay progress.

MachineClient's definitions were audited against pinned local preparation.
Actual arbitrary-tree preorder extraction supplies visible character indexing,
zero-position first-visible/final-fallback selection, and positive visible
predecessors. The attached selection theorem derives an independent PreparedGap
from physical cell factorization, empty title ownership, real unique-key forest
membership, and an in-range index; no selected-address or desired-gap premise
is supplied. Internal semantic name decoding is roundtripped, not equated with
source string parsing. Nonnegative deletion selection matches JS slice clamping;
negative/fractional indices, per-instance grouping, compressed ranges, and
transaction/clock issuance remain separate. Known forest predecessor is the
public create check in this core with no removed blocks. Invalid selections
return none here, abstracting source exceptions rather than preserving their
messages. The controls' inherited-marker and visible-predecessor expectations
match the new pinned source controls above.

An independent draft compilation caught a neg-case simplification failure in
`locate_member`: flatMap length was normalized before its original bound could
rewrite the if. The owner repaired it, and the final expanded MachineClient independently
checks cleanly below; this records the resolved draft failure.


## Final actual-storage creator and locator coupling

MachineCreators and the expanded MachineClient independently check cleanly,
with standard printed axioms and the earlier locator draft failure resolved.
MachineCreators derives actual forest names from successful operation effects;
split, detach, and append preserve block IDs. It similarly derives actual
instance keys from decoded operations, including insert/erase allocation.
Received transaction/archive linkage then supplies creator knowledge: created
keys use their own received emitter, while required keys use saved creator
provenance and closure of the received version. No caller creator guard appears
in these retrospective conclusions. Accepted current replay remains explicit;
there is no assertion that every admitted replay succeeds.

MachineClient derives requested forest membership and selected instance
presence from actual successful lookup and checked slice extraction.
`located_creators` uses those storage facts, MachineCreators, and internal
name decoding to derive known creators for both requested block and selected
instance. The prepared create/insert/split theorems discharge metadata creator
requirements for actual client preparation. They do not yet discharge selected
RGA item birth membership, establish replay progress, or assert replay owner
equals requested block. The latter stronger condition is refuted by the honest
concurrent source fixture above. Acceptance of the client's current document
is distinct from acceptance of its newly issued edit or a future merged replay.

Both root-only and attached selection theorems derive successful source-style
location and independent semantic gaps from physical cell representation,
unique real forest membership, existing instances, and in-range indices.
Attached selection additionally checks the empty inactive title. The internal
codec roundtrips remain separate from source wire names, and deletion still
models selected nonnegative addresses before source operation grouping and
range encoding. These limits are unchanged by the creator coupling.

## Focused deletion grouping and range evidence

The pinned `delete-group-controls.mjs` saves five passing literal records.
An honest inherited interval receives concurrent XY and UV runs from sessions
😀 and U+E000 at the same counter. Its physical text is UVXYcd, whereas ID range
compression sorts selected IDs by counter and UTF-16 session order. Clamped
selection [1,99) produces exactly seed@4..5, 😀@7..8, U+E000@8 after range
expansion: this order differs from physical selection, but the ID sets agree.
The sole emitted group names the inherited original instance, excludes the
empty destination title and split marker, and leaves U. A second deletion
selects only visible U, excluding the prior tombstones.

Equal, beyond-end, and reversed nonnegative ranges emit no transaction and
leave both clock and archive unchanged. Marker kind and undeleted status are
pinned with negatives. The expected IDs, ranges, and text are hand-derived;
all seven pinned source hashes are checked by run.py. This is focused evidence
for target selection/encoding, not a new broad campaign.

Source grouping uses a Map keyed by text instance in first occurrence order,
then compresses each group's IDs independently, reserving one transaction key.
Under the core normal form, a block has one populated active instance plus at
most an empty inactive title, so each nonempty honest core deletion has one
group. This fixture does not claim coverage of multi-instance selection after
merge/move extensions. Negative/fractional JS indices and wire parser validity
remain outside the nonnegative typed client domain.

## Actual selected-item birth guards

MachineBirths and the latest MachineClient independently check cleanly with
standard printed axioms. MachineBirths follows actual successful storage updates,
including duplicate integration, append, text erasure, and inherited marker
integration. It derives that every resulting stored ID has a birth in the same
instance from a transaction of that replay. Finite traversal membership then
traces back to an actual row without graph uniqueness or closure assumptions.
Receipt/archive linkage supplies located item knowledge; no birth provider or
known-item guard is a premise.

MachineClient now proves that successful checked extraction includes only
physical atoms and a physically present start, and that actual location selects
a physical address in its selected instance. For a decoded non-START address,
MachineBirths and internal decoder injectivity derive the corresponding received
located birth. The virtual START case cannot masquerade as an item. Consequently
actual prepared insert/split payloads discharge every located-reference guard;
START origins correctly have no item-reference requirement. This closes the
previous caller-supplied selected-item membership boundary for accepted current
Machine reconstructions. It does not establish acceptance of the next edit or
future merge, source wire decoding, or a global endpoint partition invariant.
The accepted current replay premise is explicitly retrospective, and concrete
machine/client controls supply nonempty instances of that domain.

## Reconstruction, deletion codec, and concrete network review

Reconstruction and Ranges independently check cleanly with standard printed
axioms. Reconstruction filters actual published typed transactions by whole-run
receipt and sorts by source transaction key, erasing archive/Replica Map
enumeration differences. Its transaction-to-run projection equals the existing
canonical replay exactly, and receipt linkage is derived internally. Reachable
archive uniqueness supplies the source immutable transaction-map discipline;
arbitrary duplicate fabricated archives and JSON payload equality remain outside
this correspondence.

Ranges follows source counter/session sorting and the same-session consecutive
range extension condition. The reverse accumulator changes storage only.
Expansion after compression equals the entire sorted input list, including
duplicates, rather than merely its set. Erasure and pending-deletion membership
then transport through that permutation. Source safe integer/positive-ID and
string decoding remain typed-wire boundaries.

The current deletion definitions select actual visible clamped addresses,
decode the first instance, and validate every target in that same instance.
Mixed-instance input fails as a whole rather than truncating a prefix. This is
an explicitly partial core preparation, not the generic source's Map grouping
for multiple populated instances. Sorted expanded targets intentionally differ
from physical character order. Physical membership and decoder provenance
derive every target's located birth and required creator. The focused Unicode
range fixture above supplies direct source evidence for this distinction.
The final deletion module independently checks cleanly, including controls
repaired by proving actual replay equals their explicit hand-derived states
and using codec roundtrip equations. Its draft control failures are resolved.

MachineNetwork's initial draft reconstructed before empty-request checks. The
review identified source's empty insert and equal-range delete early returns;
the owner added Request.earlyNoop before reconstruction. This is a corrected
model draft, not a demo defect. Other empty clamped ranges still require actual
selection. Concrete issue combines reconstruction, selection, and reservation,
and its successful transition derives item/creator admission rather than asking
for those guards. Its Reach relation admits successful requests, whole-version
exchange, bootstrap, and clock gaps; it does not prove reconstruction or valid
request progress. Source raw individual receipt, wire exceptions, and arbitrary
malformed-state execution are not equated with this successful typed network.


The frozen deletion controls retain source-sorted target order, inherited
instance ownership, and explicit whole-selection rejection for mixed instances.
Their literal states are connected to actual replay by kernel proofs, not
supplied as execution assumptions. The Network definitions' early-noop ordering
is now source-aligned. A current independent draft compile found multiline
case-expression parser failures in its admission composition and reported them
to the owner. These draft failures are now resolved: the final Network
independently checks cleanly with standard printed axioms and no warnings.
Its early_noop theorem holds for every network without a reconstruction
acceptance premise. The request control additionally pins the complete two-item
reservation ending at clock 4, excluding START-origin selection. Successful
request reachability derives creator and issuance reachability; reconstruction
and future replay progress remain explicit open obligations.


## Parent integration and repository gates

The parent inspected the stored-ID induction, exact range codec and literal
source fixtures, then connected selection to actual received reconstruction.
All positional request branches derive item and creator knowledge; no branch
accepts those guards from its caller. Independent review caught the early-noop
ordering mismatch, which was corrected before verification. The final request
control checks a nonempty positional insertion, its two-item clock reservation
and a negative against selecting START. The mixed-instance deletion control
asserts full rejection rather than merely excluding one truncated result.

The complete research gate passed 40 modules (3,451 Lean jobs) and fourteen
result groups, including five new deletion records. The production gate passed
3,694 Lean jobs, 18 exact public contracts and their axiom audit, 187 runtime
tests and validation of 569 stored benchmark records. No admits, custom axioms
or native decision shortcuts were introduced. These gates do not establish
whole replay progress, source wire/label correspondence or the Notion RA
certificate. The three confirmed demo bugs still reproduce.

## Full stored-field replay prefix evidence

The existing nine-event directed campaign was extended, retaining its original
observations and saving three new records in `replay-table-observations.jsonl`.
All 40 causal ideals and 238 canonical atomic prefixes compare actual source
Map tables to an independent decoder of literal transaction payloads: 293
instance tables, 1534 stored rows, and 27 tombstoned row occurrences. The
comparison includes full IDs, origins, kind, text content, deleted flags, and
pending-delete membership. Expected births use explicit consecutive counters
and predecessor links; deletion ranges are expanded by literal integer loops,
without source codec helpers, RGA methods, traversal, or selectors. Each text
birth's final flag reflects all prefix targets in that instance; split births
remain undeleted. Empty creator instances and chronological Map row order are
included, rather than comparing only physical traversal or ID sets.

All comparisons pass with pinned hashes checked. Known-broken no-op deletion
and wrong-instance variants are rejected. A separate fabricated raw
pending-before-birth control confirms deleted Q text and an undeleted split
marker when both IDs were targeted beforehand. It is explicitly outside honest
causal closure. This supports the proposed deletion-aware complete-row prefix
representation on the bounded campaign; it is not a universal invariant proof,
a malformed duplicate-content integration theorem, or a new source bug claim.

## Declarative table view and canonical archive order

TableView, ArchiveOrder, and MachineTableGraph independently check cleanly,
with standard printed axioms. TableView is a declarative storage layout:
chronological decoded births erased by all prefix targets in that instance.
Its algebra includes pending deletes before births and leaves markers unchanged;
it is not a second document replay or a sequential editor specification.

ArchiveOrder derives transaction-key uniqueness from issuance Reach and proves
that a canonical transaction prefix is exactly a permutation of its selected
archive entries. The chronological birth-row permutation and global birth-ID
uniqueness then follow. No row permutation, graph uniqueness, or provider-order
premise is supplied to these canonical-prefix results. MachineTableGraph uses
that derived permutation with the actual prefix deletion predicate to inherit
unique, increasing, closed parent edges. Its physical uniqueness theorem derives
sufficient actual traversal at table-length fuel and injective event names.
The latter remains a conditional actual-table graph lemma until a replay
representation theorem links the machine's table to the declarative view.

The literal full-field oracle decoder was cross-reviewed without rerunning the
campaign. Expected rows and pending sets derive solely from literal transaction
operations and language-level string iteration, explicit counters, and integer
range loops. Source RGA/selector/codec helpers do not produce the expected
answer. The full chronological Map comparison is stronger than ID-set or
traversal equality, within the honest no-duplicate-birth domain. The no-op erase
and wrong-instance mutations are distinguishing controls, while future-target
raw deletion remains explicitly fabricated.


## Final actual-table integration review

The source reviewer and parent inspected the full MachineTables induction.
Its prior table view is obtained by induction on an actually accepted prefix;
no final row equality or per-step output view is supplied. Fresh row append
follows from canonical birth uniqueness, actual lookup and accepted integration.
Creation and move preserve storage, erasure preserves IDs and parent links,
and the bootstrap and split cases follow their complete atomic phase lists.
Raw duplicate birth replay lies outside the uniqueness premise; canonical
immutable archives discharge that premise rather than assuming it.

MachineTableGraph removes the remaining caller row-permutation premise.
Actual prefix tables inherit unique IDs, increasing parent rank and closure.
Physical traversal uniqueness uses the actual table-length fuel. The next-row
integration and reference-presence results assume only the current prefix was
accepted; they do not assume acceptance of the next transaction. The independent
review found no desired-query or observation premise hidden in this chain.

The pending-list equality is a formal-machine statement. Source pending Sets
correspond by membership; list order and duplicate multiplicity are not claimed
as source observations. Hand-derived controls distinguish pending future text
births, undeleted markers, retained parents and wrong destination instances.
The independent literal decoder compares full source fields and pending Sets.

The final research gate passed 44 modules (3,455 Lean jobs), fourteen result
groups and all saved failure regressions. Prefix instrumentation now emits
three records, adding full-field comparison and a separately labeled raw
pending-before-birth control. The production gate passed 3,694 Lean jobs,
18 exact contracts and their axiom audit, 187 runtime tests and validation of
569 benchmark records. Full joint slice/display progress, source wire/label
correspondence and the Notion RA certificate remain open.

## Complete accepted-prefix tables and all owned slice evidence

MachineTables independently checks cleanly with standard axioms. Its
`replay_tables` derives full actual instance rows and pending targets from
accepted replay plus whole-list decoded birth-ID uniqueness, using actual
storage effects and transaction phase decomposition. It assumes neither the
per-step output equation nor a preselected row representation. The canonical
composition derives that uniqueness from issuance and supplies exact actual
row equality, archive permutation, graph guards, physical uniqueness, and
next-row integration. Next integration takes only the accepted **prior** prefix;
acceptance of the next transaction is not a premise. Next located references
are likewise derived present in actual prior rows. Global slice routing and
whole-transaction progress remain separate.

Lean pending lists preserve deletion chronology and duplicate targets, while
source JS uses a Set. The correspondence is exact membership, not list order
or multiplicity; the concrete marker/repeated-delete control documents this.
The raw pending-before-birth control is an accepted primitive fixture, not an
honest issuer witness. Full honest rows remain chronological Map births with
unchanged parent links and source tombstone semantics.

The all-owned-slice extension of the same pinned nine-event campaign saves
`replay-slice-partition-observations.jsonl`. Across its 238 canonical prefixes,
293 instance partitions and 1827 augmented physical atom occurrences satisfy:
first start START, physical start order, stop equal to the next start or END,
exactly one covering cell per physical atom, and unique owner blocks within
each instance. All stored nodes are included, including inactive empty title
roots. Owner duplication across different instances is deliberately allowed.
A hand-derived split of ab gives two old-instance cells and a fresh empty
START-to-END title cell; omitting that title is rejected. This adds exact
coverage and an empty-title mutant to the earlier adjacency checks, without
claiming a universal invariant or a new bug. Existing observations are retained.

## Forest reference rewrites and conditional owned partition

ForestRefs independently checks cleanly with standard axioms. It derives the
selected preorder context from actual recursive search, rewrites one selected
reference into left/right references, removes the complete detached subtree's
contiguous references, and appends child preorder. No supplied context or desired
projection equation is a premise. The split control retains a preceding empty
title and rejects dropping it. The arbitrary duplicate-name append formula
explicitly updates every list match; source Map uniqueness excludes that malformed
case. Raw detachment has an additional abstraction boundary: SliceForest skips
root matches, whereas source searches all nodes and throws on a selected root.
Core fresh markers and normal title starts exclude that discrepancy; generic
arbitrary-tree source equivalence is not claimed.

MachinePartition includes all owned references and requires per-instance
permutation to cells with next-physical-start stops, existing instances, and
per-instance owner uniqueness. Cross-instance duplication of an attached block's
owner remains permitted. `ref_extracts` and `partition_bounds` derive actual
checked slice success and global bound checks from this structural partition
and physical uniqueness, rather than taking extracted output values as premises.
This is a conditional invariant interpretation: preservation under Machine steps
and a whole-replay theorem have not been established.

The added containing-reference witness derives an actual forest slice containing
a physical marker from that partition, instance presence, and its not already
being a stored start boundary. It does not assume the containing slice or a
successful source search. These remain conditional input-state premises until
insertion preservation supplies them. An independent draft check caught a local
membership variable shadowing failure in the final tree-witness projection;
the owner repaired it, and the expanded MachinePartition independently
checks cleanly with standard printed axioms.

## Checked routing and conditional partition composition

MachineRouting and the final MachinePartition composition independently check
cleanly with standard printed axioms. Routing derives strict physical index
bounds from actual endpoint-scan membership and unique tokens. Its duplicate
marker control demonstrates that the uniqueness premise is necessary. Virtual
START and END are handled through the augmented physical/token representation;
strict containment excludes both stored endpoints, matching source slice bounds.

`splitForest_checked_progress` derives successful recursive search and valid
resulting bounds from an actual containing-ref witness, input bounds, and
physical uniqueness. Accepted search/output bounds are not premises. Its
internal accepted-step preservation lemmas are consumed only after the separate
search-progress proof constructs that step. The transient control preserves
the right interval and its tombstoned physical parent, and endpoint negatives
exclude selecting the marker at an existing start or stop.

`splitForest_partition_progress` removes the free search witness and input
bounds: the structural all-owned partition supplies both. Instance presence,
physical marker membership, physical uniqueness, and the marker not already
being a stored start remain explicit. This proves checked routing success at
that state, not preservation of Partitioned after inserting or detaching the
marker, and not complete transaction/whole-replay progress. In particular the
transient split has two same-instance references under one owner before move;
the per-instance owner invariant is an atomic-boundary property. The next-stop
control rejects treating the preceding empty interval as unbounded.

The root-detachment caveat now appears in ForestRefs' header as well as this
review: arbitrary structural detachment skips roots, while raw source would
throw on a first root match. Core freshness and normal title starts exclude
that case. None of the reviewed routing theorems relies on a claim of arbitrary
raw detachment equivalence.


## Fresh-create partition review

The proof-track reviewer independently read and kernel checked the final
MachinePartition and MachinePartitionCreate modules. Fresh create derives the
actual dispatched state and proves preservation of old cells plus the fresh
START-only cell and title reference. `create_partitioned` supplies actual
executable success rather than requiring next-step acceptance. Instance and
block freshness remain explicit; this module does not derive them from the
issuer. The empty-title positive control and structural read-side omission
falsifier distinguish invisible content from an absent interval.

The primary reviewer checked the recursive routing/endpoint proofs, exact
forest context rewrites, fresh-create case split and oracle mutation control.
No desired final partition or successful split result is used as a premise
in the new progress endpoints. The full partition is still an explicit
structural input, and its owner uniqueness is a transaction-boundary property.
No complete replay or Notion RA claim follows from this increment.

The final routing-increment research gate passed 48 modules (3,459 Lean jobs)
and all fourteen oracle result groups. Saved all-reference observations match
the fresh gate output exactly. The production gate passed 3,694 Lean jobs,
18 exact public contracts with axiom audit, 187 runtime tests and validation of
569 benchmark records. Its production ledger does not register these unfinished
Notion research modules as a verified document datatype.

## Actual insert/erase partition preservation and split phases

The final MachineSplice, MachineErase, MachineCanonicalForest,
MachineCreatorPresence, and expanded MachinePartitionUpdates independently
check cleanly with standard printed axioms. Generic splice derives checked row
integration and actual physical insertion from an input edge-coupled ordered
forest, fresh IDs, origin presence, and sibling readiness. CanonicalForest
removes those caller guards by deriving the actual forest and allocation facts
from issuance and the accepted canonical prior prefix. No next insertion
acceptance, next forest, desired physical splice, or output partition is assumed.
Literal pending text births and singleton split markers use the same proved
physical position; source text and marker kinds retain their distinct flags.

MachineErase derives finite traversal tombstone commutation without graph
closure or uniqueness premises, since IDs and parent links remain unchanged.
Its actual operation frames supply physical erasure and unchanged other
instances. CreatorPresence derives metadata-provider execution in the actual
prior prefix, including empty created instances. The public canonical insert
and erase preservation theorems use that result to discharge instance existence;
they require no free existing-instance witness. From the old all-owned partition
and accepted prior prefix, next complete insert/erase acceptance and partition
preservation are conclusions. Full replay still needs create/split composition,
initial/bootstrap handling, and preservation of the additional normal-form
properties; these are not inferred from the partition result alone.

Generic structural splice does not by itself prove fresh physical uniqueness
or prevent populating an inactive title. Those properties depend on separate
canonical allocation/client/normal-form facts. Physical update equations were
explicit interfaces in the generic partition lemmas and are now derived for
these actual insert/erase compositions. The latest insertion-result draft typing
failure is resolved in the independently checked final module.

The two pinned `split-phase-controls.mjs` records observe unchanged source
primitives and command boundaries. Hand-derived ab split at 1 preserves coverage
before creation, after creation, and after marker integration. Tree splitting
keeps coverage but temporarily duplicates the old owner; detach-before-append
briefly leaves an unowned gap; final append restores coverage and per-instance
owner uniqueness, including the empty fresh title. Skipping the move is rejected
as final ownership. A second honest split of an all-deleted inherited interval
shows the same boundary pattern and yields a|empty|empty. These are focused
phase examples, not a universal frame-preservation proof or a new bug. In
particular they do not justify asserting atomic Partitioned after each internal
tree/detach phase. Existing source root-detachment and decoder boundaries remain.

The proof-track reviewer also independently checked the final composed
insert/erase endpoints and found no dependency cycle or next-acceptance
premise. One additional boundary is explicit: creator-aware admission permits
START insertion into an attached block's inactive own-title instance. That
may preserve `Partitioned` while breaking the stronger empty-title/active-leaf
shape. Actual client selection must establish the stronger invariant. The
partition theorems do not claim it, and this is not a new demo bug.

Final validation passed: 53 research modules (3,464 Lean jobs), all fifteen
oracle groups including two split-phase records, and exact agreement between
those saved records and fresh pinned execution. The production gate passed
3,694 Lean jobs, 18 exact public contracts with axiom audit, 187 runtime tests
and validation of 569 benchmark records. No Notion document certificate was
added to the production ledger.

## Inactive-title boundary and canonical marker phase

The pinned inactive-title control and kernel countermodel agree on the semantic
boundary: bootstrap ab, split at 1, then a fabricated raw insertion into the
fresh block's own START instance. Creator admission accepts that raw choice;
NormalForest survives but EmptyInactive fails. Honest zero-gap preparation
selects the inherited marker in the original instance. Both alternatives can
display Xb and retain two nodes, so visible text and node count do not prove
inactive-title emptiness. The source probe uses a separate raw session R and
honest session H, while the typed witness uses S for the raw next key; those
literal traces are not asserted identical. Their instance/selection distinction
is the same. The kernel module checks the actual negative EmptyInactive
predicate and actual positive NormalForest, not an informal node-count proxy.
This is a raw admission-domain countermodel, not a newly found valid-client bug.

CanonicalCreate was independently checked: actual prior instance and block
absence for the next issued destination follow storage provenance, earlier
creator providers, injective names, and strict transaction ordering. Actual
fresh creation supplies empty target physical storage and exact old-instance
frames without caller absence or next-step acceptance guards. Its arbitrary
predecessor argument is a raw create-phase interface, including source's missing
predecessor fallback, rather than a public request-validity theorem.

The composed MachineMarkerProgress independently checks cleanly with standard
axioms. `canonical_split_marker_phase` derives source-instance existence and
its distinction from the fresh target, actual create success, raw marker
integration, and unchanged target/old storage frames from the accepted prior
canonical prefix. Old Partitioned is explicit; freshness, physical uniqueness,
marker presence, and recursive checked marker success are derived. No successful
next marker operation or desired physical output is assumed. MarkerStage names
the state after integration but **before** tree splitting. The subsequent
checked marker operation succeeds, but its post-tree state is not claimed
Partitioned; detach/move owner restoration and stronger active-title normal
shape remain separate. The inactive-title countermodel explains why creator
admission alone cannot supply that stronger active-selection property.

The research gate now includes CanonicalCreate, MarkerProgress,
InactiveTitleBoundary, PartitionSplit, and the planned MachineShape module,
plus the inactive-title source trace. Shell syntax checks pass. The gate lists
58 Lean modules and 16 result series; the full gate was not run during this
review and awaits the owner's readiness signal.

## Bootstrap initial case and current gate inventory

MachineBootstrap closes the actual initial partition case for every atom list.
`bootstrap_executes` derives the concrete create-plus-insert result from literal
decoded row uniqueness/rank and the actual checked integration loop; neither
acceptance nor a desired next-state equation is an input. `seeded_partitioned`
constructs the sole physical START-to-END cell from actual traversal, and
`bootstrap_partitioned` packages success and the all-owned partition. Empty
bootstrap still creates the displayed title and physical START; the kernel
PASS+FAIL control rejects omitting that instance. This proves the partition
initial case, without duplicating the separate stronger shape development.
The frozen module's narrow build completed 707 jobs cleanly, with standard
printed axioms. The parent independently reviewed the proof's literal-run and
single-cell construction.

The latest atomic-to-transaction bridge in MarkerProgress was independently
checked cleanly. It derives interpreter bound/target checks and complete
transaction dispatch from accepted structural atomicSplit plus the previously
derived creation/integration stage. That atomic acceptance is an explicit bridge
premise, not silently relabelled unconditional split progress.

The inactive-title source trace was independently rerun through run.py with all
seven fetched module hashes verified. Its single output record is **byte-for-byte
identical** to saved inactive-title-observations.jsonl (`cmp` exits zero).
The gate now lists 60 Lean modules, including seven modules added in this
increment, and 16 result series. ClientShape was added to the gate; its separate
source-agent review is not certified by this paragraph. Shell syntax and
whitespace checks pass. The full gate has not been run during these reviews.

An independent source-audit read of `MachineClientShape` found no proof or
scope defect. The attached-root case derives empty extraction from the actual
stored title and its empty physical instance, then reduces zero fallback and
positive predecessor selection to the inherited leaf. This includes an
all-deleted leaf. Atom-instance membership comes from checked slice extraction;
internal decoding uses accepted replay's actual typed instance provenance.
`prepared_insert_active` and `prepared_split_active` therefore derive local
active-instance selection without an assumed selection guard. Normal forest
shape and empty inactive titles remain explicit issuer-state premises. These
are local successful-preparation theorems; they do not establish request
progress, derive those issuer invariants throughout honest client history, or
transport the selected instance into a different canonical replay prefix.

## Independent whole-split composition review

The proof agent independently read and directly kernel-checked the latest
MachineShape and MachineCanonicalSplit modules. Both checks exit zero; printed
axioms are `propext`, `Classical.choice`, and `Quot.sound`. No hidden next-replay
acceptance or desired output partition premise was found. The canonical split
composition derives fresh creation, raw singleton integration, actual recursive
atomic split/detach/move, complete transaction success, and the final partition
and shape. The accepted structural atomic phase used by the generic shape lemma
is supplied by the derived routing theorem in this composition.

`ShapeInvariant` concerns normal root/leaf structure, profile ownership, and
empty inactive titles. Its active-instance update lemma deliberately permits
arbitrary contents of the selected active instance; it is not a physical
interval-validity theorem. Physical coverage and endpoint ownership come from
the separately composed `Partitioned` invariant. The final canonical theorem
still assumes shape, partition, and active-instance membership in the old
canonical state. Local honest client selection proves active membership in its
issuer state under those issuer invariants; transporting that fact to this
canonical prefix and deriving the invariants throughout honest history remain
open. The present theorem is complete conditional transaction progress and
preservation, not unconditional honest-replay progress or source refinement.

## Independent atomic partition and canonical full split review

PartitionSplit and CanonicalSplit independently check cleanly with standard
printed axioms. PartitionSplit derives actual recursive search, leaf detachment,
and destination append from the raw post-marker partition, old normal trees,
fresh starts/names, and empty target. The selected owner and preorder context
are recovered from search; no chosen next forest or output partition is an
input. Literal split-marker presence plus unique physical IDs identifies the
scanned atom as that boundary before cutting its cell. Reference permutations
then restore per-instance owner uniqueness while retaining empty title cells.
Generic reference-replacement equations are interfaces internally; the public
atomic theorem derives them from the actual tree operation. Hand-derived
controls reject both a no-op split and a transient duplicate old owner.

CanonicalSplit discharges creation, marker freshness, old/target instance
distinction, integration, and recursive routing from the accepted prior
canonical prefix. Complete actual transaction success, Partitioned, and strong
ShapeInvariant are conclusions, not premises. It uses the structural atomic
result to discharge the previously conditional checked transaction bridge.
No next acceptance, selected owner, or fresh-name guard is supplied by callers.
Old Partitioned, old ShapeInvariant, and ActiveInstance in that **canonical
prefix** remain explicit. The inactive-title countermodel demonstrates why
creator admission alone cannot eliminate the latter. ClientShape proves active
selection in the issuer's local state; transport to a different canonical prefix
is still an open history-provenance obligation. This is not yet unconditional
whole-version replay progress or an RA-linearizability certificate.

The gate's CanonicalSplit entry brings its inventory to 61 modules, eight added
in this increment. Syntax checks pass; the parent owns the full gate execution.


## Integrated atomic split checkpoint validation

The parent reviewed the structural cut/permutation proof, actual bootstrap
integration, shape adapters, inactive-title source fixture and canonical
composition, including their explicit old-state premises. Independent source,
oracle and proof reviews above agree on the remaining active-instance
transport boundary.

Both integrated gates passed: 61 research modules (3,472 Lean jobs), all sixteen
oracle result groups, the unchanged production ledger build (3,694 jobs),
18 exact public contracts with their axiom audit, 187 runtime tests, and 569
validated benchmark records. All research output records matched the saved
JSON evidence; replay-prefix records are distributed across the existing table,
partition and structural-instrumentation evidence files. No new Notion module
is registered as a verified document datatype.

## Active-root classification and nonfirst bootstrap review

The generic fresh-bootstrap extension, fresh-root shape frame, strengthened
CanonicalSplit active-set theorem, and prepared_root_knowledge helper all
independently check cleanly with standard axioms. Fresh bootstrap accepts an
arbitrary old partitioned state when initial block/instance names are absent;
it does not require an empty prefix. Fresh-root shape allows arbitrary own
physical contents while framing other instances. Complete splitting preserves
the exact old active-instance set, excluding the fresh destination's own title.
The preparation helper derives received root knowledge from actual local
selection and root classification; its root-classification premise is an old
state invariant, not desired acceptance of a new request.

The new active-instance oracle independently derives expected roots from literal
bootstrap/standalone-create operations and compares them to actual structural
leaves. Across 40 causal ideals and 238 atomic prefixes it checks 198 active
memberships and excludes 95 split-title occurrences. Six additional directed
snapshots cover standalone empty creation, all visible text deleted, and repeated
empty/inherited splits. The hand-derived active set remains block-A and S-block-4.
A separately fabricated own-title insertion breaks physical emptiness without
adding an active tree instance, so root classification alone is not EmptyInactive.
The honest empty-receipt @ replica creates at @1 before receiving A1 bootstrap;
canonical order is @1 then A1, Map order is independent-created block then
initial block, and display order places ab before the empty independent block.
This rejects bootstrap-first assumptions without asserting a demo bug. Four
literal records are retained; the shared instrumentation was not edited.

The frozen RootReplay was independently read and kernel checked cleanly. Its
canonical-prefix theorem derives actual success, Partitioned, ShapeInvariant,
and exact ActiveInstance iff prior root-creator metadata from CreatorReach and
archive RootProvenance. No prefix acceptance, partition, shape, or active guard
is supplied. Reverse induction constructs the prior state and uses exact root
providers to discharge selected-instance guards for the next insert/split.
Erase retains shape without an active-target guard. Bootstrap uses derived initial
name freshness and the generic arbitrary-old-state frame, so the independent
create-before-bootstrap control is admitted. RootProvenance is a structural
archive condition, not a rendered-state equation; deriving it from actual honest
requests is the separate final HonestReplay composition reviewed by the source
agent. This paragraph does not independently certify that later composition.

The gate now includes actual RootCreators, MachineRootReplay, MachineHonestReplay,
and BootstrapProvenance module paths and the active-instance trace: 65 modules
and 17 result series. Syntax checks pass. No full gate was run by this reviewer
while the main induction was being completed.

Independent source-audit review of the frozen `MachineHonestReplay` and its
`MachineRootReplay` composition found no circular proof or hidden output
premise. The network induction uses the preceding archive's root provenance
to derive actual reconstruction, partition, normal shape, empty inactive
titles, and exact active-root classification. Actual local materialization and
internal decoding then identify the new insert/split instance with a received
root creator. Emission records that provider in the new transaction's causal
past. This establishes the next archive property without assuming its desired
reconstruction. The canonical prefix induction separately derives each actual
next transaction's success; bootstrap may follow independent lower-key creates
and its initial-instance freshness is proved rather than assumed.

`honest_root_provenance`, `honest_prefix_reconstruct`, and `honest_reconstruct`
therefore remove the former free root-provenance, prior-acceptance, partition,
and shape guards from their public conclusions. Their history domain is
`MachineNetwork.Reach`: a request transition requires an actual successful
`issue` result. These theorems establish reconstruction progress for networks
built from successful positional requests, whole-version exchanges, and clock
gaps; they do not establish that every valid nonempty positional request can
prepare and issue successfully. Deletion preparation totality remains separate.
They also do not establish the independent document specification, five document
VCs, RA/history correctness, search-label runtime validation, or equivalence of
the typed interpreter with a decoded JavaScript execution. Those distinctions
are essential to the positive reconstruction result's scope.

## Integrated honest replay checkpoint validation

The parent reviewed the root-provider definitions, arbitrary-position bootstrap,
active-set preservation and both induction compositions. Independent reviews
above confirm the noncircular dependency and successful-request scope.
Both full gates exited successfully: 65 research modules (3,476 Lean jobs),
17 oracle result groups, the production ledger build (3,694 jobs), 18 exact
public contracts and axiom audit, 187 runtime tests, and 569 benchmark records.
All 17 research result series matched saved JSON evidence; the full replay
instrumentation matches the existing replay-slice-partition snapshot. No Notion
document certificate was added to the production ledger.

## Display alignment and bounded deletion totality review

MachineDisplay and DisplayOrder's insert_after_flatMap independently check
cleanly with standard axioms. Actual operations preserve unique forest names
and display permutation; existing creation returns without reordering, fresh
creation uses literal splice, and marker/move phases preserve names. Alignment
certifies ID enumeration, not render success or physical interval ordering.
The known-predecessor helper derives equality to the independent flatMap
insertion under unique old IDs and actual predecessor membership. It does not
cover raw missing-predecessor fallback, which remains a separate source domain.

The frozen DeleteTotal independently checks cleanly with standard axioms.
Actual checked slice materialization is derived from partition and physical
uniqueness; empty inactive titles contribute no visible characters. Replay
provenance makes each visible atom decode as an item rather than START, and
normal shape gives the same selected instance for every target, so the entire
validator succeeds. The honest public theorem derives reconstruction and these
structural guards, without a successful reconstruction or selected payload
premise. It covers existing blocks and nonempty in-range natural bounds
start < stop ≤ visible length; oversized clamped ends and negative/fractional
JS inputs are not included in that theorem. Its result uses codec-sorted IDs,
not physical selection order. The inherited-leaf PASS+FAIL control rejects the
unused title instance and separately checks an empty range emits none.
No broad oracle or gate was run during this assurance review.

## Valid gap preparation and issuance completion

The parent-written ClientTotal gap and insert/split issuance theorems were
independently checked cleanly. Existing blocks and natural gaps at or below
visible atom length derive actual endpoint materialization, nonempty slice
preorder, address selection, and internal decoding; index zero includes empty
or all-deleted blocks. Nonempty insert atoms are explicitly required, preserving
the source's empty-insert early no-op. No successful selection or future output
is a premise.

The owned extension adds actual erase and create issuance. Erase retains the
existing-block and nonempty in-range bounds, proves codec-sorted targets remain
nonempty, and derives reservation, emission, and honest reachability. Create
allows None or a genuinely stored predecessor in the peer's reconstructed
state; it does not weaken the public API to raw missing-predecessor fallback.
Both compose actual preparation with the executable issue function. The expanded
module's narrow build passes 726 jobs warning-free with standard printed axioms.
No broad suites or gates were run.

## Integrated document projection checkpoint

The parent reviewed FreshText, DeleteTotal, Document and DocumentErase directly:
causal counters exclude prior pending flags for fresh text, actual selectors
derive internal decoding and same-instance validation, and erasure derives the
new materialized document without an output premise. The projection is into the
existing source-document model in actual display order. Independent review of
BlockPresence and DocumentCreate confirmed that canonical predecessor presence
comes from persistent blocks, not merely persistent instances, and exact create
order comes from the literal display splice. Its source transition is derived.

Both integration gates passed: 73 registered Notion modules (3,484 Lean jobs),
17 unchanged oracle groups, 3,694 production Lean jobs, 18 exact public contracts
with axiom audit, 187 runtime tests and 569 benchmark records. Every research
result series matched saved evidence. The parent uses focused builds for ongoing
insertion/split/client-effect proofs; those in-progress modules are outside this
checkpoint. No Notion document certificate enters the production ledger.
# Archive-version history and local split integration

Independent review of `MachineHistory.honest_history_version` confirmed that
every payload case derives actual execution and independent source execution.
The generic composition premise is discharged by those cases; the conclusion
uses exactly `transactionsFor` for its atomic command history and terminal
query. No next-step acceptance or rendering equality is assumed. This does not
yet establish Sal event enumeration, specification visibility or an RA witness.

The local split issuance theorem and generalized replay dependencies passed
independent review. The research integration gate passed 3,496 Lean jobs and
all seventeen oracle groups; the production gate passed 3,694 Lean jobs,
18 contract/axiom checks, 13 regression controls, 187 runtime tests and validation
of 569 benchmark records. The production ledger still excludes this unfinished
document certificate.
