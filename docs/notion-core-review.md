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
