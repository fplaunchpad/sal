# Notion demo MRDT investigation

The unchanged published demo cannot satisfy the full ordinary local editing
contract investigated here. Honest split/merge histories expose both a local
split failure and a local formatting failure. These failures precede the
sequential-history bridge: no choice of RA witness can make a locally issued
request have an effect that it does not have. This is a result about the pinned
educational demo, not Notion's production implementation or a limitation of
Sal's five-VC theorem.

The narrower split/insertion/deletion-only milestone remains open. An independent
identity-based sequential model passes bounded differential gates. Lean proves
its local preparation effects and invariant preservation, and refines guarded
physical interval executions into its grouped history language. The missing
connection is from actual source issuance and sorted replay to those executions,
followed by the Sal event/history bridge.

## Enquiry and evidence boundaries

The goal is a faithful MRDT adaptation of the demo with ordinary positional
client effects and a separately justified identity-addressed sequential
specification. The candidate is that stable character and boundary identities
suffice, without transaction replay or search labels in the specification.
An honestly issued request with the wrong visible effect falsifies local
preparation. A version with no single history preserving both required orders
and the query result falsifies the selected history bridge.

The reality oracle is the seven SHA-256-pinned official JavaScript modules.
The formal oracles are the `Notion*.lean` research modules. A kernel proof is
about their definitions; it is not a JavaScript verification theorem. See the
[source audit](notion-source-model.md), [proof boundary](notion-proof.md), and
[reproduction instructions](../experiments/notion-oracle/README.md).

## Small counterexamples

The [permanent bug catalogue](notion-bugs.md) assigns stable identifiers, records
reproduction commands and minimization limits, and links the retained literal
traces and checked counterparts. It also separates demo bugs from counterexamples
to modelling assumptions.

All setup requests are generated through `Replica`; no malformed or fabricated
operation payload is needed. The regression corpus records literal messages.

| Case | Hand-derived ordinary effect | Pinned demo effect |
| --- | --- | --- |
| Start `ab`; concurrently split at 0 and 1; merge to obtain `empty · ba`; bold both characters of `ba` | Both selected characters become bold | Neither becomes bold |
| Start `abc`; concurrently split at 1 and 2; merge to obtain `ac · b`; bold `ac` | Bold a and c only | Also bolds b in the other block |
| Reach `empty · aX` via seven setup requests involving concurrent merges/splits; split `aX` at 0 | `empty · empty · aX` | `empty · X · a` |

The first formatting trace is minimal in its character count for reversing
selection order; this is not a claim of globally minimal transaction count.
The split shrinker reissues client requests after each removal and checks
validity, rather than deleting dependencies from a transaction log. Its local
minimality is relative to that reduction procedure.

Formatting groups selected characters by text instance but chooses interval
endpoints in the instance's order. Block order can differ after movement. For
`ba` from instance `ab`, the interval before b to after a is empty. The Lean
counterpart checks this rule on the concrete no-tombstone/no-prior-mark fixture,
with ordinary exact-selection semantics and nonempty positive controls.

The split failure concerns movement of a slice subtree rather than the complete
displayed suffix. See the source review for the minimized structure. The full
ordinary contract cannot be established while preserving these observations.
A repair or a restriction excluding these honest histories would change the
target; neither has been silently substituted here.

## Independent semantics and retained identities

The ordinary local request specification stores ordered blocks of visible
characters with bold flags. Insert splices text at a valid gap; delete removes
the selected range; split places the suffix in a fresh successor block; merge
concatenates adjacent blocks; bold toggles exactly the selected characters.
These operations do not inspect replication messages.

For concurrent histories, original numeric positions are insufficient.
Splitting `abcd` at 2 concurrently with deleting the original b,c yields `a · d`.
Neither ordering of unchanged numerical requests produces that result. This
rejects a baseline specification, not the intended identity-message approach.

`identity-spec.mjs` defines the candidate split-only sequential machine. Its
state is an ordered block list whose slots retain character identity, content,
and visibility, plus zero-width starting and split-boundary identities.
Insertion places new slots immediately after the named slot. Deletion hides
selected identities across blocks. Splitting moves the suffix after the named
slot, beginning with a new boundary slot, into the new block. Block placement
uses the original request's block identity even if concurrent splitting has
changed which block owns the text anchor.

Retained character slots let later messages address deleted characters.
Boundary slots name positions at the beginning of split blocks, including empty
blocks. Block identities distinguish placement from ownership. These are
semantic address choices, not a claim that this representation is globally
minimal. The model contains no transaction logs, Lamport clocks, sorting,
search labels, RGA parent trees, or slice trees. Its current commands require
honest fresh identities and present anchors; those invariants remain to be
proved from issuance.

The harness decodes generated messages separately and tests an increasing-ID
candidate witness. Sorting chooses a witness outside the specification; it
does not define the machine's transitions. Across three fixed seeds, 150 trials,
six rounds per trial and two two-request branches per round, 4,500 local/merged
observations agree. The test includes retained block IDs in comparison. It is
bounded validation; two deliberate mutants (no-op delete and unmoved split
suffix) are detected by the same comparison harness. It is not proof of
refinement, legality, specification visibility,
or correspondence for arbitrary histories.

## Adaptation boundary

The executable adaptation stores immutable identified transactions and merges
payload-preserving branches by union. It checks that the supplied base is a
subset of each branch. Client preparation and document rendering use the pinned
demo, so this experiment preserves the source's observed failures as well as
its successes. It changes replication from message receipt to a ternary state
merge; the base contributes a consistency check rather than a subtraction.
No independent renderer equivalence is claimed from comparing two calls to
the same renderer.

A same-ID/different-payload conflict is rejected, not resolved by set order.
Fresh sessions, safe clocks, transaction atomicity, causal closure and source
allocation (including merge's 20-tick gap) belong to the issuance boundary.
Repeated delivery is distinct from two independently issued merges with the
same user intent. The latter occur in the minimized split trace.

## Verification status

| Obligation | Evidence and scope |
| --- | --- |
| Source boundary | All seven pinned modules audited; article and executable evidence separated |
| Distinguishing oracle | 575 directed cases, including IDs, clock gaps, boundaries, causal order, repeat delivery, split/merge and bold |
| Core local effects | 560 generated states, 18,053 local split/insert/delete checks, one fixed seed, no failure |
| Independent core semantics | Complete Lean slot machine and prefix-closed grouped history language; 4,500 original plus 5,348 adversarial comparisons |
| Independent local preparation | Universal insert/delete/split effects, structural invariant preservation and progress; hidden origins allowed |
| Allocation and issuance | Receipt-derived clock bounds and uniqueness; whole-version mint-past closure; item-producing providers in actual source-key-sorted prefixes; source payload decoding remains separate |
| Source-selected preparation | Actual zero/fallback and visible-predecessor rules on the core normal form; successful physical insert/delete/split effects |
| Materialized source model | Physical interval transitions project to semantic steps; guarded grouped histories preserve all query answers |
| Global structural components | Recursive origin search and raw parent-table extraction; endpoint partition/ownership; slice-tree root/leaf and inactive-title induction |
| Actual source invariant | 43,005 shape/title-owner and 62,849 interval checks, 238 instrumented sorted prefixes, 144 directed endpoint-adjacency checks; joint execution and source decoding proof still open |
| Positional request admission | Actual per-peer sorted reconstruction; create/insert/single-instance delete/split derive item and creator guards; total replay and core deletion progress remain open |
| Combined typed interpreter | Exact deletion-aware actual tables through accepted canonical replay; derived actual graph guards, next reference presence and row integration; joint slice/replay progress remains open |
| Local effects with merges/formatting | Refuted by fresh-client executable traces; restricted kernel formatting counterparts |
| Three-way adaptation | Executable transaction-set shell preserving source preparation and rendering |
| Five VCs | Reused finite-store proof, key-consistency lemmas and arbitrary-render convergence; storage only |
| Natural sequential-history bridge | Open for the core; full requested local-effect contract refuted |
| Ordinary and recursive bases | Generic storage convergence covers both via the existing five-VC chain; no Notion document-history correctness theorem for either |
| Production implementation | No source correspondence or verification claim |
| Arbitrary block movement | No public demo client request; only merge's internal slice movement audited |

The only development task list is `PRIORITIZED_REMAINING_WORK.md`. This record
states evidence and semantic choices; it is not a second queue. GC, the paper,
formal-reference PDF and public Site are outside this branch's changes.

## Core proof increment

The research question sharpened to a source provenance obligation: does every
honestly prepared origin, when replayed among concurrent transactions, still
select a unique active interval whose RGA insertion is an immediate retained-slot
splice? Sorting transaction-first IDs alone is insufficient. The preserved raw
`Z@10`/`A@11` countermodel demonstrates the missing whole-run knowledge premise;
honest receipt rules it out by advancing the next counter to 12.

The allocation network derives clock bounds, disjoint run ownership, freshness,
and complete-run provenance from publication and receipt. Source sessions use
UTF-16 units; comparing Lean strings would reverse some Unicode ties. Those
results are operational allocation facts, not assumptions about editing answers.
Their integration with actual source origin selection remains separate.

The full independent machine proves ordinary local request effects. Its
structural admission rules preserve unique block/address names and invisible
anchors from the empty document and guarantee that admitted commands execute.
The materialized physical source machine has a separately defined renderer and
projects accepted guarded transitions to the independent machine. Its grouped
history refinement preserves queries at every transaction boundary on the same
ordered label sequence. This supplies an intermediate refinement theorem;
it does not select an RA event permutation or derive the source normal form.

The [correspondence analysis](notion-core-correspondence.md) identifies the
remaining extraction obligations. The [independent review](notion-core-review.md)
checks definitions, theorem strength, mutation sensitivity and the separation
between allocation, semantic guards, physical source operations and JavaScript.
Ordinary and recursive-base natural editing correctness both remain open;
the existing five-VC storage result covers both only at the transaction-set level.

## Source traversal and preparation increment

The source-normal-form argument now has global search and extraction components.
`NotionCoreOriginTree` searches a finite physical tree for the actual origin and
derives the surrounding preorder splice context. `NotionCorePartition` starts
with an augmented raw traversal and endpoint-owner table, recovers cells through
endpoint scans, and derives coverage/unique ownership across repeated splits,
insertions and deletions. Its virtual START is not a stored JavaScript item,
and its endpoint order is not block display order.

`NotionCorePhysicalReplay` connects these two representations: source session
identities inject into opaque semantic names, actual tree insertion preserves
the raw traversal coupling, and raw scanning yields the updated interval cells.
For splits it derives the source's post-marker routing through the old endpoint
table before installing the new endpoint. Freshness and child dominance remain
structural inputs; this theorem does not yet derive them from source issuance.

`NotionCorePreparation` follows the source's zero/fallback and visible-predecessor
selection rules. It derives a prepared semantic gap, proves deletion identity
selection, and proves successful physical-model local insert/delete/split effects.
The attached-block zero address deliberately differs from the independent
helper's unused title root. This closes preparation on the defined normal form,
not extraction of that form from every source replay.

The new four-case pinned oracle exposes bootstrap grouping, deleted-boundary
fallback, raw receipt before dependencies and an atom/string distinction.
Source insertion accepts lone surrogates: two separately inserted surrogate
atoms can display as one emoji while remaining separately indexed. The formal
values remain opaque atoms; no Unicode-scalar/string roundtrip or silent input
restriction is assumed. Source receipt also does not check dependency closure.
A faithful MRDT issuance theorem must establish closure for its version states,
rather than cite a validation absent from the demo.

The outstanding full-source proof must connect the parent map to the finite
origin tree and endpoint table, preserve the per-block root/leaf shape and
block display order, and derive payload/identity/provenance guards from issuance.
Grouped bootstrap, no-event empty edits, ID-range compression and rendering
remain encoding boundaries. The Sal same-witness certificate still needs that
source correspondence; the current structural components do not supply it by
assuming the desired observation equation.

## Issuance and raw source structure increment

The candidate claim is that every dependency-closed version of honestly issued
core transactions replays with present origins, fresh item identities and
dominance over the chosen origin's old children. A missing provider or an old
internal child sorting above the new first item would refute it. The targeted
reality oracle instruments actual pinned RGA entry points over all 40 causal
ideals of a nine-event network: 238 transaction-prefix replays, 646 entry checks,
661 child comparisons and 398 internal-child whole-run checks pass. Deliberate
missing-dependency, child-dominance and shared-session controls are detected.
The saved literal ledger includes overlapping runs and Unicode session ties.
A new transaction below an unrelated stored item refutes a stronger global
maximum requirement; that requirement is not imposed on the implementation.

The formal increment derives whole-version mint-past closure and item-provider
availability in actual source-key-sorted prefixes. Review exposed that allocation
alone does not imply an item exists: create/delete also reserve IDs. The model
now distinguishes item-producing runs, and a positive/negative control pins the
difference. Source payload decoding still has to establish the tags and selected
references in the complete execution.

Raw parent-table extraction now derives a finite ordered forest and complete
coverage from operationally preserved rank, uniqueness and closure. Separate
slice-tree induction derives the core root/leaf shape and empty inactive titles
through actual search/split/detach/append operations. These results narrow the
remaining correspondence problem to their joint execution, payload/identity
decoding, endpoint ownership and displayed block order. They do not yet supply
the same-witness RA certificate. Exact theorem scopes are in the
[correspondence analysis](notion-core-correspondence.md).


## Typed payload and ordered traversal increment

The candidate claim is now checked at two previously separate boundaries:
exact raw parent edges plus unique IDs and ordered siblings determine the
actual traversal, and honestly emitted typed payloads supply their own item
births, reservation widths and same-instance replay providers. An unordered
forest with the same edges and a globally present item in the wrong instance
are distinguishing negative controls. The kernel-checked declarations and
residual premises are recorded in the correspondence analysis.

The typed archive derives freshness against all earlier issued items, including
unreceived transactions. Its canonical-prefix theorem names an actual provider
payload and the selected text instance, instead of assuming a free item tag.
The source-selected membership premise still needs derivation from the joint
interpreter. Source block-name/range encoding, block-creator provenance, search
label validation, display order and the final same-witness RA bridge remain
open. The full core milestone is not complete.

Three new pinned-source fixtures check the trusted payload boundaries. Honest
requests show that item existence is instance-specific and empty edits reserve
no clock or transaction. A clearly labeled fabricated primitive checks that a
pending delete tombstones a later text birth but not a split marker. These are
controls, not additional confirmed demo bugs; the preserved count remains three.


## Combined replay increment

The candidate claim is that the typed replay interpreter maintains a physical
partition whose stored stops name successive boundaries, so its actual reads
refine the independent materialized specification. Wrong stops are a falsifier:
a checked control exposes neighboring text when a boundary is dropped. Raw
incomplete receipt is another excluded countermodel; it can allocate an
instance with no covering slice.

The formal oracle now derives graph uniqueness, counter rank and parent
closure for every canonical prefix, reconstructs exact parent edges, and
derives checked row integration for the next payload. The combined interpreter
passes kernel-checked execution controls. Successful checked slice extraction
and attached-tree reads follow from the structural partition premises, rather
than an assumed read equation. The reality oracle validates 144 instance
adjacency checks on directed honest core histories. Canonical label controls
cover 8,191 binary paths of depth at most 12 plus twelve honest repeated splits;
alphabet-valid but noncanonical labels can alias and are not claimed injective.

These results remove component guard assumptions, not the remaining whole-state
induction. Actual replay tables must still be coupled to deletion-aware typed
prefix births; slice endpoint ownership, empty inactive titles and display
alignment must hold for that same execution. The later positional issuance
increment supplies reference and creator provenance. The same-witness RA bridge, source
codec and label proof remain open. The first milestone is still incomplete,
and the confirmed demo bug count remains three.


Review exposed a specific reason the typed allocation network does not yet
supply whole-interpreter progress: START has no item-reference requirement, so
it permits an unseeded insertion that creates a table without a block title.
A following item-referencing split lacks a source slice. This countermodel now has kernel-checked old-admission Reach witnesses and
failed interpreter replay; it is not a trace from an honest demo client. It sharpens the creator-provenance obligation;
no fourth demo bug is claimed.


## Source preparation and creator increment

The falsified claim was that item-provider reachability suffices for source
replay progress. A two-transaction kernel counterexample preserves the failure.
Creator-aware admission now derives metadata providers, and actual interpreter
provenance connects created forest blocks and touched text instances to received
creator transactions. Actual create/insert/split preparation discharges these
metadata guards from the reconstructed document. The following increment
derives selected item providers; whole replay success remains open.

The source comparison also rules out an excessive repair: an edit's replay
origin owner need not equal the block selected at issuance. Honest concurrent
splits of `abc` exhibit the difference and render `a|c|b`. Preparation must
validate the local selection, while replay must retain global interval routing.
A source guard counterexample and an underconstrained model counterexample are
both research evidence; neither increases the confirmed demo bug count of three.


## Actual item provenance and positional issuance

The candidate claim was that successful source-style client selection derives
same-instance birth knowledge without a supplied reference guard. MachineBirths
and MachineClient now prove it through actual storage and traversal. The
falsifiers remain wrong-instance items, fabricated births, and selecting an
empty destination title instead of its inherited marker. Kernel PASS+FAIL
controls distinguish these cases.

Canonical per-peer reconstruction now projects exactly to the earlier sorted
run replay. The positional request network uses it directly and derives both
item and creator admission conditions. Deletion selects one core active
instance and emits the exact sorted range-codec expansion. Five new pinned
source controls distinguish physical selection order from wire ID order and
check no-op clocks, markers and prior tombstones. They found no additional bug.

This closes the free-reference-guard gap in issuance; it does not close the
research question. The largest remaining obligation is a joint invariant for
actual replay tables, endpoint ownership, inactive titles and display order,
including unconditional reconstruction and supported-request progress. Source
wire/name/label correspondence and the full same-witness RA theorem remain
separate. The confirmed published-demo bug count is still three.


## Actual replay-table correspondence

The candidate invariant was exact storage equality: each instance contains its
chronological decoded birth rows with all prefix deletion targets applied.
The falsifiers are omitted tombstones, wrong parent or instance, and pending
deletes lost before birth. Independent literal decoding matched 293 actual
source instance tables and 1,534 rows across the existing 238-prefix campaign;
mutation controls distinguish no-op deletion and wrong-instance ownership.

The universal typed theorem is now checked. MachineTables follows actual
accepted storage transitions and atomic phases, while ArchiveOrder derives
canonical freshness and chronological/archive permutations from issuance.
MachineTableGraph uses them to derive actual graph invariants, physical ID
uniqueness, next reference presence and next-row integration success. It does
not assume next-step acceptance. Accepted prefix reconstruction remains an
explicit input, so full replay progress is still open.

The remaining structural proof must relate all actual forest slices to each
instance's endpoint partition, including empty inactive titles. Normal shape,
endpoint adjacency, unique ownership and display alignment must be preserved
in that same execution to establish split routing and bounds. Source wire and
label correspondence and the RA bridge remain separate. No new demo bug was
found; the three confirmed editing failures remain recorded.


## All-reference routing increment

The structural candidate now includes every stored slice reference, including
empty inactive title roots. Its exact per-instance physical factorization
derives checked extraction, a containing-reference witness, successful actual
recursive split search and valid output bounds. Separate recursive-update
lemmas derive the split and detach contexts, preserving earlier empty roots.
Fresh create also derives executable success and partition preservation from
explicit name freshness. Independent reviews and kernel checks found no hidden
desired-output premise.

The oracle checked 293 instance partitions and 1,827 augmented physical atom
ownership occurrences across the existing 238-prefix campaign. A hand-derived
split fixture distinguishes retaining the fresh empty title from omitting it.
These are bounded observations, not invariant preservation.

The proof must be atomic: immediately after splitting a tree node, both new
references still have the old owner. Per-instance owner uniqueness is restored
only after movement to the fresh destination. Thus the full partition relation
belongs at transaction boundaries; intermediate phases need weaker relations.
This is a proof-design constraint, not a fourth demo bug. Full replay progress,
wire/label correspondence and the same-witness RA bridge remain unfinished.
