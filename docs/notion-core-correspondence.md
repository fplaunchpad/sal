# Core correspondence: current result and historical proof route

## Current authoritative scope

The typed create/insert/delete/split core now has an execution-derived Sal RA
result. `NotionCoreProtocol.versions_witness` constructs the same event witness
for carrier replay, required order, specification visibility, and the independent
history's query answer for **every registered version**. `specification_ra`
specializes this result to current heads. Their source-specific inputs are an
injective replica-to-session assignment and actual `Protocol.Reach`; neither
archive coupling, carrier equality, replay success, nor a desired document
answer is a caller-supplied premise.

This result covers ordinary Sal version merges and canonical recursive virtual
merge bases. Those merges union immutable transactions; they are different from
the demo's merge-block editing request, which is outside the verified fragment.
The concrete carrier and actual checked document renderer are
`NotionCoreMRDT.D`. Its query returns an `Option` answer, so an execution error is
not silently replaced by an empty document. The independent history delegates
to the existing retained-slot `CoreSpec`, with one atomic update group per
transaction. It contains neither an archive nor a source-clock replay rule.

The protocol has an explicit factory action from the initial source archive,
followed by ordinary locally prepared requests. Empty forks can precede that
action. Factory authorization is not inferred from a replica's locally empty
finite store. Ordinary issuance preserves one allocator per assigned session,
whole-run receipts, and captured mint past. Source compound IDs remain payload
metadata; Sal's globally fresh outer timestamps have a separate domain.

The pinned-source audit and executable evidence support the source model, but
there is still no machine-checked JavaScript-to-Lean extraction theorem or claim
about Notion's production service. The exact public-demo source hashes are in
[the source manifest](../experiments/notion-oracle/sources.json); function-level
source evidence is in [notion-source-model.md](notion-source-model.md).

## What is connected now

| Boundary | Checked artifact and result |
| --- | --- |
| Honest archive to replay | `MachineHonestReplay.honest_prefix_reconstruct_version` derives success, physical partitions, normal root/leaf shape, empty inactive titles, and exact active instances for every closed archive version and prefix. |
| Physical machine to independent document | `MachineDocument*` derives display-ordered materialization and actual create/insert/erase/atomic-split transitions; `MachineHistory.honest_history_version` transports the same sorted transaction sequence to independent history admission. |
| Source version to actual MRDT query | `MRDTArchive` relates the finite carrier to actual canonical replay and rendering. `MRDTClient.issued_update` relates actual issuance to `D.update` and its query. |
| Positional client effects | `MRDTClient.insert_effect`, `split_effect`, and `erase_effect` derive the ordinary visible effect on the issuer's next concrete MRDT query. Bounds use visible string-iterator atoms; deletion uses a nonempty in-range interval. |
| Five VCs to registered carrier | `NotionCoreMRDT.fiveVCs` and `represented_versions` reuse the finite-store VC induction with the real document query. Storage correctness alone is not presented as document correctness. |
| Archive to the same Sal event witness | `ArchiveEvents` derives event/source-key uniqueness, source-order visibility, exact enumeration, and closed-version eligibility. `ArchiveCertificate` derives registered carrier equality through the VC representation. |
| Actual Sal/source execution coupling | `MachineExecution`, `MachineGenesis`, and `IssuanceGuard` preserve the common archive, mint past, current heads, and allocator clocks through factory creation and guarded operations. `Protocol.Reach.paired` derives the coupling used by the final witness. |
| Search-label lifecycle | `MachineSearchLabels.honest_mapping_guard` derives canonical labels and multiplicity-sensitive key uniqueness through actual closed-version replay, including split routing and movement. |
| Literal wire names | `WireNames.honest_wire_mapping_guard` carries those labels to source-shaped block/item names and composite mapping keys; separator-bearing sessions do not create collisions on the stated domain. |
| Finite empty participants | `MachinePreallocation.finite_source_participants` constructs a real empty-fork prefix and initial source pairing for any finite participant set. Source sessions, archive, clocks, and receipts remain unchanged. |

The representation retains tombstones, split markers, inactive title anchors,
parent links, and interval endpoints. Thus it justifies future addressed commands,
not only equality of rendered text. Actual forest-map search order, per-instance
RGA order, and displayed block order are distinct and are related by proofs.
Sibling dominance follows from whole-run origin knowledge; transaction-first ID
sorting alone is insufficient. At an inherited leaf's zero gap, actual preparation
may select its moved marker rather than the convenience specification preparer's
unused title anchor. The local effects use the structural `PreparedGap` relation,
not false equality of the two prepared messages.

Finite preallocation closes participant availability at initialization. It does
not yet prove that every arbitrary timed source trace can be rearranged into a
Sal protocol trace, nor that a post-factory Sal fork is the same action as creating
a new empty source replica. The former copies its source's current snapshot.

## External correspondence limits

The final RA theorem is for the defined typed core and explicit protocol. The
remaining external extraction obligations include JavaScript object/Map and
transaction decoding, the source tree/label fields, conversion between strings
and iterator atoms, and error/exception behavior outside valid client inputs.
The parent-table, slice, range, and label models have direct audited source rules
and directed controls, but these are not a compiler or execution-equivalence
proof for the pinned modules.

`WireNames` proves mathematical decimal and separator codec properties. Its
agreement with JavaScript `Number.toString` is limited to positive safe-integer
counters; conversion to JavaScript strings remains external. Source session
comparison uses UTF-16 code-unit order. The model's opaque text atoms do not
establish grapheme-index or unrestricted JavaScript input behavior. Local request
progress covers existing blocks and valid natural-number positions/ranges;
early empty requests emit no transaction. Arbitrary isolated transaction receipt
with missing dependencies is outside the whole-version MRDT protocol.

No document theorem for the demo's merge-block, unrestricted movement, removal,
or formatting extensions follows from the core result. Three honest-client
editing failures remain reproducible: reversed-range formatting can affect
neither selected character; formatting `ac` can also affect `b` in another block;
and a merge-derived `aX` split at zero yields `X | a` instead of `empty | aX`.
See [the exact counterexamples](notion-research.md#small-counterexamples).
These are three demo bugs, not counterexamples to the restricted typed core.

## Current validation

The final research gate passed 3,515 Lean jobs and all seventeen pinned result
groups, including 575 systematic cases with zero failures. The production gate
passed 3,694 Lean jobs, eighteen exact contracts and their axiom audit, thirteen
contract controls, 187 JavaScript tests, and 569 benchmark records. These checks
support the scoped artifacts above; they do not replace external JavaScript
extraction. Notion remains outside the production theorem ledger.

## Historical progress entries

Everything below records the chronological proof investigation. Statements such
as “not yet proved,” “open,” or “local component only” describe the checkpoint at
which that entry was written and are superseded where the current overview above
names a completed theorem. Historical build counts are checkpoint evidence, not
a claim about the latest validation run. The current task list remains solely
`PRIORITIZED_REMAINING_WORK.md`.

This enquiry concerns honestly issued create/split/insert/delete transactions, with merge, slice movement outside split, removal of blocks, and formatting excluded. Source references use the exact seven hashes in `sources.json` and the function map in `notion-source-model.md`. The proposed invariants below are source-derived proof obligations; they are not yet a mechanized refinement theorem.

## A sufficient shape invariant

At transaction boundaries each block has one of these shapes:

1. Its title root is the only slice node.
2. Its title root has exactly one child, that child is a leaf, and the root's own text instance contains no RGA items. The child's instance may contain visible characters, tombstones, and split markers.

Every node interval remains one contiguous interval of its instance's RGA preorder. Intervals partition the text items of the instance, while boundary markers serve as stable addresses. Each instance's `start` address belongs to its original title root. Each split marker serves as the beginning address of exactly one moved right-hand interval. Blocks remain alive throughout the core fragment. Search-label hints do not choose the core dispatch target, but mapping rebuilds reject duplicate labels. A complete source correspondence must cover that runtime check as well as interval routing.

This is stronger and more precise than “at most one populated slice”: two nodes and one child are allowed, but the parent in that shape has a permanently empty *instance*, not merely no visible characters. A root with tombstones is not interchangeable with an empty new root. All bounds here are at complete transaction boundaries. A split temporarily creates one additional node before moving it.

The source offers an induction route:

- `createBlock` with a fresh block identity creates a single empty title root. A split's fresh destination root starts in this state.
- Insert and delete do not change tree shape. In a two-node block, `locateInsertion` selects the child: if text is visible it selects its first/previous visible character; if none is visible it walks to the last node and selects that child's starting marker. Thus ordinary preparation never populates the empty parent instance. A later replay proof must establish that the prepared child instance remains an existing interval owner, rather than assuming it stays in the same block.
- For a split of a one-node block, `splitTextSliceTreeNode` creates a right child; `moveTextSliceIntoBlock` detaches that child and puts it under the fresh empty destination root. The old root again has no child.
- For a split of a two-node block, honest preparation addresses the child interval. Splitting that leaf transiently makes a grandchild, and moving it leaves the old child a leaf; the destination again has an empty root and one child.
- The source's `#splitText` selects the interval containing the new marker globally, rather than trusting the stale pointer or label. The above induction therefore also requires marker membership and address-preservation lemmas. Merely inspecting the issuer's tree is insufficient when another transaction replays first.

No existing child subtree is transferred by a core split at a stable transaction boundary: the node actually split is a leaf. The problematic merge-derived sibling structures are consequently outside this invariant. This explains why the post-merge split counterexample does not immediately refute the core model.

## Why long runs do not justify arbitrary replay

`RgaText.traversal` sorts siblings by descending operation ID and visits them in preorder. To implement a new run as an immediate-after-origin slot splice, its first ID must dominate every existing child of the origin. Sorting transactions by their first IDs does not alone imply this: older runs can contain internal IDs larger than a later transaction's first ID.

A concrete countermodel uses a fresh block, a `Z@10` run `ab` after `start` (character IDs `Z@10`, `Z@11`), then transaction `A@11` inserting `X` after `Z@10`. Sorted replay places `A@11` after transaction `Z@10`, but RGA siblings of `Z@10` order `Z@11` before `A@11`. The source renders `abX`; immediate slot insertion renders `aXb`. I executed this literal fixture against the pinned modules. It deliberately uses a fabricated message and is **not** an honestly issuable counterexample: receiving the `ab` transaction advances the issuer's clock through 11, so its next insertion cannot have counter 11.

The required provenance argument partitions existing children of an insertion origin:

- A split marker or first run character has its owning transaction's first ID. Earlier sorted replay puts that ID below the new transaction's first ID.
- An internal run character has an origin equal to the previous character of the same atomic run. For the current issuer to select that origin, it must know the owning run transaction, either by prior receipt or its own prior issuance. `Replica.receive` observes `transactionClockMax`; own insertion reserves the entire run. The new transaction's first counter therefore exceeds the owning transaction's complete allocated maximum and hence exceeds this internal child's ID.

This establishes the intended sibling-dominance argument only after origin knowledge, complete-run allocation, transaction freshness, and the replay-prefix relation are proved. An older transaction with a large internal maximum elsewhere is harmless: only children of the selected origin affect this local splice. The same partition applies to a newly issued split marker, which is also a first-ID item. Unicode runs allocate one counter per string-iterator element.

Causal origin knowledge is stronger than raw message well-formedness. The source accepts identity-addressed payloads without checking that an issuer observed the origin's transaction. A complete theorem must quantify over issuance-derived executions, not every payload set accepted by `receive`.

## Checked local tree lemma

`Sal/MRDTs/Instances/NotionCoreRGA.lean` defines a rose tree and preorder, without importing the demo or the independent slot machine. `runTree_preorder` proves that a fresh chain reads as its run. `first_child_run_splice` proves that placing that chain first among an origin's children splices its whole run immediately after the origin and before the entire previous child forest. `context_run_splice` preserves the equality under a supplied list context. A concrete positive/negative control rules out appending the run after the old subtree.

The file checks with `lake env lean Sal/MRDTs/Instances/NotionCoreRGA.lean`; the printed splice theorem uses only standard `propext` and `Quot.sound`. It does not derive sibling ordering, search for the origin, derive the surrounding context, or model timestamps. Those are separate obligations. Keeping the theorem generic avoids confusing the finite tree labels with actual source timestamps.

## Representation and history obligations

A candidate relation can compare the source forest's visible text plus retained interval start/character addresses with the ordered-slot machine. Empty destination roots contribute their own zero-width start addresses; moved interval starts contribute the split marker. A block with one populated interval has no tree branching to encode in the specification. Deletion hides slots while preserving address order. Insert and split must use the issuance-derived sibling-dominance lemma before applying local preorder splice. Block-list insertion must separately match the original request's `afterBlockId`, even when the anchored text now belongs to a different block.

The relation must retain enough hidden structure to justify later commands, not merely compare rendered strings. In particular, unique character and boundary addresses, empty-root ownership, interval endpoints, and source-origin provenance are necessary inductive facts. Search-label encoding is not needed by the slot semantics, but forgetting it requires proving that all emitted labels are observationally irrelevant to this source interpreter on the chosen fragment.

The source key orders Lamport counter and session lexicographically. Sal's outer execution timestamps have separate global uniqueness and causal-order requirements. Source keys must remain operation payload metadata; tied source counters cannot be identified with globally unique outer timestamps. A finite proof may rank session names while preserving their comparator, but must exhibit that preservation. An ascending-source-key history witness then needs its own causal/order/visibility proof. Source refinement does not supply the framework's independent-history bridge automatically.

The open route is therefore substantive but specific: derive provenance and shape from issuance, prove each replay step preserves the source/slot relation, prove local numerical preparation has its requested effect, then establish one history witness with the selected paper order and specification visibility. The generic transaction-set five-VC shell addresses storage; it does not discharge these document obligations.

## Materialized source interval model

`NotionCoreSource.lean` now separates physical source atoms from semantic slots. An atom has an address and either text/deletion state or split-marker kind. A source slice stores its start address and the physical atoms strictly inside its interval. An instance partition concatenates those cells in traversal order, independently of block order. Blocks distinguish root-only ownership from an empty title root plus one active leaf. Their projection adds the appropriate invisible semantic addresses.

The checked source operations compute insertion, deletion, and split on these materialized intervals. Splitting partitions the active atom list, introduces a new start marker, retains the old block's root shape, and creates a destination with its own empty root. `split_partition_traversal` proves the resulting global partition traversal is marker insertion at the selected coordinate. `split_normal`, `insert_normal`, and `erase_normal` preserve the stated block shape and same-instance atom condition. `split_slice_identity_projection` and `insert_slice_identity_projection` connect an independently located address coordinate to the retained-slot commands. `erase_slice_projection` proves source tombstoning projects to independent identity deletion, while `erase_preserves_traversal` retains physical address order. `split_visible` derives visible suffix movement from the computed source split. A split-zero positive/negative control excludes the measured merge anomaly inside this restricted normal form.

This is a checked local source-normal-form calculation, not yet the whole source transition system. Its `Normal` predicate does not establish global block/address uniqueness, partition ownership, RGA provenance, label invariants, or that a marker is fresh. Those facts must come from an issuance-derived document invariant. In particular, treating an endpoint-bounded RGA slice as a materialized cell still requires an extraction theorem: insert the new marker in the global RGA preorder, show the uniquely containing interval splits at that position, and show detached ownership corresponds to the destination root wrapper. These facts are not premises asserting observation equality, but they remain absent proofs. The source's complete map-based document state and its invariant assertions have not been mechanized here.

The separate `NotionRunAllocation.lean` establishes the allocation part of sibling dominance under a network with one allocator per session. It must still be coupled to actual selected source origins and replay prefixes. Its possible delivery steps do not establish document causal closure; a delivered transaction must carry or have already received its semantic dependencies before the source interpreter can safely render.

The endpoint arithmetic now has a checked local layer too. `Endpoint.extract` finds the suffix after a start address and stops before an end address. `extract_factor` derives the materialized interval from a traversal factorization plus exclusion of an earlier start or internal end. `split_extract` derives both new endpoint intervals after insertion of a fresh marker between a left and right factor. This is the list-order counterpart of `sliceItemBounds`; connecting it to numeric entry indices from `RgaText.traversal` remains a separate source extraction step. The residual gap is therefore global RGA/provenance/ownership induction, not an assumed equality between source and specification observations.

`split_block_identity_projection` additionally handles the source's whole block wrapper: for an attached interval it retains the old empty title root in the left projection and introduces the fresh destination root before the moved marker/suffix. Its premises are the located active address index and inequality with the unused empty-root address. The theorem therefore does not force source preparation to select the independent helper's first slot at visible position zero. This distinction matters because `locateInsertion` selects the moved active marker rather than the empty title instance in that case.

The combined narrow build `lake build Sal.MRDTs.Instances.NotionCoreSource Sal.MRDTs.Instances.NotionCoreRGA` succeeds. No admitted source-correspondence theorem has been introduced to cross the remaining extraction/issuance gap.

## Complete normal-form document transition projection

`NotionCoreSourceDocument.lean` supplies a complete document transition layer over the materialized physical blocks. It has its own create, insert, delete, and split command constructors. Source insertion uses active physical traversal addresses, source deletion changes physical tombstones, and source split looks up the active owner and a distinct empty destination before computing the physical interval transfer. Its interpreter does not call the independent specification's transition function.

`project_create`, `project_insert`, `project_delete`, and `project_split` prove transition projection. `step_sound` combines them: every accepted source transition projects to the independent `CoreSpec.step`, under unique block identities and a structural `OriginSafe` guard for addressed operations. `OriginSafe` excludes unused empty title-root addresses as prepared origins. Split acceptance checks that its destination is distinct and root-only/empty; those checks are source-model restrictions, so the theorem asserts soundness of accepted transitions rather than equivalence of malformed-request rejection. The proof does not assume source/spec observation equality.

`Execution` chains accepted transitions carrying those structural guards. `execution_sound` proves that every such source normal-form execution maps to the independent command execution. This is a genuine trace simulation for the defined materialized source machine. It is not yet the required RA history bridge: the theorem does not derive these executions from pinned JavaScript/RGA replay, local client issuance, transaction-set merge, or source-key sorting. Nor does it prove that the source guards follow from issuance. Fresh atom/marker identities, same-instance allocation, and complete partition ownership remain additional source-generation invariants.

A hand-derived source split fixture has a positive and negative control. The narrow `lake build Sal.MRDTs.Instances.NotionCoreSourceDocument` succeeds; printed dependencies of `step_sound` and `execution_sound` are standard `propext`, `Classical.choice`, and `Quot.sound` only.

## Allocation-to-comparator sibling bridge

`NotionCoreSourceInvariant.lean` closes the local ordering gap between allocation and preorder splice. `compareIds` follows the source's literal counter-first/session-second branches, using UTF-16 code-unit lists. `descending_comparator` proves that the chosen descending sort relation matches this comparison. `sort_fresh_first` establishes first-child placement after sorting an arbitrary old child enumeration. `allocation_sort_fresh_first` derives its dominance premise from `RunAllocation.child_dominance`: every existing child has a published owning run whose first key precedes the new transaction, and internal run children have a preceding character known to the issuer. These inputs describe allocation/replay provenance; none assumes the resulting sorted list or observation.

`sorted_forest_splice` then places the fresh run's complete traversal before the old children's complete subtree traversals. The sorting algorithm used in Lean is library merge sort. Agreement with the source concerns the total comparator/order contract, not identity with JavaScript's sorting implementation. A positive/negative control checks both counter priority and session tie-breaking. The narrow build succeeds without warnings or admissions; the main bridge lemmas use only standard `propext`, `Classical.choice`, and `Quot.sound`.

The remaining source correspondence obligation is still global: derive the child provenance, interval partition, unique ownership, and unused-root exclusion from actual pinned RGA/tree replay and honest client preparation. These local sorting results do not replace that extraction theorem or provide the RA sequential-history admission bridge.

Independent review identified that freshly inserted map keys can appear after old keys. `sort_permutation` and `sort_fresh_enumeration` now cover any enumeration permuting `fresh :: children`, including append-at-end insertion. This strengthens the first-child result beyond arbitrary ordering of only the old children. The amended module rebuilds cleanly.

## Global origin search in a finite source tree

`NotionCoreOriginTree.lean` now models physical finite origin trees, including text tombstones and split markers. START is the external forest root. Run insertion constructs a chain, searches recursively for the actual origin, and inserts the chain among that node's children using the source's counter/session comparator. `insertChild_sorted_keys` proves that, under the existing sibling order and child dominance, the modified child list equals complete descending source-key sorting.

`insertForest_splice` derives the surrounding preorder context by recursion through ancestors and earlier sibling subtrees. No prefix/suffix equality is supplied as a premise. `insert_item_indices` and `insert_run_indices` derive the global equation `take (idxOf origin + 1) ++ run ++ drop (idxOf origin + 1)` from origin presence and structural child dominance. The theorem searches the full physical preorder, so invisible origins remain usable. It works for first-occurrence search even without uniqueness; allocation-derived unique IDs make that occurrence the unique source origin. `insert_preserves_unique_ids` proves that a fresh internally unique run preserves global item-key uniqueness.

The checked controls cover a hidden nonroot origin with a child subtree, a leaf with a later root sibling, START insertion, a split-marker origin, and absent-origin failure, each with a distinguishing negative. The fixture respects descending root order and increasing child allocation IDs. The narrow module build succeeds without warnings or admissions; the global splice lemmas use only standard `propext`, `Classical.choice`, and `Quot.sound`.

This closes the global search/context obligation *inside the finite rose-tree representation*. It does not prove that JavaScript's map of parent links extracts to that representation, that all replay prefixes are causally closed, or that the structural dominance inputs follow from a coupled source execution. In particular, raw `RgaText.#integrate` accepts items whose origins are absent, and traversal omits such unreachable orphans until their dependencies arrive. The modeled tree operation returns `none` when origin search fails; this denotes a transition outside the known-origin fragment, not a claim that the JavaScript receiver rejects it. The parent-map extraction/domain theorem must establish origin reachability before applying the rose-tree splice result.

## Global raw endpoint partition

`NotionCorePartition.lean` separates a raw `State` containing an augmented physical traversal and an endpoint/owner table from materialized `Cell`s. The traversal explicitly prepends a virtual START boundary atom; JavaScript keeps START outside its RGA items. Table order is physical interval order, not displayed block order. No result about a complete document's block ordering follows from this module.

`extract` runs the existing `Endpoint.extract` scans on the raw address sequence with an explicit END sentinel, then resolves payloads by physical identity. `Represents` records structural traversal/table factorization, global physical address uniqueness, and distinct interval owners. It does not assume that extraction returns the proposed cells. `extraction_correct` derives that equality for arbitrary represented raw states. `physical_unique_owner` proves that every retained physical identity belongs to exactly one cell, including starts, split markers and tombstones.

The executable raw `split` finds the containing interval by scanning the endpoint-extracted cells, computes the physical origin index and endpoint-row index, inserts the marker, and updates the table. `split_refines` derives the containing cell from raw origin membership and proves representation of the corresponding materialized `splitSlice` result under fresh marker/owner names. It does not require a desired final projection equation or a supplied context around the physical origin. `insert_represents` proves the analogous fresh-run splice result; `erase_represents` handles tombstoning without changing addresses or endpoints.

`Reach` starts with one virtual START interval and chains actual raw split/insert results plus deterministic deletion. Its guards mention fresh names, instance agreement and newly inserted text kind; they contain no materialized output, representation predicate, or observation equality. `reachable_represents` derives global coverage, unique ownership and text-only interval interiors after arbitrarily many operations. `reachable_extraction` shows that the actual scan provides that invariant partition. The hand-derived PASS+FAIL controls check endpoint exclusion, retained tombstones, hidden-origin ownership, and deletion followed by two splits with an intervening hidden-origin insertion.

The narrow build `lake build Sal.MRDTs.Instances.NotionCorePartition` succeeds without warnings or admissions. These are global endpoint-table results inside the defined raw model. The typed integration below couples the origin-tree splice to this augmented traversal. The source's endpoint/owner map must still be shown to extract to the table, and honest source issuance/allocation must establish the raw guards. These results do not establish full JavaScript correspondence or the RA history bridge.

`marker_routing_after_insert` also aligns the source's integrate-then-route split order. After fresh marker integration and before changing the endpoint table, the actual scan locates the marker in exactly the old origin's interval, now materialized as `insertCell cell origin [boundary marker]`, with the same owner. The proof derives that interval from raw origin membership and uses insertion/endpoint extraction preservation; it assumes no routing result. This is a transient state with an interior split atom, so `InteriorText` is restored only after installing the new endpoint row. PASS+FAIL controls cover a hidden origin and a later existing interval, rejecting routing to the new owner or constantly to the first interval.

## Typed tree-to-endpoint replay integration

`NotionCorePhysicalReplay.lean` connects the actual origin-tree traversal to the raw endpoint-table machine. Source IDs retain their UTF-16 session list and counter. Semantic addresses use `LocalId.event (Encodable.encode session, counter)` in a fixed text instance. `localId_injective` and `address_injective` prove preservation of identity; `address_ne_start` prevents an event from aliasing virtual START. The encoding makes no order claim. Comparator order stays entirely in the source-side dominance/replay premises.

The physical map preserves text values, deletion flags, and split-marker kind, then augments preorder with the virtual START boundary required by endpoint extraction. `physical_origin_index` proves the exact one-position index shift. `tree_insert_physical` transports the derived global origin-tree splice to the raw machine's actual `spliceAfterBy`, for START and item origins.

`tree_insert_partition` and `tree_split_partition` integrate that equation with partition ownership and extraction preservation. They derive the affected cell from raw origin membership, compute the raw insertion/split and materialized interval update, preserve `Represents`, prove the resulting raw physical state equals the actual inserted tree's augmented traversal, and derive endpoint scanning of the updated cells. Fresh encoded-address uniqueness and disjointness follow from source item-ID freshness. The input coupling is an equality of two physical representations, initialized by `initial_coupled` and preserved by these steps; it is not an assumed rendering law.

`tree_marker_routes` also matches the source order inside `#splitText`: after actual marker insertion into the tree, locate that marker with the old endpoint table. Its containing cell and owner follow from scanning the actual new traversal. No owner-routing result is assumed as a guard.

The module has hand-derived positive/negative controls for semantic-name separation and START insertion. `lake build Sal.MRDTs.Instances.NotionCorePhysicalReplay` succeeds cleanly; its four printed integration theorems use standard `propext`, `Classical.choice`, and `Quot.sound` only.

Remaining premises are explicit: initial parent-map-to-tree extraction, honest issuance of source runs/markers, replay origin reachability, derivation of child dominance and freshness in that coupled execution, block-order/root-wrapper correspondence, transaction grouping, and admission of the same source-key history to the selected RA bridge. These theorems do not establish production correspondence or complete the core milestone by themselves.

## Whole-version issuance and source-ordered prefixes

`NotionCoreIssuance` extends the allocation network with ghost records of the
actual mint-time received runs. Exchange imports a whole peer version through
the existing receipt operation. `allocation_reachable` erases these steps into
the checked allocation model, preserving its single serialized allocator per
session. `peers_closed` derives that every exposed version includes the complete
mint past of each transaction it contains. Raw isolated receipt in JavaScript
does not enforce this property; the whole-version MRDT exchange supplies it.

Item-producing insert/split runs are distinguished from reservation-only
create/delete operations. `ItemKnown` requires a received provider record that
produces items, rather than accepting any allocated clock ID as an origin.
The item-production tag and selected references remain inputs whose decoding
from source payloads must be proved. `record_reference_births` preserves those
births in the saved mint past. `reference_counter_before` derives strict parent
counter rank; `replay_child_dominance` combines sorted transaction-first children
with whole-run knowledge for internal children.

`replay` deduplicates received reservations using the published records and
sorts them by source key. Allocation uniqueness derives strict ordering.
`replay_item_ready` proves that each referenced item's complete, item-producing
provider occurs in the actual sorted prefix. Closure is also preserved under
union and intersection; these structural facts do not instantiate the Sal
ordinary or recursive-base document theorem. Controls distinguish whole-run
clock observation, unknown references, canonical versus receipt order,
dependency-incomplete delivery, and reservations that produce no items.

## Raw parent-table extraction

`NotionCoreParentMap` defines physical item/origin rows and actual child
filtering, descending sorting, lookup and recursive traversal. The extractor
builds the existing rose-tree type. `extract_raw_model` derives its structural
adjacency/order/lookup relation from unique IDs and strictly increasing
parent-to-child counters, using the maximum stored counter as sufficient fuel.
No traversal equality or pre-existing tree is assumed. `extraction_covers_rows`
adds known-parent closure and derives that every stored row is reachable from
START and appears in extraction.

Fresh, known-origin integration history derives uniqueness, increasing rank
and closure; `reachable_extraction` gives the resulting complete extraction.
Raw orphan integration remains permitted by `insertFresh`, and a control
checks that START traversal omits the orphan until its dependency exists.
Other controls traverse tombstones and split markers in source sibling order.

`fresh_run_edges_any` connects literal appended run rows with the exact parent
edges of the existing recursive tree insertion, including START. This preserves
records and parent links, not merely observations. `ParentEdges` alone does not
assert sibling order, whereas `ForestModel` includes it. Establishing that the
incrementally updated ordered forest is exactly the raw table's extracted forest
remains a coupling obligation, as do deletion-flag updates and source payload
decoding in that complete execution.

## Source slice-tree shape induction

`NotionCoreSliceForest` models arbitrary finite slice trees. Its recursive
search uses actual endpoint extraction to test membership. Splitting transfers
all old children under the new right node; a separate recursive search detaches
that entire subtree and appends it to the freshly created title root.
`atomicSplit_result` derives the selected source and moved leaf from successful
execution. The leaf conclusion follows from the input invariant, rather than
being built into the split algorithm.

The state invariant contains root-only or empty-title-root-plus-one-leaf shape,
active-instance ownership, distinct block names, and physical emptiness of
inactive titles. `reachable_invariant` derives it from creation, updates to an
active instance, and actual successful atomic splits with fresh names. No guard
assumes the resulting shape or query answer. Instance updates abstract their
contents, so this frame theorem must still be coupled to valid RGA/endpoint
transitions; it does not independently establish interval coverage or progress.

The forest order is `blocks.values()` map insertion order, used by source
`#allNodes`. Appending a newly created block matches that search enumeration.
The separate displayed `blockOrder` inserts after the requested block and is
not represented by this list. Connecting displayed order and the materialized
document projection remains explicit. Controls check actual split/detach/append,
a reachable structural fixture, and a repeated split of an attached leaf.


## Ordered parent coupling and typed payload archives

`NotionCoreParentCoupling.edges_model` derives the ordered forest model from
exact parent-row permutation, unique item IDs and recursively ordered siblings.
`appended_run_traversal` preserves those facts through actual recursive insertion
and proves that traversal of the appended raw rows equals the resulting tree
preorder. The conclusion is not supplied as an input. A hidden-origin control
checks the complete traversal; an edge-equivalent forest with reversed siblings
shows why parent edges alone are insufficient. Origin presence/acceptance and
child dominance remain structural inputs to this theorem.

`NotionCorePayload` expands typed transactions into their actual atomic phases.
Bootstrap creates then inserts with the shared A@1 key. Split creates a fresh
block, inserts one marker, then moves its slice. `born_iff_record` derives the
issuance item-production tag from the expanded operations; create/delete IDs
cannot become fictitious RGA origins. `clockMax_reservation` derives the full
reservation bound from the actual operation list, including empty bootstrap.
Ordinary empty insertion/deletion emits no transaction. Pending deletes change
text visibility but leave split markers as markers.

`NotionCorePayloadNetwork` retains emitted typed transactions and their actual
mint-time received versions. Its projection computes all issuance records from
those payloads. `forget_reachable` derives whole-version issuance reachability;
`prepared_births_fresh` derives new item-ID disjointness against every earlier
emitted payload, even those not received by this issuer. `birth_ids_unique`
proves within-run uniqueness. `replay_located_provider` derives an earlier typed
provider for each referenced instance/item pair in the canonical sorted replay,
with the whole-provider clock bound. Tombstone flags do not change these birth
addresses (`birthAddresses_deleted`). The public conclusion identifies the
actual provider transaction, rather than merely an allocated range or Boolean
tag. Its controls distinguish same-instance ownership, overlapping allocation,
and unsorted newest-first archive enumeration.

The remaining selection premise is explicit: an emitted reference must occur
among a received provider's births in the selected instance. This layer does
not yet extract that fact from source `locateInsertion`/deletion selection and
the joint document state. It also does not prove block-creator availability,
block-name/string injection, deletion-range decoding, or display predecessor
validity. Those boundaries must connect to the slice forest and endpoint table;
no source execution or Notion RA certificate follows from allocation admission
alone. Search-label generation/uniqueness and its runtime exception boundary
remain part of that source correspondence.

Three pinned-source controls separately validate instance ownership, pending
text versus marker tombstones, and empty-request clocks. The pending-delete
fixture deliberately fabricates a future target at the raw RGA interface;
it is a primitive semantic control, not an honestly issued demo bug. The other
two use honest public requests. Literal records are in
`payload-provenance-observations.jsonl` under `experiments/notion-oracle/`.

### Search-label codec and same-instance uniqueness

The pinned `search-labels.js` (`b9cd62692c8b73060fb5c47ac0799cd6ec4f3a02077e150755f41c2b13b25c09`)
encodes one **to five**, rather than six, binary decisions per character.
For a nonempty chunk of length `d ≤ 5`, interpreting L/R as bits with numeric
value `p`, its character value before the ASCII offset is
`p * 2^(6-d) + 2^(5-d) - 1`. Thus it lies in 0..62 and never equals 31.
Its trailing-one count is exactly `5-d`; that count recovers the chunk length,
and division by `2^(6-d)` recovers `p`. These are direct algebraic properties
of the codec, not Lean-checked theorems in this increment.

Canonical labels concatenate five-bit chunks followed by one final chunk of
length 1..5; the empty path is the empty label. Every nonfinal encoded value
is even. This restriction matters: the two valid-character strings `LL` and
`D` both decode through `printableSearchLabel` to the path `LL`. The former
is noncanonical because its first chunk has only one decision. Consequently,
injectivity over arbitrary strings accepted by `decode` is false. On canonical
labels, character equality recovers each chunk uniquely, hence the whole path.

The two branches of `splitSearchLabel` implement path extension exactly. An
odd final value has `t ≥ 1` trailing ones: adding or subtracting `2^(t-1)`
changes the chunk encoding into the right or left extension respectively.
An even final value is already a full five-bit chunk, so the appended values
15/47 encode a new L/R chunk. The empty label follows this second branch.
This gives an inductive canonical-generation invariant, including arbitrarily
many chunk boundaries. Replacing one path `w` in a prefix-free frontier by
`wL,wR` preserves prefix freedom and excludes collisions with every other
frontier member. Canonical injectivity then gives label uniqueness.

This frontier describes slice **labels**, not the physical attachment tree.
In pinned `text-slice-tree.js`
(`c5167ec9fa2aee3a3264f0f0888cfeb821a09224f41f970818797b1dda808f91`),
`splitTextSliceTreeNode` replaces the selected label with its left child and
allocates a right-label node; transferring old children does not relabel them.
In pinned `document.js`
(`5c710856463c4941991b4f0fba348b7ea2ab1b3f6212558f0c3698733df37616`),
`#moveTextSliceIntoBlock` and `#moveTextSlice` detach and reattach the same
nodes, preserving their instance and label. A fresh block's empty title root
has its own instance, so its empty label does not collide with the attached
slice's label. Provided creation uses fresh instance identities and nodes
remain uniquely owned, splitting and movement preserve per-instance frontier
uniqueness. Arbitrary raw input assigning aliases, repeated creation identities,
or malformed ownership is outside this argument.

`search-label-controls.mjs` checks the pinned codec on all 8191 binary paths
through depth twelve and performs twelve honest `Replica.splitBlock` calls
with actual slice moves. Hand-derived checkpoints are depth five `=`, depth
six `=L`, and depth twelve `==D`. At every depth the original instance has
exactly the frontier `L^depth` and `L^i R` for `0 ≤ i < depth`; the fixture
checks this literal expected set, prefix freedom, unique runtime mapping keys,
and preservation of the lone `a`. Every document reconstruction runs the
source `#rebuildMappings` duplicate-label exception check. The literal record
is `experiments/notion-oracle/search-label-observations.jsonl`. Negative
controls distinguish the chunk boundary, a collapsed singleton frontier, and
the noncanonical alias. This is source-focused evidence and an explicit
algebraic proof route, not a mechanized codec theorem or a full execution
certificate for instance freshness and node ownership.

## Parent-table deletion and the combined-state boundary

`NotionCoreParentErase.lean` follows pinned `rga.js`'s existing-item deletion:
text targets acquire a tombstone, split markers keep their kind, and parent
links are unchanged. `erase_edges`, `erase_unique`, and
`eraseForest_ordered` preserve the exact table/tree coupling and sibling order.
`erase_traversal` then derives the updated raw traversal by mapping the
visibility update over the old traversal; `erase_traversal_ids` proves that
physical identities remain unchanged. No updated traversal equation is a
premise. Hand-derived positive and negative controls retain a deleted parent's
live child and descendant marker, and reject turning a marker into text.
Pending deletes for items not yet born are outside this existing-item update;
payload birth decoding already accepts the pending-deletion predicate, but a
combined interpreter must maintain that set.

The smallest faithful combined interpreter should keep instance-keyed parent
tables, pending tombstones, actual slice trees, and the source block-order
structure. Physical traversals and materialized slices should be derived from
these fields. A remaining coupling obligation is endpoint adjacency: actual
slice references, grouped by instance and sorted by physical start position,
must have stored stops equal to the next start or END, with full physical
coverage. Forest enumeration and displayed block order do not supply this
physical interval order. The atomic split must create its destination, insert
its marker, search the post-insertion traversal, split the selected node, and
detach/append its subtree. The combined typed interpreter below implements these phases with an injective
block-name encoding. The separate component proofs still need a joint execution
invariant and derivation of client selections from its materialized state.

## Graph invariants from typed replay provenance

`NotionCoreReplayGraph.lean` derives `Unique`, `Increasing`, and `Closed` for
`PayloadParents.prefixRows` from `PayloadNetwork.Reach`. These tables contain
actual expanded payload births in the selected instance. `all_births_unique`
uses prepared reservation freshness across the whole typed archive;
`prefix_unique` restricts that result to arbitrary filtered run lists.
`prefix_increasing` derives external parent ranks from the issuer's observed
clock and internal predecessor ranks from consecutive run IDs.
`prefix_closed` covers every prefix `pre` of a canonical received replay,
including the full replay. An external parent has a located provider earlier
in that prefix; an internal predecessor is born in the same included payload.
No graph predicate or desired traversal equation is an input.

`prefix_graph` and `canonical_graph` package these three structural results.
The deletion predicate may vary with replay state without changing identities
or parent links. Positive and negative controls distinguish internal run
parents from START, preserve tombstoned parents of markers, and keep split
markers in their inherited instance rather than the destination title instance.
This closes the replay-table graph guards; combining table execution, slice
endpoint coverage, displayed ordering, and client preparation remains separate.

## Exact edges of raw extraction

`NotionCoreExtractionEdges.lean` upgrades raw parent-map extraction to exact
`ParentEdges` under `Unique`, `Increasing`, and `Closed`. It derives extracted
ID uniqueness rather than assuming it. A counting lemma follows each item's
unique parent backwards: its traversal multiplicity equals its parent's
multiplicity, or one for a START child. Strict counter rank makes that descent
terminate. Actual lookup rows supply forward row membership; closed-map
coverage supplies the converse, yielding a row permutation.

`prefix_extraction_edges` obtains all three graph guards from typed canonical
replay provenance. `prefix_extraction_ready` then derives readiness of the
next transaction against that actual extracted prefix, without an externally
chosen forest or edge-coupling premise. These theorems address the parent-map
component. Slice endpoint coverage, pending-delete execution, block display
ordering, and full document/client refinement still need the combined state.
Controls preserve tombstones and marker rows while distinguishing source
sibling order from archive enumeration. A raw orphan control demonstrates why
closure is necessary for complete reconstruction.

## Typed prefix to checked machine row insertion

`NotionCoreMachinePrefix.lean` derives acceptance of the actual
`Machine.integrateRows` loop for the next canonical transaction's expanded
births in a selected instance. `transactionRows` filters the typed decoder's
actual rows. Its IDs are unique by the payload run allocation, parent rank is
derived from replay graph provenance, and separation from prior rows follows
from whole-reservation ownership plus strict canonical replay order.
`integrate_canonical_prefix` derives the append result without an accepted-step
premise. `integrate_prefix_permutation` accommodates any existing table
enumeration structurally equivalent to the decoded prefix.

The old-prefix and new-birth deletion predicates may differ. This permits an
actual pending-delete set to determine newly born tombstones without changing
identity freshness or parent rank. Controls append a two-character run after a
tombstoned origin, retain its internal predecessor edge, and distinguish
bootstrap's shared-key text births from metadata and a different instance.
The remaining combined-state obligation is to derive that each machine table
has the deletion-aware prefix representation throughout actual transaction
execution. This module does not assume or prove a rendered-document equation.


## Combined interpreter and checked slice extraction

`NotionCoreMachine.lean` executes typed atomic operation lists over per-instance
parent tables and pending deletes, arbitrary slice forests, and separate block
display order. It checks duplicate payload content while preserving old
tombstone status, retains existing-block placement on repeated creation, and
performs marker insertion before slice search/split/detach/append. Its
structurally recursive sibling sorter is proved equal to the parent-map merge
sort; concrete controls are kernel checked without native-decision axioms.
Bootstrap, hidden-origin insertion, concurrent split/insertion, conflicting
duplicates, tombstone-preserving duplicates, existing creation, and Map/display
separation each have a hand-derived positive and negative control.

`replay` consumes an ordered transaction list. This interface is not the
source constructor's sorting algorithm. The model omits JS wire decoding and
search-label validation, and checks bounds globally after marker splitting;
source splitting checks the two new intervals and the constructor validates
all slices after complete replay. The valid core correspondence still needs
the joint invariant proving these checks succeed. Malformed raw states do not
have a source-equivalence claim. `blockName_injective` preserves typed block
identity but does not prove correspondence with source string encoding.

`NotionCoreMachineSlices.sliceAtoms_factor` derives successful bounds checking
and exact interior extraction from a unique, structurally factored physical
traversal. `sliceAtoms_cell` specializes this to a partition cell whose stored
stop is the next physical cell's start or END. `empty_title_atoms` and
`attached_tree_atoms` connect actual tree preorder extraction to that cell while
retaining an empty inactive title's own START slice. These conclusions are
not assumptions. Physical factorization, instance existence, uniqueness, and
correct next-endpoint ownership remain explicit structural premises. Whole
replay must establish them; these lemmas do not themselves establish that
invariant. Controls distinguish a legal empty interval from reversed bounds
and demonstrate the neighboring text exposed by dropping a stored stop.

The directed pinned-source endpoint campaign passes 144 per-instance checks
across four closed concurrent-split versions and local followups with complete
deletions, fresh runs and repeated inherited splits. It groups all stored
slices, including empty inactive title roots, then orders them by physical
start. It checks START coverage and consecutive stop/start adjacency. A raw
received payload without dependencies creates an uncovered instance and is
explicitly outside the closed-version claim. This is bounded validation,
not an exhaustive network test or a proof of the invariant.


## Creator provenance is necessary for unconditional replay

Review identified a concrete missing admission obligation; the counterexample
is now kernel checked in `NotionCoreCreatorNetwork.missing_creator_control`.
`PayloadNetwork.Known` covers item references; START introduces no such
reference. From the unseeded initial network, an insert into `.initial` at
START can therefore be admitted without a preceding block creation. Its typed
machine step installs a parent table but no title. A subsequent split after
that item can meet item-provider admission yet find no source slice for its
marker. Similarly, a create with an absent predecessor has no item reference;
the raw machine's front fallback is not the independent guarded create rule.

This is a kernel-checked countermodel to using the earlier item-only typed
network reachability as a whole-interpreter progress premise. It includes
actual Reach witnesses and failed interpreter replay. It is not an honest
client trace or a new public demo bug. Existing graph, freshness and row-integration theorems retain
their stated scopes. Actual source selection and block/instance creator
provenance must refine the issuance model before unconditional replay progress
can follow. Assuming accepted replay would prove only conditional table
preservation and would not discharge this obligation.

The inspected two-message witness uses session `[66]`: first key `(1,[66])`
inserts `[97]` into `.initial` at START; key `(2,[66])` splits `.initial` after
that first item. Both item-reference obligations are satisfiable, but the first
message never created an initial title. A separate missing-predecessor witness
is a first create after `.issued (99,[90])`. These literal typed messages are preserved in the kernel counterexample.
Source selection now rejects the unseeded block, and creator-aware admission
excludes that first insertion.

Creator provenance must be paired with issuer-side active-gap selection.
Creation alone would still permit START in an empty inactive title instance.
Conversely, replay must not require the current owner to equal the payload's
requested block: concurrent splitting can transfer that interval, and source
routing deliberately searches globally. The current owner follows from the
physical partition, while the requested block's creator justifies placement
of the new destination block.


## Actual preparation and creator knowledge

`NotionCoreCreatorNetwork` reuses the typed archive's state and transitions.
Its separate Reach relation requires received creators for payload block and
text-instance keys, including START references with no item provider. It
forgets to the earlier item-only Reach and derives creator providers in saved
emission pasts and canonical replay prefixes. Creator births are metadata,
not RGA item births. This layer alone still permits inactive-title selection;
it is not the final source issuance policy or a replay-progress theorem.

`NotionCoreMachineCreators` follows the actual interpreter. Accepted replay
from the empty state can produce a forest block only through an actual
creation phase, and can touch an instance only through a created or referenced
payload key. Split/detach/move preserve block names. Received transaction
membership and creator-aware reachability therefore derive received creator
knowledge for every resulting block and instance. The accepted-replay premise
concerns the client's current reconstructed document. These retrospective
statements do not assume or establish success of its next edit or merged replay.

`NotionCoreMachineClient` extracts every actual slice in tree preorder, then
implements source selection: positive indices select the preceding live atom;
zero selects the first nonempty slice or the final slice if all are empty.
The source create-predecessor check uses forest membership in this core without
removed blocks. Empty insertions and empty deletions produce no payload.
Deletion address selection uses nonnegative JS slice clamping; negative or
fractional indices, instance grouping, ID-range compression, source string
parsing and search labels are outside these definitions. `decodeAddress` only
inverts the Lean interpreter's internal semantic names, with roundtrip proofs.
Option failure abstracts source exceptions and no-op returns, not their messages.

`locate_storage` derives both requested-block presence and selected-instance
presence from actual selection and checked extraction. `prepared_create_creators`,
`prepared_insert_creators`, and `prepared_split_creators` combine this result
with actual replay provenance to discharge metadata guards. No creator assertion
is supplied by the caller. The previous received transaction list and successful
current reconstruction remain explicit inputs to these component theorems.
The request network below supplies the canonical receipt list and derives item
guards and core delete messages. Complete replay progress remains open.

`own_selection_prepared` and `attached_selection_prepared` derive successful
actual location and the independent `PreparedGap` from unique block membership,
physical partition cells, valid index and, for attached leaves, an empty title.
They do not assume the chosen address or the desired semantic gap. The physical
partition still needs preservation in the same full replay. Controls cover
inherited zero selection before and after complete deletion, positive live
predecessors, missing blocks/predecessors and clamped deletion ranges.

Three pinned source fixtures validate the preparation boundaries. Public create
rejects an unknown predecessor before reservation; a clearly fabricated raw
payload instead uses the document interpreter's front fallback. Live and fully
deleted inherited leaves select the original instance's split marker at zero.
Finally, honest concurrent splits of `abc` move the second request's origin
into the first split's destination before replay. This refutes requiring replay
owner to equal requested block; it preserves global source routing and is not
an ordinary local-effect bug. The canonical replay remains source-key ordered,
while creator theorem membership works for any accepted received replay list.


## Positional issuance from canonical reconstruction

`NotionCoreMachineBirths.replay_row_birth` follows actual accepted integration,
erasure, creation and slice movement. Every stored row ID has a decoded birth
in an actual replayed transaction and the same instance. Deletion cannot change
that birth identity. `traversal_row_member` holds for arbitrary finite traversal
fuel, including malformed tables: traversal cannot invent a row. These are
retrospective provenance statements, not completeness or progress assumptions.

MachineClient now proves physical membership for extracted boundaries and
atoms. `physical_decode_progress` derives internal decoding from canonical
names produced by replay. `physical_decoded_known` combines actual row birth,
instance-name injectivity and receipt provenance. Successful insertion and
split preparation therefore supply every located reference guard, including
hidden origins and inherited split markers. START supplies no item reference.

`NotionCoreRanges.expand_compress` proves exact sequence equality with ascending
source-ID sorting, including duplicates. The codec changes physical target
order but preserves deletion flags. Pending-target membership is preserved;
raw pending-list equality is not asserted. This is a typed codec theorem:
positive safe JS counters, nonempty sessions, bounded UTF-16 units and wire
validation remain external boundaries.

`NotionCoreMachineDelete.selectErase` selects visible addresses, takes the first
address's instance, and validates every selected address in that instance.
It emits the expanded compressed IDs in source order and derives both item and
creator knowledge. Mixed-instance selections fail explicitly; generic source
grouping after merges is not implemented here. The supported core normal form
has one active instance, but total preparation from that invariant remains to
be proved. Positive and negative controls check sorted targets, inherited
instances and complete rejection of mixed input.

`NotionCoreReconstruction.transactions` filters the archive by a peer's actual
whole-run receipts and sorts by source ID. `transactions_runs` proves exact
projection to `NotionCoreIssuance.replay`; strict ordering follows from reachable
issuance. `transactions_received` supplies the receipt/archive correspondence
previously passed by callers. The list represents document-constructor order,
not the intermediate Replica Map enumeration. Wire parsing and conflicting-key
JSON equality remain separate; whole-version receipt is the adaptation domain.

`NotionCoreMachineNetwork.issue` checks source early no-ops, reconstructs that
canonical received version, prepares positional create/insert/delete/split,
reserves the issuing peer's clock and publishes the decoded transaction.
Its `Reach` has no item-knowledge or creator-knowledge premise. The checked
`creator_reachable` and `issuance_reachable` derive the existing archive and
allocation invariants from these concrete transitions. This is no longer an
arbitrary selected-payload issuer. It is still partial: `none` combines no-op,
invalid request and failed reconstruction. Successful issuance does not prove
its next reconstruction succeeds. The joint replay invariant, source label
validation and same-witness RA bridge remain open.


## Exact actual tables and next-row readiness

`NotionCoreTableView.rows` is a declarative storage view: chronological decoded
births with every prefix deletion target applied. It is not a second document
interpreter or a sequential specification. The append equation accounts for
both later deletion of an old birth and earlier pending deletion of a new
birth. Birth IDs, parent links and marker kinds are retained. Exact codec
output order is retained in the typed pending list.

`NotionCoreMachineTables.replay_tables` proves that every actual instance
lookup after accepted replay has exactly these rows and the chronological
pending-target list. It follows actual get/put operations, fresh checked
integration, erasure and the complete bootstrap/split phase sequences.
Creation and slice movement preserve stored rows. A reverse induction derives
the previous storage view from the accepted prefix; no per-step result view is
assumed. Global birth-ID uniqueness is its only additional freshness premise.
Identical duplicate raw birth insertion is outside this theorem's domain;
canonical immutable archives have unique keys and births.

`NotionCoreArchiveOrder` discharges that premise for canonical prefixes. It
also derives the permutation between chronological birth rows and the earlier
archive-ordered prefix view, using actual archive key uniqueness. Neither
permutation nor fresh IDs are supplied by a caller.

`NotionCoreMachineTableGraph.canonical_tables` composes these results.
`canonical_prefix_graph` establishes unique rows, increasing parent counters
and known-parent closure for the actual machine tables. Consequently its
actual length-fuel physical traversal has unique addresses. The next decoded
transaction's references occur in the actual same-instance table, and
`canonical_next_integrates` proves the checked row loop accepts its births.
Neither theorem assumes acceptance of that next transaction. The existing
positional network reaches this theorem through its derived payload-network
reachability. Full transaction success still needs slice routing, valid bounds,
fresh destination structure, detach/move and display alignment.

The source reality oracle now checks all stored fields against independent
literal decoding over the existing nine-event campaign: 293 instance tables,
1,534 stored rows and 27 tombstoned rows across 238 prefixes of 40 causal ideals.
The expected decoder does not call source range, RGA, traversal or selector
helpers. Wrong-instance and no-op-deletion variants are rejected. A separate
raw delete-before-birth fixture checks pending text deletion and undeleted
markers. It is explicitly not an honest issuance witness.

The source stores pending targets in a Set. The formal machine stores their
chronological list, including duplicates. The exact list theorem concerns the
formal machine; source correspondence is membership equality, not equality of
order or multiplicity. The saved full-field oracle compares pending Sets.
This increment does not prove the joint slice partition, source wire/label
validation, complete reconstruction progress or the same-witness RA bridge.


## All-reference partitions and split routing

`NotionCoreForestRefs.ownedRefs` enumerates every actual tree node with its
block owner, including empty inactive title roots. `splitForest_refs` derives
the exact selected-reference replacement from the actual recursive search.
Detach derives the removed subtree's contiguous preorder context; append
retains the existing children before the appended subtree. These are typed
algorithm lemmas over arbitrary trees. Source detach correspondence additionally
needs the core domain: the demo throws on a first matching title root, whereas
the typed detach searches children. Fresh markers and normal title starts
exclude that case. Duplicate block IDs are outside the source Map domain.

`NotionCoreMachinePartition.Partitioned` relates each actual instance's physical
traversal to cells and a permutation of its exact owner/start/stop references.
Stops are next physical starts, with END for the final cell. Every reference
names an existing instance. Owner uniqueness is per instance: an attached block
also owns an empty title in its own instance. It is not global owner uniqueness.
This is a structural factorization and reference relation, not an equation
assuming extraction or successful search.

From that relation and physical address uniqueness, `ref_extracts` derives
successful checked extraction and `partition_bounds` derives every current
endpoint check. A physical item which is not already a stored start supplies
an actual containing tree reference. `NotionCoreMachineRouting` proves strict
endpoint positions from the raw scan, then proves actual recursive split
search succeeds and its output bounds are valid. The composed
`splitForest_partition_progress` assumes neither a selected owner, a successful
search nor output bounds. Canonical-prefix address uniqueness was established
by the previous actual-table increment; the partition relation must still be
preserved in that same replay.

`NotionCoreMachinePartitionCreate.create_partitioned` proves actual fresh-create
success and preservation of this relation. Existing instance cells and refs
are retained; the fresh instance adds its START-only cell and empty title ref.
Fresh instance and block names are explicit inputs, not yet discharged here
from canonical creator provenance. A structural negative theorem proves that
an instance with no title violates the relation even if its text is empty.

The phase boundary matters: immediately after the split opcode, left and right
references have the same owner in one instance. Full `Partitioned` is therefore
an atomic-boundary invariant; the intervening phase needs a weaker relation
until movement assigns the right subtree to its fresh destination. The theorem
can use the old partition after raw marker insertion and before tree splitting,
with the marker in a cell interior. It does not assert partition preservation
after each opcode.

Pinned instrumentation checked 293 all-reference partitions and 1,827 physical
atom ownership occurrences over the existing 238 prefixes and 40 causal ideals.
It includes virtual START and every empty title. A hand-derived `ab` split at
index 1 requires two cells in the original instance and a separate empty title
cell in the new instance; omitting that title is rejected. The saved evidence
is `replay-slice-partition-observations.jsonl`. These bounded checks support
the structural candidate; full replay preservation and the RA bridge remain open.


## Actual insert/erase preservation from canonical issuance

`NotionCoreMachineSplice` connects the actual checked row integration and
`putInstance` to physical splicing after the selected origin. It derives
successful origin-tree insertion and the resulting physical context; no
chosen next forest or traversal equation is assumed. The text wrapper decodes
the literal run with actual pending deletion flags. Its generic premises are
structural old edges, ordering, freshness and origin presence. A singleton
marker theorem covers raw marker integration before tree splitting.

`NotionCoreMachineCanonicalForest` discharges those generic premises for the
next canonical nonempty insertion. The actual accepted prefix determines its
ordered extracted forest and exact parent edges. Archive provenance supplies
origin presence, sibling dominance and disjoint fresh birth IDs. The resulting
`canonical_insert_physical` derives actual operation success and physical
splicing without accepting any of those guards from the caller. It still
assumes the prior prefix was accepted.

`NotionCoreMachineErase` proves a stronger local fact: erasure commutes with
finite traversal without graph guards. IDs, parent links, child enumeration,
lookup order and traversal fuel are unchanged. Actual erase maps text flags
in the selected physical instance, retains markers and hidden parents, and
leaves other instances, the forest and display unchanged. This unconditional
finite-evaluator result does not make malformed cyclic raw graphs legitimate
source executions.

`NotionCoreMachineCreatorPresence` supplies the missing forward provenance.
Every instance created by an earlier accepted transaction persists; the
forest's own block names have supporting instances. Thus an earlier archived
creator, identified in the actual canonical prefix, establishes the next
required instance's presence. Empty metadata-created instances are included;
item-reference knowledge alone would not establish them.

`NotionCoreMachinePartitionUpdates.canonical_insert_partitioned` and
`canonical_erase_partitioned` compose these results. Under creator-aware
canonical issuance, an accepted prior prefix and its structural `Partitioned`
relation, the next nonempty insert or erase transaction executes and preserves
that relation. No selected owner, instance-existence guard, freshness, child
dominance, physical-output equation or next-step acceptance is a caller premise.
Erasure includes empty target lists. Generic structural splice preservation
alone does not establish fresh-ID uniqueness or normal slice shape; the
canonical insertion proof derives its required graph and birth facts.

The weaker creator-aware relation can still admit START insertion into an
attached block's inactive own-title instance. Such insertion can preserve
`Partitioned` while violating the intended empty-title/one-active-leaf shape.
The actual positional client-selection rule is therefore needed for that
stronger invariant; creator presence alone cannot establish it. This is an
intermediate-model boundary, not an additional honest demo failure.

The full induction remains unfinished: bootstrap/create and complete split
transactions must preserve the joint partition, normal active/empty title
shape and display alignment. The phase oracle makes the split obligation
precise. After tree splitting, both refs still have the old owner; after
detachment there is a transient coverage gap; append restores final coverage
and ownership. Two pinned, honestly issued traces preserve these observations
and a hand-derived wrong-final-owner control. They support the phase model,
not a universal preservation theorem. Source wire/label correspondence and
the same-witness RA bridge remain separate.


## Canonical create and checked marker composition

`NotionCoreMachineCanonicalCreate.canonical_destination_fresh` derives absence
of the next issued block name from both actual instances and forest blocks.
Earlier used names have earlier archived creators; canonical transaction-key
uniqueness excludes their equality with the next ID. Actual create success,
partition preservation, exact storage frames and a START-only destination
follow without caller-supplied name freshness.

`NotionCoreMachineMarkerProgress.canonical_split_marker_phase` composes this
actual create with canonical marker-row integration. It derives that the
selected source instance differs from the fresh destination, transports its
actual rows through creation, and derives the raw physical marker splice.
That intermediate state retains the old intervals, has unique physical IDs,
contains the literal split-boundary atom, and has no stored interval starting
at the fresh marker. Recursive search and the marker opcode's endpoint check
therefore succeed. Only acceptance and `Partitioned` for the old prefix are
assumed; next marker acceptance is a conclusion.

`split_transaction_of_atomic` connects a successful structural `atomicSplit`
result to the actual three-operation transaction. Its marker stage derives
checked bounds; split preserves forest block IDs, which derives existence of
the move destination. The helper takes the structural atomic result as input;
it does not itself prove partition restoration after movement. The following
preservation layer must establish that result and the final partition.

The pre-tree marker stage is intentionally distinct from the later tree-split
state, whose two references temporarily share one owner. No theorem here
claims `Partitioned` for that intermediate tree-split state.

## Inactive-title admission boundary

The new pinned `inactive-title-controls.mjs` trace starts with an honest split
of `ab` at 1. A separately fabricated raw insertion writes X into the new
block's own START instance. Honest zero-gap preparation instead selects the
inherited split marker in the original instance. Both display `Xb` and have
two tree nodes, but only the raw trace populates the inactive title.

`NotionCoreMachineInactiveTitleBoundary` checks that the raw choice satisfies
creator admission and preserves `NormalForest`, while refuting `EmptyInactive`.
Its positive control checks honest selection of the inherited marker. The
Lean counterpart uses a fresh next counter in the splitting session; the
source trace uses a fresh session at that counter. They test the same admission
boundary, not literal transaction equality. This countermodel explains why
honest client selection must enter the stronger invariant; it is not a fourth
confirmed demo bug.


## Bootstrap and actual active-instance selection

`NotionCoreMachineBootstrap.bootstrap_executes` derives successful atomic
bootstrap create/insert from the literal decoded run for any atom list.
`bootstrap_partitioned` proves its single title owns the whole physical
instance. Empty seeds retain a displayed empty block and virtual START; a
kernel PASS+FAIL control rejects omission of that physical instance.

`NotionCoreMachineShape` projects the combined interpreter onto the existing
normal-tree/profile/empty-title invariant. Fresh actual creation preserves
this invariant, and raw storage updates preserve it when the updated instance
is active. `atomic_split_active` establishes exact equality of the old and
new active-instance sets for accepted structural atomic split. In particular,
the fresh destination inherits the source instance; its own title instance
does not become active. These are structural preservation facts, not a whole
reachable-machine invariant.

`NotionCoreMachineClientShape.prepared_insert_active` and
`prepared_split_active` derive the active-instance premise from actual local
preparation, normal tree shape and physically empty inactive titles. They
inspect actual extraction and zero/positive index selection, including the
all-deleted inherited leaf. Accepted issuer replay supplies canonical internal
name provenance so decoding retains the selected instance. Neither theorem
assumes the next transaction's effect or selection from an unrelated replay.
The outstanding history transport must retain this instance in the canonical
prefix where the transaction later executes.


## Complete canonical split preservation

`NotionCoreMachinePartitionSplit.atomicSplit_partitioned` derives the actual
atomic tree result and its final all-instance partition. It finds a containing
reference from coverage, rejects the fresh empty title as a routing candidate,
and follows actual split/detach/move to recover the reference replacement.
Physical ID uniqueness and literal split-marker membership identify the exact
boundary atom inside the old cell. Cutting there preserves the raw traversal;
the fresh owner restores per-instance owner uniqueness. The right reference
moves to a different forest enumeration position, so the proof preserves the
per-instance reference permutation rather than assuming enumeration equality.

`NotionCoreMachineCanonicalSplit.canonical_split_preserves` composes this with
the canonical create/marker phase and checked interpreter bridge. Given a
creator-reachable archive, an accepted old canonical prefix, its `Partitioned`
and `ShapeInvariant` relations, and an active source instance in that state,
it derives actual complete transaction success and both invariants afterward.
It assumes no next acceptance, chosen owner, desired output forest, name
freshness or successful routing. The marker opcode's transient duplicate
ownership is never asserted to satisfy the final invariant.

The active-instance premise remains explicit and material. Actual local
preparation proves it in the issuer's reconstructed state; carrying it into a
different canonical prefix requires the honest-history provenance argument.
The raw inactive-title countermodel prevents dropping this obligation in favor
of creator knowledge. This theorem closes the conditional complete-split case,
not full reconstruction or the document-history/RA certificate.


## Honest-network replay without supplied structural guards

`NotionCoreRootCreators` classifies root providers by payload: bootstrap
creates the initial active instance, standalone create creates an issued active
instance, and split creates only an inactive own-title instance. Its archive
`RootProvenance` property records a received root provider for each insert/split
selection. Canonical closure places that provider in the actual earlier
transaction prefix, rather than merely proving some global creator exists.

`NotionCoreMachineRootReplay.canonical_prefix_reconstruct` derives execution,
`Partitioned`, `ShapeInvariant`, and the exact root-created active-instance set
for every canonical prefix, assuming creator reachability and this archive
property. The induction handles all payload kinds. It derives insertion's
nonempty run from actual admission, preserves inactive emptiness through erase,
and uses exact active-instance preservation through complete split.

`NotionCoreMachineHonestReplay.honest_root_provenance` then derives the archive
property by induction on actual positional-request network history. At each
request, the old archive property supplies the issuer's reconstruction
invariants; actual local preparation selects an active instance; exact root
classification identifies a received root provider for the new payload.
`honest_prefix_reconstruct` and `honest_reconstruct` consequently require only
`NotionCoreMachineNetwork.Reach`, a peer, and the chosen canonical prefix.
No prefix acceptance, partition, shape, selected-owner, active-instance or
root-provenance premise remains in these final theorems.

Bootstrap is not assumed first. A peer without initial receipts can issue a
lower-key standalone create before later receiving bootstrap. The pinned
`@1`/`A1` trace and kernel counterpart preserve that case.
`NotionCoreBootstrapProvenance` derives initial-name freshness in the actual
prior prefix; generalized bootstrap execution preserves independent earlier
blocks and their physical contents.

This closes reconstruction progress and the structural replay induction for
the typed core. Network reachability records successful actual request issuance;
it does not prove that every valid positional request is accepted. Actual
render/specification alignment, total preparation, wire/label validation and
the same-witness document-history/RA theorem remain separate obligations.

## Actual document projection and request progress

`MachineDisplay.reconstructed_aligned` proves that actual accepted replay keeps
unique forest keys and a display permutation of all keys. The literal display
insert-after splice equals the existing document specification's flatMap
insertion when its predecessor is present. `MachineBlockPresence` derives
persistent block membership and canonical required predecessors from creators.

`MachineDocument.honest_document` takes actual `MachineNetwork.Reach` and derives
successful reconstruction, successful projection to the existing SourceDocument,
and actual rendering equal to CoreSpec.view of that projection. It reads actual
display order and active interval contents, retaining inactive own-title anchors
in the semantic slots. It is a same-state observation theorem; transition and
history correctness do not follow merely from its existence.

`MachineDeleteTotal` and `MachineClientTotal` derive actual selection, internal
decoding, reservation and issuance for existing blocks with valid natural-number
gaps, nonempty insert atoms, or bounded nonempty erase ranges. Create permits no
predecessor or an existing predecessor. All output networks remain honestly
reachable. These endpoints do not assume prior selection or desired visible
effects. Oversized clamped deletion bounds and JavaScript wire decoding are not
claimed by the bounded request theorems. Early no-ops intentionally emit nothing.

`MachineFreshText` derives that every actual prior pending deletion target has
counter below the next canonical transaction. Every allocated text offset is
therefore initially live, independent of session ties; no desired flag premise
or acceptance of the next operation is supplied.

`MachineDocumentCreate.canonical_create_document` derives fresh creation and
its exact existing source-document create transition, including display order.
`MachineDocumentErase.erase_source_step` and `erase_spec_step` derive source and
independent-spec deletion from actual erasure and old materialization. They
preserve parent/marker identities and endpoints; no new materialization or
rendering equation is assumed. Insertion, atomic split, positional edit effects,
source runtime correspondence and the same-witness RA/history bridge remain open.
No fourth demo bug is claimed and no document certificate enters the ledger.
