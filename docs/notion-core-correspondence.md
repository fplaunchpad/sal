# Core correspondence: source invariants and proof route

This enquiry concerns honestly issued create/split/insert/delete transactions, with merge, slice movement outside split, removal of blocks, and formatting excluded. Source references use the exact seven hashes in `sources.json` and the function map in `notion-source-model.md`. The proposed invariants below are source-derived proof obligations; they are not yet a mechanized refinement theorem.

## A sufficient shape invariant

At transaction boundaries each block has one of these shapes:

1. Its title root is the only slice node.
2. Its title root has exactly one child, that child is a leaf, and the root's own text instance contains no RGA items. The child's instance may contain visible characters, tombstones, and split markers.

Every node interval remains one contiguous interval of its instance's RGA preorder. Intervals partition the text items of the instance, while boundary markers serve as stable addresses. Each instance's `start` address belongs to its original title root. Each split marker serves as the beginning address of exactly one moved right-hand interval. Blocks remain alive throughout the core fragment. Search labels distinguish intervals but do not affect the interpreted operation in the demo.

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
