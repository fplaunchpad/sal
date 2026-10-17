# Notion typed core: protocol-scoped catalogue entry

The current implementation is `NotionCoreStructuralMRDT.D`: a finite set of
immutable origin rows, deletion targets, creation links and split-owner facts.
Updates decode one transaction into facts; merge unions facts. Its query traverses
those structures and folds creation links without replaying transactions.
`NotionCoreMRDT.D` remains the transaction-set reference used in the proof.
The original `NotionCoreProtocol.Reach`, injective session assignment, explicit
factory initialization and guarded client issuance remain the correctness scope.
This protocol-scoped entry is separate from the eighteen uniform contracts in
`Production.registry`.

The compiled indexed implementation maintains concrete row maps and child indexes,
plus transaction/archive and allocator metadata. Refinement connects its actual
receipt, direct merge and query functions to the structural model. The archive
still supports the original issuance protocol; semantic facts alone do not
recover allocation history.

| Claim | Checked endpoint |
| --- | --- |
| Structural carrier five VCs | `NotionCoreStructuralMRDT.fiveVCs` |
| Every registered version and current-head RA | `NotionCoreStructuralMRDT.versions_witness`, `specification_ra` |
| Actual target operations, including recursive bases | `NotionCoreStructuralMRDT.operational_reach` |
| Structural/reference query agreement | `NotionCoreStructuralMRDT.registered_query` |
| Indexed receipt and merge refinement | `NotionCoreRuntimeRefinement.receive_refines`, `merge_refines` |
| Acceptance on the honest domain | `NotionCoreRuntimeHonestProgress.receiveMany_honest`, `merge_honest` |
| Executable query for registered versions | `NotionCoreRuntimeTheorem.registered_query` |
| Constructive initialization and arbitrary-order receipt | `NotionCoreRuntimeEndToEnd.load_closed_version` |
| Original local positional effects | `NotionCoreMRDTClient.insert_effect`, `split_effect`, `erase_effect`, `merge_effect` |
| Reference RA with block merge | `NotionCoreProtocol.versions_witness`, `specification_ra` |
| The current retained facts omit merge information | `NotionCoreStructuralRender.SPOT.merge_outside_scope` |

The request set is create, insert, erase, split and block merge. The reference
carrier `NotionCoreMRDT.D` and its protocol theorems cover all five requests.
The structural carrier's RA, execution and query-agreement theorems take a
`NotionCoreMergeFree.MergeFree` premise: a merge's effect depends on which
blocks are alive when it replays, and `merge_outside_scope` proves that no
query on the fact set agrees with replay once merges are present. The
executable runtime refines the structural query on the same fragment and
refuses a merge transaction on receipt, so its registered-version query needs
no merge-freedom premise (`NotionCoreRuntimeRefinement.received_merge_free`).

The sequential machine is unchanged. Structural history transport reuses the same
reference witness after proving query agreement; it does not assume that
agreement. Native representation and query proofs provide a further refinement.
All these datatype-specific dependencies belong in the combined bridge/refinement
footprint, alongside the original sequential-history argument.

The independent document specification retains ordered semantic slots, hidden
anchors and split boundaries. It contains no transaction log, replay sort,
search labels, parent table or slice tree. These identities are necessary to
interpret prepared edits after concurrent deletion or splitting. Local requests
have ordinary positional effects at the issuer; a merged block stays in the
specification as a tombstone that the view omits; concurrent histories execute
the resulting identity-addressed atomic command groups. Natural-number valid
gaps, nonempty insertion and bounded nonempty deletion are supported. Early
no-ops intentionally emit no transaction.

Automation reuses the finite-store five-VC bundle, query transport and generic
commuting-carrier representation induction. Document meaning is not inferred
from union convergence: source allocation, provenance, interval ownership,
replay progress, actual client preparation, source-document simulation and
shared-archive execution pairing were proved separately. Those datatype-specific
proofs constitute the main manual burden. No measured person-hours or automatic
proof-generation success rate is claimed.

The positive core excludes formatting. Its block merge is the corrected design
of [the merge design note](notion-merge-block-design.md), not the demo's
three-operation merge. Five honest-client pinned traces expose two
bold-selection failures (N-002, N-003), one local suffix-split failure after
editing merges (N-001), and two merge histories that hide stored text (N-004,
N-005); see [the bug catalogue](notion-bugs.md). The merge extension removes
N-001, N-004 and N-005; the formatting failures remain. These editing merges
differ from the verified Sal version merges.

Correspondence with the seven hash-pinned demo modules is supported by source
audit and distinguishing executable evidence. The typed certificate is not a
kernel extraction of JavaScript objects, Maps, JSON, exceptions, safe-number
printing or opaque atom/string representation. Mathematical name/range codecs
and actual search-label uniqueness are checked within their stated domains.
No Notion production implementation correspondence is established.

See [the paper handoff](notion-integration.md), [current research claims](notion-research.md),
[the proof boundary](notion-proof.md), and [independent reviews](notion-core-review.md).
Publication and integration status are recorded separately; this entry alone
is not evidence that deployment or branch integration has completed.

The indexed algorithms are compiled from their checked Lean definitions. Native
execution additionally trusts the Lean/C compiler and runtime, JSON parsing and
the tested demo-to-typed codec. The recorded native oracle corpus passed 200
cases and 10,008 query comparisons. Native queries remain slower on the measured
mixed workload; no universal speedup or memory-saving claim is made. See
[the executable refinement](notion-executable-refinement.md).
