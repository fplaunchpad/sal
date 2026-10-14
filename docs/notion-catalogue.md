# Notion typed core: protocol-scoped catalogue entry

The instance is `NotionCoreMRDT.D`: a finite set of immutable typed transactions,
whole-transaction insertion, union merge, and source-key-sorted actual typed
replay/render query (`Option View`). Its theorem is scoped to
`NotionCoreProtocol.Reach`, with injective session assignment, explicit factory
initialization and guarded ordinary client issuance. It is a distinguished
protocol-scoped research entry, not an additional unrestricted contract in the
eighteen-entry `Production.registry`.

| Claim | Checked endpoint |
| --- | --- |
| Carrier merge proof | `NotionCoreMRDT.fiveVCs`, transported from finite-store VCs through `QueryLift` |
| Every registered version | `NotionCoreProtocol.versions_witness`: one event witness for enumeration, required order, specification visibility and actual query admission |
| Current-head RA criterion | `NotionCoreProtocol.specification_ra` |
| Actual client/MRDT transport | `NotionCoreMRDTClient.issued_update`, with valid insert/split/bounded-delete visible-effect wrappers |
| Merge-base scope | Actual ordinary and canonical recursive virtual-base Sal merge steps |

The independent document specification retains ordered semantic slots, hidden
anchors and split boundaries. It contains no transaction log, replay sort,
search labels, parent table or slice tree. These identities are necessary to
interpret prepared edits after concurrent deletion or splitting. Local requests
have ordinary positional effects at the issuer; concurrent histories execute
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

The positive core excludes editor merge-block/movement and formatting. Three
honest-client pinned traces expose two bold-selection failures and one local
suffix-split failure after editing merges; see [the bug catalogue](notion-bugs.md).
These editing merges differ from the verified Sal version merges.

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
