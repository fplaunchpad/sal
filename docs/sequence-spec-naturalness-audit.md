# Sequence specification naturalness audit

Audit scope: source definitions and theorem statements read on 2026-10-14. This
records the source audit and subsequent checked refinements. Update and merge
algorithms are unchanged; native RGA restores its intended reserved-root guard. “Checked” below means a theorem exists for the stated language,
not that every packet field belongs in a natural client API.

## Research question

Can the sequence implementations share an ordinary client list specification,
with generated identifiers, coordinates, structural parents, and observed
anchors related to client requests by a separate refinement? For queues, can
the abstract language distinguish an ordinary destructive dequeue from an
idempotent removal of an observed head?

The decisive boundary is the update alphabet and its acceptance conditions.
An abstract state can be a plain list while its language still exposes
implementation metadata or a different operation semantics. A merge theorem
alone does not settle that boundary.

## Message-history contracts

| Family | Current independent abstract state and operations | Metadata role | Checked result and remaining client boundary |
|---|---|---|---|
| Native RGA | List of IDs plus a permanent allocation registry. Insert after a live ID, or root; remove named ID. | Insert ID is the event timestamp. Replica is ignored. Anchor identifies a visible list position. | `RGAConcretePort.history` proves an accepted strict-list witness, specification visibility, and the stored query on that same witness. Ordinary and recursive execution exports exist. A positional request-to-generated-ID/anchor adapter is not established by that theorem. |
| Native RGA missing-anchor variant | The same list/registry machine permits a missing anchor; insertion then changes allocation but leaves the list unchanged. | Same IDs and anchor inputs. | This is an explicitly different language, not another name for the strict editor API. Do not silently substitute it to discharge a strict-list obligation. |
| Embedded RGA | Ordinary list of `(id,value)` pairs. Insert immediately after a supplied anchor; delete by ID. | Generated coordinate prefix does not affect abstract step, but production legality checks its coherence against an earlier anchor record. Increasing inserted IDs are required by the proof language. | The local sequential adjacency theorem and the execution-scoped invariant bridge are checked. A client specification that erases prefix and Lamport-generation conditions needs a separate request/packet refinement. |
| Sided embedded RGA | Ordinary `(id,value)` list containing a root sentinel. Insert immediately before or after an anchor; delete by ID; query hides sentinel. | Side is semantically meaningful at this intermediate API. Coordinate prefix and monotone timestamps occur in legality. | Two-sided adjacency and the same-witness invariant history bridge are checked. Root-left insertion is a legitimate extra operation, so this API is not literally the one-sided embedded API. Positional request refinement remains separate. |
| Peritext over embedded RGA | Product of the embedded list machine and mark/attribute collections, observed through a document renderer. | Anchor IDs affect formatting boundaries; text coordinate prefix is packet provenance. | Full-event ordinary and recursive scoped history exports exist. The text component can share an ordinary list layer; the whole document cannot be identified with a plain list of values. Formatting acceptance and rendering need their own observable contract. |
| Sided Peritext Core and RichCore | Sided text plus independent mark/deletion collections; RichCore adds rendered document observations. | Stable IDs identify text and marks. Side and mark boundaries affect observable order/formatting. | The production certificate path is explicitly native insert-only for text; do not advertise unrestricted text-delete correctness from it. Core/RichCore history exports exist for that issuer scope. Their text part can reuse the two-sided list abstraction, but native operation scope and rendered queries differ. |
| FugueMax | Permanent identity list and deletion marks; generated insertions name a stable left origin, deletions name an ID. Clients request positional edits. | Structural parent, side, right origin and chain stay in generated implementation messages; none occurs in the independent sequential action. | Physical positional refinement and complete natural invariant-scoped RA certificate are checked through the five VCs, for ordinary and recursive executions, with maximal noninterleaving on the same witness. The old live-parent language remains an explicitly rejected alternative. |
| Historical mergeable queue | List of tagged values. Enqueue appends; removal names a previously observed head. A repeated target already absent is legal and a no-op. Query returns tagged head. | Tag selects which element was observed; it is semantically load-bearing under concurrency. | Sequential ordinary FIFO refinement is checked under `qOK`. The concurrent public certificate uses the idempotent named-head language, not unconditional `tail` on every dequeue event. |
| Anchored-enqueue queue | The same tagged FIFO language: enqueue appends; a live named removal must target current head; an already absent, previously born target is a no-op. | Tail anchor and coordinate certify enqueue placement but are ignored by independent FIFO step. Dequeue target remains semantically relevant. | The schedule, public tagged-head witness, and ordinary/recursive execution certificates are checked. It is a different implementation and issuer from the historical queue; it shares the named-head abstract behavior, not its operational graph. |

## Source map

- Native list and canonical replay: `Sal/MRDTs/Instances/RGASequential.lean`
  (`listStep`, `listLegal`, `listSpec`, `canonical_refines_list`). The public
  strict and missing-anchor machines are
  `Sal/MRDTs/Paper1/RGAIdentified.lean` (`machine`, `strictSpec`,
  `missingNoopSpec`), lifted without changing event inputs by
  `Sal/MRDTs/Paper1/RGAEventSpec.lean`. The full criterion bridge is
  `Sal/MRDTs/Paper1/RGAConcretePort.lean` (`history`, execution exports).
- Embedded list: `Sal/MRDTs/Instances/EmbedRGASequential.lean`
  (`eSpecStep`, `eSeqOK`, sequential adjacency/refinement), and
  `Sal/MRDTs/Instances/ProductionRGA.lean` (`embedSpec`, `embedLegal`).
  Full specification visibility is handled separately by
  `Sal/MRDTs/Paper1/CertifiedRGAInvariantHistory.lean`; its
  `canonical_valid_history` conclusion combines replay equality, specification
  visibility, and admission on one history.
- Sided list: `Sal/MRDTs/Instances/SidedEmbedRGASequential.lean`
  (`sInsBefore`, `sInsAfter`, `sSpecStep`, `sided_seq_read`),
  `Sal/MRDTs/Instances/ProductionRGA.lean` (`sidedSpec`, `sidedLegal`), and
  `Sal/MRDTs/Paper1/CertifiedSidedInvariantHistory.lean`.
- Document products: `Sal/MRDTs/Instances/Peritext.lean`,
  `Sal/MRDTs/Instances/SidedPeritext.lean` (`richSpec`, `richGeneration`),
  `Sal/MRDTs/Paper1/CertifiedPeritextInvariantCertificate.lean`,
  `CertifiedRGACoreCertificate.lean`, and `CertifiedRGARichCertificate.lean`.
  `CertifiedRGACoreCertificate` requires `NativeInsertOnly` when constructing
  the chronological text witness.
- Fugue mismatch: `docs/fugue-spec-source-audit.md`,
  `Sal/MRDTs/Instances/FugueMaxContract.lean` (`listLegal`),
  `FugueMaxListRefinement.lean` (`listStep`), and
  `Sal/MRDTs/Paper1/CertifiedFugueInvariantObstruction.lean`
  (`valid_execution_counterexample`). Source-correct issuer and coordinate
  evidence are in `FugueMaxIssuer.lean`, `FugueMaxHonesty.lean`, and
  `FugueMaxOriginBounds.lean`.
- Historical FIFO: `Sal/MRDTs/Instances/QueueSequential.lean`
  (`qSpecStep`, `qOK`, `queue_seq_sound`), `QueueContract.lean`
  (`clientStep`, `clientLegalAux`, `clientSpec`), and
  `QueueConditioningSPOT.lean` for concurrent duplicate-head behavior.
- Anchored FIFO: `Sal/MRDTs/Paper1/AnchoredQueue.lean`
  (`CanIssue`, `fifoStep`, `fifoApplicable`, `fifoLegal`),
  `AnchoredQueueHistory.lean` (`NextLegal`), `AnchoredQueueSchedule.lean`,
  `AnchoredQueuePublic.lean`, and `AnchoredQueueCertificate.lean`.

## Shared specifications and genuine differences

The natural reusable text layer is a list with fresh stable element IDs,
value insertion at a visible position, ID-addressed idempotent deletion, and
queries returning visible values. A named visible anchor is an intermediate
representation of a position, not a generated structural parent. Freshness
can be stated over allocated IDs without importing a coordinate codec or
requiring client timestamps to increase. Packet coherence and source Lamport
conditions belong in the request-to-message relation and issuer proof.

The one-sided and two-sided buffer programs share splice and deletion lemmas.
They still expose different operation alphabets: before/after with a sentinel
is more expressive than insert-after with a root-front convention. A shared
positional list specification is plausible, but needs checked projections of
both request alphabets. Existing local adjacency lemmas are useful inputs;
they are not already those projections.

Strict insertion and missing-anchor no-op are different semantics. Likewise,
ordinary `dequeue` that consumes the current head on every accepted operation
is different from “remove the head I observed,” which can be idempotent when
two replicas remove the same tag. This difference must stay visible in the
public queue API. Tags may be hidden from returned values only after an
observation/refinement theorem; erasing tags from removal requests can erase
which operation the implementation actually performed.

The anchored queue is the current Queue for this campaign. KC explicitly
excluded the historical implementation from consolidation; the following is
a retained research note. The anchored and historical queue languages may
share a common tagged-head specification. Their independently written abstract steps differ on illegal
middle-target removals: historical `clientStep` leaves the queue unchanged,
whereas anchored `fifoStep` filters the target. Their legality rejects that
case, so compare the languages on admitted histories rather than claiming
unconditional equality of the raw step functions.

## Refinement checklist and established boundary

1. Specify the client request alphabet independently: valid positional insert,
   delete by position or stable ID, and its return values. Keep the generated
   replication message as a separate alphabet.
2. Prove each source issuer prepares a message representing that request in
   its current visible view. For embedded variants, erase coordinate prefixes
   at this boundary while retaining enough provenance to prove placement.
3. Prove admitted message histories refine client histories while preserving
   observable answers and the event identities required by the RA criterion.
   A local sequential simulation alone does not supply the concurrent witness.
4. Preserve one history satisfying the policy order, specification visibility,
   abstract admission, and stored query. The existing invariant-history
   theorems provide this shape and should remain the acceptance gate.
5. For FugueMax, connect the checked physical positional refinement
   (`FugueMaxHonestPhysicalRefinement.honest_physical_insert_refinement`)
   to a complete certified history theorem. The origin-tree construction,
   specification visibility and final `FugueMaxNaturalCertificate` are checked.
   Local placement and the global same-witness result are separate theorems.
6. For queues, choose explicitly between destructive FIFO dequeue and observed
   tagged-head removal. Keep the checked duplicate-dequeue negative control
   when considering a simpler client alphabet.

The local preparation obligations for native, Embedded and Sided RGA are now
proved below. Queue retains observed-head semantics, and FugueMax has the full
natural global certificate. Existing RGA global witnesses retain their
identified-operation languages. A new concurrent history alphabet consisting
only of positions, or a metadata-free document UI, is not claimed.

### FugueMax implementation-order boundary

The final certificate must use the existing `InvariantOrder` criterion with
`CertifiedFugueInvariant.Valid`. This domain requires sorted records with
provenance from the execution, and has separately proved initial-state,
update, and merge closure. It is not a predicate chosen to fit the new witness.

The raw, all-states criterion is stronger: filtering a malformed unsorted list
can change where a subsequent insertion lands. The checked scratch-state
example in `CertifiedFugueRawOrderObstruction` already establishes this
distinction. Consequently, an insertions-before-deletions witness cannot be
justified by claiming that unrelated insertions and deletions commute on every
raw state. The intended proof uses their existing valid-state commutation
theorem and checks specification visibility separately on the same witness.

## Native RGA positional boundary

`Paper1/RGAClientLocal.lean` adds a positional request adapter for the source-faithful
issuer. `prepared_canIssue` proves issuance from a complete live view and
fresh metadata; `covers_original_issuer` supplies a request for every originally
applicable message. `prepared_refines_identified` proves its strict identified
list effect with explicit uniqueness and exclusion of visible ID zero.
`apply_clock_above_observed` derives clock monotonicity from an actual apply
step, rather than assuming it follows from the application guard alone.

KC clarified that both the original paper and implementation reserve zero for
the root. Lean's earlier issuer omitted that convention. The checked trace
allocates zero, reads `[0]`, and turns insertion at index 1 into `[1,0]` rather
than `[0,1]`. This diagnoses the missing formalization guard; it is not a
counterexample to the source RGA algorithm or its intended issuance domain.
The correction is checked: insertion IDs are positive in the issuer and both
identified sequential languages. `certified_no_root` proves the invariant for
ordinary and recursive certified executions, and `prepared_refines_certified`
uses it at the client boundary. The old trace is an explicit dropped-guard
regression whose insertion fails the corrected issuer. Update and merge
algorithms are unchanged.

`RGAClientPhysical.certified_query_prepared` now proves the direct local equation
`RGAM.query (RGAM.update s event) () = Client.step (read s) stamp request`.
Its premises are a certified source execution, an actual certified apply step,
the actor's head/version lookup and successful positional preparation. Finite
birth support, unique IDs, a fresh timestamp, an undeleted new ID and a live
anchor follow from execution and the original issuer guard. The recursive
execution variant proves the same equation. This complements the separate
global history bridge: it proves the effect of this particular client edit.

## Certified embedded client effects

`EmbedRGAClient.certified_prepared_physical` and
`SidedRGAClient.certified_prepared_physical` prove that successful positional
preparation at an actual certified source produces the requested physical
insert/delete effect. Their premises are the source execution, an actual apply
step, the actor's head/version lookup, and successful preparation. Sortedness,
unique positive IDs, chain provenance, and a clock above the source records are
derived through the existing five-VC execution results. No `eSeqOK`/`sSeqOK` or
caller-supplied coordinate invariant remains in these local theorem premises.
The global admitted-history languages are unchanged; this does not erase their
metadata guards or expand the native Core/RichCore text-operation scope.
