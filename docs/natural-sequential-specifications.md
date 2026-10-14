# Natural sequential specifications

This campaign checks two different claims: generated replication messages have
an admitted sequential history, and generating a message implements the client
request at its issuing view. A checked message-history bridge does not by itself
establish the second claim. The update/merge implementations, intended issuance, five VCs and selected
RA criterion remain fixed. Native RGA restores the source's reserved-zero guard
that the earlier Lean issuer omitted.

## Current audit

| Datatype family | Natural client contract | Current message-history bridge | Client interpretation and remaining work |
|---|---|---|---|
| Grow-only set, including finite and Boolean carriers | Insert an element; read the set | Checked | Replaced the application-log state with a mathematical set or finite set. Complete history-language equivalence is checked, including interspersed queries. |
| Integer, increment-only and PN counters | Add the requested integer delta; read an integer | Checked | Replaced the log state with an integer balance. Complete history-language equivalence is checked for every delta interpretation. |
| Ordinary and efficient OR-set | Ordinary finite set: add, remove, membership | Checked | Both now instantiate `NaturalSetSpec.model`. `ORSetSharedSpecification.admits_iff` identifies their complete history languages after renaming operation constructors and retaining event identity. Concrete algorithms remain distinct. |
| Enable-wins and disable-wins flags | Enable, disable, Boolean read | Checked | Both already share a Boolean sequential machine. Their distinct merge policies select different concurrent outcomes. Neem's application source omits the query; the Boolean interpretation is explicit. |
| Published bounded counter | Increment/decrement a scalar; transfer and inspect local rights | Checked, including ordinary/recursive executions and local/global bounds | Independent scalar and account balances match the observable API. The transfer matrix is absent from the sequential state. |
| LWW register | Write a value; read the most recent sequential write | Checked | Sequential state is an optional value, without timestamps. The bridge selects a timestamp-consistent witness. |
| Multi-value register | A local write replaces all currently observed values; concurrent writes may remain together | Checked identity-addressed overwrite language | `MVRClient.prepare` accepts a value and captures all live write identities. Its issuance equivalences and local singleton replacement/read are checked for both representations; historical freshness additionally excludes dead prior identities, and its local effect theorem derives overwrite coherence from a certified source version. The concurrent value-set contract remains distinct from a singleton register. |
| Native RGA | Positional edits over an identified list | Identified-operation contract and reserved-root correction checked | The issuer and strict/missing identified languages now require positive insertion IDs, matching the source's reserved root. `RGAClientLocal.certified_no_root` derives exclusion of zero for ordinary and recursive certified executions; the positional adapter uses it. The old zero trace is retained only with an explicit failed issuance guard. `RGAClientPhysical.certified_query_prepared` and its recursive variant prove the actual updated implementation query equals the positional edit. Freshness, finite support and view uniqueness follow from the certified execution and actual apply step. |
| Embedded RGA and document variants | Positional edits and visible text; documented mark operations | Checked for their existing identified-operation contracts | `EmbedRGAClientLocal` and `SidedRGAClientLocal` now derive physical positional insertion/deletion from a certified source and actual apply step, with no assumed legal replay history or coordinate invariants at the public theorem boundary. Existing global identified-operation languages remain; document mark semantics and the Core/RichCore insert-only scope remain distinct. |
| Anchored Queue | Enqueue a value; dequeue the observed head | Checked | `AnchoredQueueClient.prepare` generates the tail coordinate or head identity. `prepared_canIssue` and `prepared_refines` prove the unchanged issuer accepts the message and its local effect is append/pop on a sorted, fresh, unique-ID issuing state. Empty dequeue generates no event. Concurrent duplicate removals still use the checked idempotent named-head language; this is not a destructive-dequeue concurrent specification. |
| FugueMax | Positional insert/delete; generated messages project to stable insertion ID and left origin, or deletion target | Physical client refinement and certified natural RA bridge checked | `FugueMaxHonestPhysicalRefinement` proves the actual local edit. `FugueMaxNaturalHistory.natural_witness` constructs a permutation of the original events admitted by the origin-only language, with the exact source query and specification visibility. `FugueMaxNaturalOrder.respects_order` checks the existing valid-state implementation order. `FugueMaxNaturalCertificate.correct` and `correctV` connect these results through the five VCs for ordinary and recursive executions, with maximal noninterleaving on the same witness. |
| TreeMove and AegisSheet | In-place tree and sheet edits | Existing bridges checked | Audit completed: tree effects are ordinary cycle-checked moves with causal-origin legality; the sheet machine retains observed versions, tokens and undo context. A visible-sheet-only transition is already refuted for the current message alphabet. Request elaboration remains separate. |

The [sequence audit](sequence-spec-naturalness-audit.md) records the exact
RGA/Queue contracts and genuinely different operation semantics. The
[source audit](fugue-spec-source-audit.md) records the mismatch in FugueMax's former live-parent language.
The [remaining-family audit](natural-other-datatypes-audit.md) covers registers,
flags, the published bounded counter, TreeMove and AegisSheet, with exact
source declarations and the limits of their client interpretation.

The state simplifications use `DeterministicSpec.Abstraction.admits_iff` in
`SequentialAbstraction.lean`. The four instantiations in `SimpleEventPorts.lean`
are `set_language_preserved`, `finite_language_preserved`,
`boolean_language_preserved` and `delta_language_preserved`. This is an
equivalence between sequential machines; it does not change implementation
equality or the five-VC framework. The downstream `SimpleConcretePorts` build
was independently checked after these changes.

## Evidence rules

- Prefer ordinary abstract data: sets, integers, Booleans, values and identified
  lists. Coordinates and ordering encodings belong in implementation proofs.
- Stable IDs may identify the effect of a request across concurrent changes.
  Show how they are generated from a natural client request.
- A state simplification must preserve the complete admitted history language,
  including interspersed queries, not merely one final observation.
- Test replay candidates against Sal's actual implementation-order and
  specification-visibility obligations. Failure under full causal replay alone
  is not an RA-linearizability counterexample.
- An intermediate tombstone/gap machine is not a completed client bridge.
  Require both local request correspondence and the certified execution theorem.
