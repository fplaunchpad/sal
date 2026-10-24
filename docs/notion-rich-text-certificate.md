# The repaired rich-text protocol

The repaired typed Notion model has a positive sequential-history and
RA-linearizability proof. Formatting uses the maximal-run selection compiler
and one shared priority for every segment of a transaction. Distinct segment
IDs remain globally fresh. The old per-segment candidate and its `10011`
counterexample are retained separately.

The public theorem is
[`NotionCoreRichProtocolCertificate.specification_ra`](../Sal/MRDTs/Instances/NotionCoreRichProtocolCertificate.lean).
Its premises are an injective replica-to-session map and reachability through
the actual source/framework protocol. Successful replay, a state relation,
coordinate correspondence, endpoint availability and query agreement are
proved consequences. `versions_witness` covers every registered version;
`specification_ra` specialises the result to current heads.

## Operations and sequential meaning

The supported core operations are bootstrap, block creation, text insertion,
text deletion, split and corrected block merge. Positional indices are natural
numbers. Selections use the source's clipped `drop`/`take` convention; empty
selections issue no formatting transaction. The repaired compiler produces
before-item and END boundaries.

The client computes one Boolean from the complete current selection: remove
bold when every selected character is bold, otherwise add bold. It emits an
atomic assignment carrying that Boolean and all of the selection's regions.
Delivery preserves the issued value. All segments arbitrate using the same
transaction header, with distinct IDs retained for allocation and integrity.

The independent sequential state contains the displayed block document and,
for each text instance, retained physical cells, current character marks and
current insertion-gap marks. Cells include tombstones and split markers.
They retain the boundary information needed by subsequent edits. The state
contains no transaction log, annotation-operation list, arbitration priority
or replay sorting.

For a region with current physical boundaries `[l,u)`:

| Effect | Rule |
| --- | --- |
| Paint existing characters | Assign the issued Boolean at `l ≤ i < u` |
| Paint future insertion gaps | Assign the same Boolean at `l < g ≤ u` |
| Insert a run at gap `g` | New characters and the resulting gaps inherit the old gap mark |
| Delete text | Hide its cells while retaining their identities and gap marks |
| Split | Insert a hidden marker using the same gap rule, then move the displayed suffix |
| Corrected merge | Move the displayed slices while retaining instance cells and marks |

Thus insertion at the left boundary stays outside a mark; insertion at the
right boundary inherits it. Deleting an endpoint preserves its identity.
Two physical anchors at one visible position can have different inheritance:
an empty block's root and a moved split marker are a checked example. The
operation therefore retains the actual chosen instance and origin.

## How the proof connects

| Result | Source |
| --- | --- |
| Actual batch priority, distinct IDs and renderer | [`NotionCoreAtomicFormatting`](../Sal/MRDTs/Instances/NotionCoreAtomicFormatting.lean), [`Machine`](../Sal/MRDTs/Instances/NotionCoreAtomicFormattingMachine.lean) |
| Direct character/gap updates and independent document specification | [`RichSequential`](../Sal/MRDTs/Instances/NotionCoreRichSequential.lean), [`Document`](../Sal/MRDTs/Instances/NotionCoreRichSequentialDocument.lean) |
| Static transaction-to-specification input translation | [`RichSequentialInputs`](../Sal/MRDTs/Instances/NotionCoreRichSequentialInputs.lean) |
| Actual positional preparation and whole-transaction transport | [`RichProtocolNetwork`](../Sal/MRDTs/Instances/NotionCoreRichProtocolNetwork.lean), [`RichProtocol`](../Sal/MRDTs/Instances/NotionCoreRichProtocol.lean) |
| Five VCs for the actual rich-query carrier | [`RichProtocolCarrier.fiveVCs`](../Sal/MRDTs/Instances/NotionCoreRichProtocolCarrier.lean) |
| Projection into the existing honest plain protocol | [`RichPlainReach.erase_reachable`](../Sal/MRDTs/Instances/NotionCoreRichPlainReach.lean) |
| Derived compiler support, providers and boundary integrity | [`RichProtocolFormatFacts`](../Sal/MRDTs/Instances/NotionCoreRichProtocolFormatFacts.lean), [`RichCanonicalIntegrity`](../Sal/MRDTs/Instances/NotionCoreRichCanonicalIntegrity.lean) |
| Full canonical rich-history simulation | [`RichCanonicalHistory.canonical_history_version`](../Sal/MRDTs/Instances/NotionCoreRichCanonicalHistory.lean) |
| Public version witness, RA theorem and successful-query result | [`RichProtocolCertificate`](../Sal/MRDTs/Instances/NotionCoreRichProtocolCertificate.lean) |
| Derived exact caller selection and issued Boolean | [`RichSequentialSelection`](../Sal/MRDTs/Instances/NotionCoreRichSequentialSelection.lean), public `selection_exact` |
| Plain-query conservation at every registered version | [`RichPlainConservation.registered_version`](../Sal/MRDTs/Instances/NotionCoreRichPlainConservation.lean) |
| Nonempty actual framework execution invoking the public certificate | [`RichProtocolCertificateSPOT`](../Sal/MRDTs/Instances/NotionCoreRichProtocolCertificateSPOT.lean) |

Formatting reservations become clock advances in the plain projection; edit
IDs and payloads are preserved. The earlier structural proofs then apply to
the exact projected edit prefix. The rich proof additionally tracks both
character and gap marks. One actual whole-event enumeration supplies event
coverage, required order, full visibility, specification visibility and query
agreement. Ordinary merges and canonical recursive-base merges use this same
proof through the protocol's actual `StepV` transitions.

The guarantee is per version/head, with the full identified rich query.
It does not construct one prefix-compatible history of all successive reads.
The selection theorem establishes correctness of successful preparation;
it does not assert acceptance of every possible user request.

## Executable validation

The repaired path is tested in temporary copies of the seven hash-pinned
public demo modules. The cached sources, original `toggleBold` body and
maximal-run planner remain unchanged. The temporary patch derives the shared
priority from the enclosing transaction, rather than trusting a separately
supplied per-segment priority.

For each corrected merge variant, the current finite gate checks:

- 44 directed positive/negative cases, including the repaired fracture;
- 12,384 concurrent formatting/insertion cases over all Boolean patterns of
  lengths one to four, every nonempty range and insertion gap, both session
  orders, equal and unequal counter priorities, and both delivery orders;
- 70,992 later insertions probing every resulting gap, for 83,376 generated
  paired controls in total, with zero discarded cases.

Expected generated results come from a separate direct character/gap machine.
The old candidate is checked as a failing control: it returns `10011`, while
the shared-priority repair returns `10001`. Original N-002/N-003 reproductions
remain in the original-source suite. Results are in
[`atomic-priority.json`](../experiments/notion-formatting/results/atomic-priority.json).

```sh
lake build Sal.MRDTs.Metatheory.NotionFormattingLedger
sh scripts/check-notion-rich-text.sh /tmp/notion-formatting-sources
./scripts/check-mrdt-refactor.sh
```

Download the pinned cache using the command in the
[experiment README](../experiments/notion-formatting/README.md).

Independent reviews checked the public theorem's premises, every payload case,
the same-event witness, the direct-state specification and the nonempty actual
framework fixture. The complete local release gate passed 3,946 Lean jobs,
18 public certificate contracts, 13 certificate tests, 187 runtime tests and
569 benchmark records. The repaired ledger and load-bearing public results
depend only on `propext`, `Classical.choice` and `Quot.sound`.

The same release gate passed on the hosted runner for source revision
[`04bf222`](https://github.com/fplaunchpad/sal/commit/04bf22203447e5a6baafc80ccfb9a3e9182bca3b)
on 24 October 2026. The
[completed CI log](https://github.com/fplaunchpad/sal/actions/runs/40064692119)
confirms all of the counts above and the repaired ledger's axiom audit.

The formal result concerns this repaired typed model. Differential tests
validate the stated source behaviours on the recorded finite scope; they
are not JavaScript extraction or equivalence proofs. Raw demo operations
outside the typed core, including arbitrary stale/dead-block calls and
negative indices, and production Notion remain outside this certificate.
