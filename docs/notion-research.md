# Notion demo MRDT investigation

The unchanged published demo cannot satisfy the full ordinary local editing
contract investigated here. Honest split/merge histories expose both a local
split failure and a local formatting failure. These failures precede the
sequential-history bridge: no choice of RA witness can make a locally issued
request have an effect that it does not have. This is a result about the pinned
educational demo, not Notion's production implementation or a limitation of
Sal's five-VC theorem.

The narrower split/insertion/deletion-only milestone remains open. An independent
identity-based sequential model passes a bounded differential gate, and Lean
checks useful semantic laws and counterexamples. Neither testing nor the
transaction-set adaptation supplies the missing general refinement proof.

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
| Independent core semantics | Executable slot machine; 4,500 comparisons; kernel split/delete laws and boundary controls |
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
