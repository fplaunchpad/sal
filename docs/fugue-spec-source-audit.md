# Fugue client operations and structural parents

Original audit: source comparison and a hand-derived single-replica scenario.
Follow-up: `FugueMaxNaturalCertificate` now proves the replacement origin-list
contract through the five VCs, and `FugueMaxHonestPhysicalRefinement` proves the
actual positional client effect. The source issuer and implementation are unchanged.
The five merge VCs and their expansion proofs concern a separate equality
boundary and do not establish correspondence to the original client API.

## Finding

The former live-parent sequential contract interprets the structural parent in a generated
Fugue message as a live-list splice anchor. Original Fugue allows this parent
to be a tombstone. For the insert/delete/insert scenario below, the issuer's
choice is consistent with the original algorithm; the live-parent requirement
and the resulting splice semantics are the mismatched trusted boundary.

## Primary-source evidence

[Weidner and Kleppmann, *The Art of the Fugue*](https://arxiv.org/pdf/2305.00583),
Section 4, printed pp. 4–6: the public API is positional `insert(i,x)` and
`delete(i)`. Algorithm 1, printed p. 5, lines 23–28, selects the preceding
visible element, then the next structural node including tombstones. The new
node may become that structural successor's left child. Deletion hides the
value while retaining the node. Section 5.3, printed p. 8, changes right-child
sibling ordering for FugueMax rather than this public API or parent rule.

The authors' [FugueMax Simple implementation](https://github.com/mweidner037/fugue/blob/31e74fea67f23add13a5d10f781c0d78edcd14da/fugue-max-simple/src/index.ts#L476),
revision `31e74fea67f23add13a5d10f781c0d78edcd14da`, independently confirms:

- Lines 476–489 expose positional insertion and select its preceding live node.
- Lines 492–508 select a right child or a left child of the structural successor;
  the latter selection includes tombstones.
- Lines 281–285 find the structural leftmost descendant without testing deletion.
- Lines 515–524 expose positional deletion and generate an ID-addressed message.
- Lines 535–550 integrate insertion through parent ID and retain deleted nodes.
- Lines 244–276 exclude deleted nodes from indexed lookup.

These source locations distinguish client requests from generated replication
messages. The structural parent is an implementation field, not a requirement
that the parent appear in the current visible list.

## Local definitions and the scenario

`FugueMaxIssuer.lean:68` chooses the live preceding identity for positional intent
and passes it to `mGenInsAfter`. `FugueMax.lean:368` can then choose a different
structural parent: when root already has a right child, insertion at position
zero becomes a left child of root's structural successor. Birth metadata keeps
that successor available after its visible deletion.

Hand-derived source trace: insert element 1 at index 0; delete index 0; insert
fresh element 3 at index 0. Root retains child 1, now deleted. The third request
selects root as its visible left origin and tombstone 1 as structural successor,
so its message has parent 1 and side L. Its client result is the singleton
containing element 3.

`FugueMaxImplementation.lean:22` stores generated `op`, left origin, right
origin and chain in `Payload`. However, `FugueMaxContract.lean:14` requires an
insertion's `op` parent to be undeleted in its sequential prefix.
`FugueMaxListRefinement.lean:13` executes that same parent as a visible-list
splice anchor. `SidedEmbedRGASequential.lean:55` returns the unchanged list when
a before-anchor is absent. Thus the sequential program rejects the third
message and, even if legality alone were relaxed, cannot produce its insertion.

## Recommended correction for review

Do not restrict the original issuer to live structural parents merely to satisfy
this list contract. First separate generated message fields from client intent.
A proposed independent client specification should execute positional edits or
an explicitly justified stable visible-gap abstraction, and separately relate
those requests to generated parent/side/origin/chain fields. The relation must
handle tombstone parents and concurrent changes to the issuing view.

Removing only the undeleted-parent conjunct is insufficient: the current step
still loses insertions whose parent is absent. Replacing parent by left origin
alone is also not yet justified: backward insertion, same-gap siblings and
concurrent-origin histories require a separate ordering argument. A tombstone
sequence machine is another possible intermediate specification, but must not
be presented as an ordinary visible-list ADT without a refinement theorem.

This audit identifies the local mismatch; it does not prove a complete replacement
specification, API equivalence for all executions, or the original strong-list
and maximal-noninterleaving properties for the current Sal carrier.
