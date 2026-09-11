# Consolidate MRDT ordering

## Semantic `rc` correction

Goal: make `rc` specify the intended resolution of concurrent events,
independently of concrete-update commutation. For LWW, increasing write-key
order selects the winner even though timestamp-max updates commute.

Status: machine-checked. Generic replay convergence needs only coverage of
noncommuting pairs, not the converse that every `rc` edge is noncommuting.
Its conditional-swap premise must refer to the semantic `rc` absorber used by
`loOn`, rather than assuming that absorber is concretely noncommuting.
The public correctness certificate continues to require an independent legal
sequential replay and query agreement; these sufficient algebraic laws are
not fields of `VerifiedMRDT`.

Falsifier: two respecting permutations with different concrete folds under
the revised laws, or exclusion of an acyclic timestamp policy for commuting
updates. Formal oracle: `convergence_on_of_replayLaws`, an all-commuting
constructor for `ReplayLaws`, the actual LWW instance, and positive/negative
LWW controls. The semantic oracle is the chosen ordinary overwrite-register
specification: the later timestamp wins, independently of delivery order.
No external implementation-equivalence claim is intended.

Validation: the formal-reference, paper, production, refactor, and negative
Lean ledgers build; `scripts/check-mrdt-refactor.sh` passes, including 186
runtime tests and validation of 569 benchmark-result schemas. The new LWW
controls and the generalized proof use no new axioms or admits. No new
randomized PBT campaign was run; the evidence is the general theorem plus
kernel-checked positive/negative controls. The standalone `lake build Sal`
target has no umbrella `Sal.lean`; verification uses the repository's named
ledger targets instead.

`scripts/check-working-papers.sh` also passes after rebuilding all three PDFs
with cached TeX resources outside the macOS sandbox. Its checks now follow
the current per-datatype profiles rather than the retired summary table.
The historical binary-law adapter now asks for full `RcAcyclic` explicitly:
its old timestamp-guarded no-chain premise alone cannot exclude self edges
or cycles on arbitrary equal-timestamp inputs.

## Claim

The public framework has one design-supplied ordering policy, `rc :
ReplayPolicy`. There is no second event-order datatype or policy. For a replay
context `C` and finite event set `E`, `loOn C E` is the sole order:

- a visibility edge is included exactly when `rc` classifies its pair as
  conflicting;
- a concurrent pair gains an edge from first to second exactly when `rc`
  returns `Fst_then_snd` in that direction; and
- the set-relative absorber clause prevents such a policy edge from being
  followed by a visible conflicting successor in `E`.

`Either` therefore means only “`rc` imposes neither concurrent direction.” It
also identifies a nonconflicting pair, so visibility alone contributes no edge
for that pair.

Status: machine-checked and migrated.

Formal oracle: `Instances/RcSPOT.lean`, the
`Sal.MRDTs.Metatheory.RefactorLedger` build, and the public `VerifiedMRDT`
theorem ledger.

The reusable replay laws require `RcAcyclic`, defined by the absence of a
nonempty `Relation.TransGen rc` cycle, including self edges. This replaces the historical
`no_rc_chain` law. Acyclicity allows useful chains, including three LWW writes
in increasing timestamp order, while excluding cycles.

The public relation is semantic: concurrent LWW writes are resolved in
increasing timestamp order. Concrete commutation is a proof technique, not a
definition of that relation. The sufficient `ReplayLaws` route now requires
only `noncomm_covered` (noncommuting pairs are ordered), acyclicity, and a
conditional-swap law for the semantic absorber. Ordered pairs may commute.
The historical biconditional remains only in historical theories and in
datatype-specific lemmas where it is actually true.

`ReplayLaws.of_all_comm` admits every acyclic policy for commuting updates.
The merge-law bundles explicitly carry that same policy rather than silently
selecting the default. LWW's concrete replay laws, Join theorem, replay
certificate, and ordinary-register certificate use its timestamp policy
throughout; the auxiliary empty-policy LWW proof has been removed.

## Migration consequence

Filtering visibility by conflict restores ordinary sequential specifications:

- The add-wins OR-set uses `Finset α`. Same-key add/remove conflicts are
  resolved remove-before-add; cross-key add/remove commutes and receives
  `Either`, so its visibility need not be preserved.
- Tombstone RGA uses `List Nat`. Its issuer may insert only at root or at a live
  anchor. The implementation still retains deleted anchors to integrate a
  child minted concurrently with deletion, and `rc` orders that child before
  the deletion. Sibling and parent/child insert conflicts follow timestamp
  order.
- The embedded and sided production RGAs already require a live anchor because
  their issuer guards demand that the anchor record occur in the materialized
  state.

## Checked controls

- `RcSPOT.LWW.old_no_chain_refuted` exhibits an allowed length-two `rc` chain.
- `LWWRegister.rc_order_acyclic` proves the timestamp policy has no cycle.
- `LWWRegister.replayLaws` instantiates the generalized laws with its public
  timestamp relation and concrete max updates.
- `LWWRegister.ordered_updates_commute` and
  `concrete_noncomm_iff_rc_refuted` pin the separation between semantic
  resolution and concrete noncommutation.
- `LWWRegister.reversed_assignments_wrong_winner` checks that the ordinary
  overwrite machine still needs the selected replay direction.
- `LWWRegister.canonical_respects` constructs a `loOn`-respecting sorted
  witness refining to the total overwrite register.
- `loOn_iff_of_rc_either` proves that the all-`Either` policy yields no edge.
- `ORSet.cross_key_rc_either` and `ORSet.same_key_rc_add_wins` distinguish
  commuting from conflicting set operations.
- `RGA.canonical_respects_rc` proves that the ordinary-list witness respects
  the single RGA relation.
- `RGA.GC.future_after_dead_anchor_not_applicable` checks the issuer-side
  live-anchor rule.
- The typed production and negative ledgers prevent obsolete interaction
  declarations from remaining part of the checked interface.

Trusted definitions are the chosen datatype policies, issuance payloads, and
sequential specifications. Lean checks their consequences; it does not decide
whether they are the intended external APIs.
