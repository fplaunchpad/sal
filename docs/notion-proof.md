# Notion split proof enquiry

## Question and falsifiers

**Goal:** connect a faithful MRDT adaptation of the pinned published demo to an independent block/text sequential specification through the existing five merge VCs and a separate history bridge.

**Candidate claims:** (1) replaying positional client requests explains the crossing-delete observation; (2) retaining semantic character identities and split gaps explains that observation without retaining transactions; (3) the full adaptation meets the ordinary editing contract on every honestly reachable issuance state.

**Falsifiers:** for (1), one two-request result outside both sequential orders; for (2), a split/delete order mismatch or boundary insertion outcome outside the independent identity specification; for (3), a locally issued ordinary edit with the wrong visible effect, or a version with no legal witness satisfying both required orders.

**Formal oracle:** `Sal/MRDTs/Instances/NotionSplitSpec.lean`, checked with `lake env lean Sal/MRDTs/Instances/NotionSplitSpec.lean`.

**Reality oracle:** the separately fetched, hash-pinned published JavaScript demo and the literal traces in `experiments/notion-oracle/`. The Lean definitions below are independent specifications, not a translation or verification of that JavaScript.

## Checked fragment

The positional specification stores a list of blocks, each a list of characters. A split replaces the addressed original block by its prefix and suffix. A delete removes the requested range in that block, with clamping. The concrete theorem `no_positional_serialization` checks both orders of splitting `abcd` at 2 and deleting `[1,3)`. The resulting serial documents are `a | cd` and `ad | empty`; neither is the measured `a | d`. A strict bounds discipline would reject one or both orders and cannot restore a witness. This refutes this request-level replay contract. It does not refute an identity-addressed message specification or the framework.

The independent identity fragment stores ordered semantic character slots, each with an identity, value, and visibility. A deletion names character identities and hides their slots across all blocks. A split names the character immediately before its gap. Hidden slots remain available as gap anchors. These identities express an editing distinction: deleting the character before a prepared gap does not erase the gap. They are not transaction identifiers, replay keys, sorting labels, slice records, or a transaction log.

`splitByAnchor_erase_commute` proves for every document, anchor, and target list that identity deletion commutes with splitting the first block at that retained anchor. `identity_anchor_crossing_delete` checks `a | d` in both orders, including a negative control against `ad | empty`. `boundary_insert_orders` checks both boundary placements with opposite sequential orders: split then insertion gives `abX | cd`; insertion then split gives `ab | Xcd`. Its negative control proves these outcomes differ. This establishes that identity-dependent boundary placement alone is not a non-linearizability counterexample.

`cut_erase_commute` additionally checks the simpler retained-slot-index fragment. `local_delete_preparation_control` checks one hand-derived concrete range preparation. It is not a universal client-preparation theorem. Every concrete scenario has a negative control. The file uses no added axioms or admissions; reported dependencies are Lean's standard `propext` and `Quot.sound` where used.

## Exact boundary of the fragment

The identity fragment is executable but is not a complete specification of the published demo. It currently addresses the first block, uses a single left character as its gap anchor, and lacks insertion at the beginning, block identities, concurrent split ownership, slice restoration/duplication, block merges, movement, formatting, transaction atomicity, and message preparation. Missing-anchor behavior is totalized, so issuance must separately establish presence and uniqueness before any claim of ordinary editing legality. Insertions assume fresh semantic identities; this invariant has not been derived from an issuer.

No faithful demo MRDT adaptation is defined by this fragment. The generic transaction-storage shell below supplies convergence only. No Notion-specific editing representation invariant, replay-policy proof, sequential-history bridge, or end-to-end correctness certificate is claimed. The fragment's checked commutation theorem supplies a candidate local lemma, not the whole requested milestone.

## What the actual five-VC interface requires

The relevant current interface is `Sal/MRDTs/Paper1/ConcreteJoin.lean`, `Raw.MergeVCs`, not the historical 24-VC skill template. Its five fields are `merge_comm`, `init`, `causal_delta`, `local_redistribute`, and `shared`. They are guarded by a context-indexed representation, semantic support, and metadata closure. Instantiating them alone is insufficient.

`VCReplayConditions` in `ConcreteVCExecution.lean` additionally requires replay laws, unique representation, initial representation, finite event enumeration, canonical states, support, a `Raw.ReplaySupply`, and represented versions derived from issuance-certified executions. Replay supply must reconstruct both the semantic event past and the remainder after a jointly semantic-maximal and metadata-maximal event. One cannot assume this reconstruction from convergence of transaction-set union.

For an independent natural specification, `ScopedVCConditions` adds `ExecutionHistoryAdequacy`; the total alternative `VCConditions` adds `CommutationCompatibility` and `EventFoldHistorySound`. `ConcreteHistoryBridge.lean` preserves a single witness's event permutation, paper order, specification visibility, and accepted independent query history. A transaction-set carrier with `Either` updates can establish storage convergence while failing the compatibility condition: independent text operations can interfere even when insertion into the carrier commutes. Sorting transactions again inside the specification would conceal this gap.

The framework offers ordinary and recursive execution theorems (`executions` and `executionsV`). Applying either requires the corresponding issuance-established representation and history premises. The natural editing fragment currently has neither instance, so it covers neither execution theorem. The generic storage shell below has a separate, narrower scope. Recursive bases cannot be claimed merely because a union carrier ignores the supplied base.

## Status

The positional-request bridge is **refuted** by a kernel-checked finite counterexample. The identity split/delete law and the boundary insertion controls are **machine-checked** within the explicitly limited independent fragment. Agreement with the source is **measured** on the external traces, not proved. Complete local preparation and full sequential-history refinement remain **staged** pending the source model and reachable-state invariants. See `docs/notion-research.md` for the investigation's overall conclusion and source/oracle evidence.

## Reachable local formatting obstruction

`NotionFormattingCounterexample.lean` isolates the source's single-instance annotation interval rule on fixtures with no hidden characters or pre-existing marks. The source groups displayed selections by text-instance identity, then formats an interval in the instance's order from before the selected first character to after the selected last character. Display and instance order can diverge after block splits and merges.

The source audit reproduces a two-character trace: start with `ab`; concurrently split at 0 and 1; obtain `empty | b | a`; merge `a` into `b`; obtain `empty | ba`; request bold on all of `ba`. In the underlying instance order `ab`, before `b` equals after `a`, so the interval is empty. `two_character_reversal` kernel-checks this finite interval calculation and its inequality with ordinary formatting of both selected characters. `contiguous_selection_control` shows the rule works on a nearby contiguous selection and is not constantly empty. `noncontiguous_selection_overformats` checks the complementary `ac` fixture: spanning the instance-order interval also formats `b`, displayed in another block.

These theorems use hand-derived inputs and do not prove that the JavaScript generates the fixture or implements the modeled interval rule. The separately pinned executable traces and source audit provide that evidence. Together they identify an obstruction to simultaneously preserving the demo's measured behavior and proving ordinary exact-selection local formatting on all honestly reachable split/merge states. Five merge VCs cannot repair a failed local client effect. This does not settle the narrower split/insertion/deletion-only milestone.

The additional `local_split_zero` theorem states the independent ordinary split-at-zero rule for every text. `minimized_split_zero_rejects_ordinary_contract` checks the minimized target block `aX` against the observed `X | a`. The unchanged preceding empty block is outside this first-block fragment. Source reachability remains external evidence; this is a semantic counterpart, not a mechanization of the source execution.

## Generic transaction-storage shell

`NotionTransactionSet.lean` now instantiates the existing finite-store port with an arbitrary immutable transaction type. `fiveVCs` exposes the actual current `Raw.MergeVCs` bundle; `storageJoin` consumes its representation and replay-supply package; `same_events_render` derives equality for any deterministic renderer on two registered versions with the same event set. Its ordinary and canonical recursive-base specializations are checked. This reuses `SimpleConcretePorts.Finite.conditions`, whose represented execution states are constructed through `CommutingPort.automatedReplayConditions` and the five-VC induction.

The theorem is about storage convergence. Its renderer is an arbitrary parameter; it has no natural-text history or correctness contract. The issuance policy is unrestricted transaction insertion, not a verified translation of the demo's client. `adapter_union_agrees` checks equality with the runtime adapter's base-inclusive union when its accepted-input base-subset guard holds. It does not verify JavaScript parsing, object equality, or the guard implementation.

`Consistent`, `consistent_insert`, and `consistent_union` separately express the runtime adapter's key/payload discipline. The whole-value finite set can otherwise contain different payloads with one key. `identity_collision_control` checks individually consistent branches whose union conflicts. Deriving this property from fresh sessions and the actual issuer remains absent. These generic shell results establish neither a faithful Notion adaptation nor its independent sequential-history bridge.
