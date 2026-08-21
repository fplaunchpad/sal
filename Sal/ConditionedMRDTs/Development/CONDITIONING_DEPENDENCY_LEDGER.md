# Conditioning dependency ledger

This ledger records which conditions the production theorems actually use.
It supports Priority 7A and the paper's Neem-first argument. Read theorem
statements and proof bodies as authoritative; do not infer a dependency from a
field name or catalogue row.

## Research question

- **Goal:** Identify the smallest conditioning interface that preserves the
  corrected MRDT, safety, and sequential-intent results used by Peritext.
- **Candidate claim:** Successful production instances need flat MRDT algebra,
  a causal generation contract, a separate safety policy, and a local
  sequential mint policy. They do not currently need signature-level
  `Inv`/`applicable` to rescue a false algebraic VC.
- **Falsifier:** A positive production capstone whose Join/RA proof fails after
  replacing signature `Inv`/`applicable` by `True`, even when its existing
  generation history is supplied.
- **Formal oracle:** Public declarations listed below, the
  `GenerationVerifiedMRDT` compatibility adapter, and the production ledger.
- **Reality oracle:** The JavaScript issuer API and persisted replica state.
  Lean does not establish that the handwritten runtime enforces its guard or
  Lamport-clock premises.

## Dependency matrix

`T` means definitionally trivial. `LB` means load-bearing in the cited proof.
`E` means an external premise not yet derived by the public certificate.

| Canary | Signature `Inv` | Signature `applicable` | Generation guard/history | Safety | Sequential intent |
|---|---|---|---|---|---|
| EmbedRGA | T | T | **LB:** `eApplicable -> EHonest -> EHonestCore -> e_join_kit_at` | T | **LB:** `eSeqOK`; guard alone is insufficient; `LinearMintHistory` now derives it |
| SidedEmbedRGA | T | T | **LB:** `sApplicable -> SHonest -> SHonestCore -> s_join_at` | T | **LB:** `sSeqOK`; `LinearMintHistory` now derives it. Fugue/FugueMax side policy is separate |
| canonical Embed-Peritext | T | T | **LB:** inherits EmbedRGA generation and Join at `PeritextElt` | T in unified certificate; GC/mark theorems carry separate conditions | **LB:** `eSeqOK` for `peritextEmbed_seq_sound`; local bridge inherited from EmbedRGA |
| mergeable queue | T | T | **LB:** `qApplicable -> QHonest -> QHonestCore -> q_join_at` | T | **LB:** `qOK` requires fresh enqueue tags and dequeue-at-head; `qOK_of_linearMintHistory` now derives it |
| bounded counter | T in production `BC`; nontrivial only in auxiliary `BCCond` | T in `BC`; `bcApplicable` in `BCCond` | Not needed for Join/RA; **LB for safety:** mint evidence gives `BCHonest` | **LB:** `BCHonest -> bc_version_inv -> BCInv/value >= 0` | **LB:** `BCSequentialHonest`; `BCSequentialHonest_of_linearMintHistory` now derives every prefix invariant |

## Findings

1. **The corrected Neem replacement remains foundational.** `VerifiedMRDT`
   packages the Join-based RA proof that replaced the failed bottom-up
   linearization route. Consolidating conditioning must preserve that proof;
   it does not replace it.
2. **Generation history is load-bearing for three Join proofs.** EmbedRGA,
   SidedEmbedRGA, and queue use datatype-specific history derived from local
   issuer checks. Their signature-level fields remain `True`.
3. **The bounded counter uses conditioning for safety, not convergence.** Its
   Join theorem is unconditional. `bcApplicable` and `BCHonest` establish the
   no-overdraft invariant at every registered version.
4. **Sequential intent is a local theorem.** A concurrent configuration need
   not admit one globally applicable operation list. The public package must
   not equate distributed RA correctness with one global sequential replay.
5. **The clock premise was missing from the generation interface.** The
   checked theorem `applicable_mints_do_not_imply_eSeqOK` refutes guard-only
   sequential intent. `LinearMintHistory` supplies the missing local Lamport
   discipline; the Embed and Sided bridges are machine checked.
6. **No positive production instance currently validates the strongest
   signature-conditioning claim.** Rehoming RGA and Shesha use genuine
   algebraic conditioning but are refuted designs. `BCCond` is positive, but
   its nontrivial fields support safety rather than an otherwise-false Join or
   commutation VC.

## Candidate interface status

`MRDT_Instances/ConsolidatedConditioningCanaries.lean` defines the staged
`GenerationVerifiedMRDT` package. It keeps:

- `AlgebraVerifiedMRDT`, which contains the corrected Join and sequential
  certificates but no `Inv` or `applicable` field;
- `OperationalConditioning`, which isolates the legacy configuration's
  initial invariant witness;
- `GenerationContract` and its history-to-Join bridge;
- `SafetyCertificate`; and
- a new `sequential_of_mint` bridge from `LinearMintHistory`.

`GenerationVerifiedMRDT.toUnified` is lossless. The checked split/rebuild
round trip reconstructs the original `VerifiedMRDT`. EmbedRGA,
SidedEmbedRGA, and canonical Peritext inhabit the candidate package and recover
the established distributed RA and safety theorems. This result validates the
organization and the public dependency boundary. It does not yet remove
`ConditionedMRDTSig` from the legacy operational semantics.

## Remaining gates

1. Allocate unique persistent mint slots at the deployment boundary. The
   runtime allocator, causal observation, recovery, and post-GC controls pass.
2. Update the stable external claim manifest. `PeritextFlagshipCertificate`
   now composes distributed correctness, local intent, compressed commit GC,
   asynchronous distributed-GC refinement, and state-GC render preservation.

## Conditioning boundary decision

Use `AlgebraVerifiedMRDT` as the paper-facing algebra and sequential-intent
layer. It contains no `Inv` or `applicable` field. Use `GenerationContract` and
`LinearMintHistory` for issuer policy and causal mint evidence. Keep client
safety in `SafetyCertificate`.

Treat signature-level state conditioning as an operational compatibility
extension. The current `Configuration` type stores `D.Inv` proofs, so
`OperationalConditioning` still supplies `initInv` when the new certificate is
adapted to `VerifiedMRDT`. This is not evidence that `Inv` or `applicable` makes
a production Join law true. The round-trip control proves that splitting and
rebuilding the old package loses no theorem data; the boundary control shows
that algebra alone does not manufacture an invariant witness.
