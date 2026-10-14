# Independent review of the Notion research increment

Review scope: the pinned-source audit, independent JavaScript command/request machines, experimental transaction-set adapter, deterministic regressions, generators/minimizer, the Lean specification files, and the generic `NotionTransactionSet.lean` storage shell. This review does not establish source equivalence or a document-history refinement.

## Findings

1. **Resolved: minimizer guarantee.** The reviewed revision repeats request removal after seed-text shrinking. `oneMinimal: true` now refers to the final seed under the stated one-request-removal procedure; it still does not claim global minimality.
2. **Resolved: interval projection comment.** `NotionFormattingCounterexample.lean` now explicitly projects the complete RGA traversal onto text characters, removing split markers before the restricted interval calculation.
3. **The retained-slot JavaScript machine needs its own scope recorded.** `IdentityDocument` supports block identities, beginning anchors, and split-boundary slots that the smaller Lean fragment does not. Passing `identity-check.mjs` is differential evidence for this JavaScript machine, not evidence that the Lean definitions implement all its cases. Existing prose distinguishes formal limitations, and the final report should preserve that distinction.
4. **Adapter agreement intentionally shares observation code.** `TransactionSet.issue` delegates to `Replica`; its observation delegates to the same `CrdtDocument` as the source oracle. Adapter-versus-source equality therefore tests storage and issuance plumbing, not independent document-semantics refinement. The adapter comments and systematic-suite summary disclose this. Do not promote this agreement to a separate semantics validation result.

## Validity checks

The two-character formatting failure is honestly reachable through public issuance: seed `ab`; concurrent A split at zero and B split at one; deliver both; merge A's suffix block into its preceding B block; request bold over the resulting `ba`. The generated annotation has equal before-`b` anchors and leaves both selected characters unbold. I independently reproduced this against all seven hash-checked modules before reviewing the checked-in regression. The three-character `ac | b` overformatting case is independently reproduced too.

The local split regression uses distinct transaction identities for duplicate-intent merges. It does not rely on forged low-level messages or replaying an identical transaction as a fresh edit. The regression asserts its pre-edit fixture and uses a separate ordinary split function for the expected result. This is a valid local request-effect counterexample, irrespective of later RA history choices. The revised Lean split counterpart checks the minimized target text `aX` against observed `X | a`, omitting the unchanged preceding empty block. It does not mechanize source reachability.

The independent machines do not import the demo interpreter. `regressions.mjs` obtains a source pre-state and then applies a separately defined ordinary local request; this is a valid one-step differential oracle, not a self-oracle. Hand-derived pre-state and actual-output assertions pin the critical fixtures. `identity-check.mjs` keeps ascending-ID witness selection outside `IdentityDocument`. Its generated commands still require independent decoder and issuance-invariant justification before a universal refinement claim.

I reran `identity-check.mjs` with the separately fetched pinned modules: 4,500 comparisons, three declared seeds, 50 trials per seed, six rounds, zero discards, pass. I reran `regressions.mjs`: all four deterministic rows completed successfully, including the two expected formatting failures, a positive formatting control, and the expected local split failure. Success here means the known failures reproduce; it does not mean the ordinary editing contract holds.

## Storage theorem and conclusion review

`NotionTransactionSet.lean` reuses `SimplePorts.Finite.conditions`, whose replay conditions come from `CommutingPort.automatedReplayConditions`, together with the finite-store compatibility and history soundness proofs. Its `fiveVCs` theorem has the actual `Raw.MergeVCs` type; `storageJoin` consumes the representation/replay package. `same_events_render` derives equality for any deterministic renderer from certified equal-event-set storage convergence. The ordinary and canonical recursive-base theorems specialize that statement. This is a real existing five-VC chain applied to generic whole-value set storage; no natural text specification appears in those theorem conclusions.

The key-consistency lemmas correctly require cross-branch payload agreement. Individual branch consistency alone is insufficient, as the positive/negative collision control demonstrates. The JavaScript adapter's base-subset guard and identity-key rejection are additional issuance/acceptance obligations; the generic finite set does not derive them. The conditional `adapter_union_agrees` correctly uses the base-subset premise only for the algebraic union equality.

`docs/notion-research.md` accurately separates the refuted unrestricted local split/formatting contract, open split/insert/delete-only milestone, measured slot-machine gate, and storage-only theorem. Its negative conclusion is supported by local counterexamples and does not require proving the missing sequential-history bridge. The stated lack of production correspondence is appropriate.

No reviewed artifact proves the full split/insert/delete milestone or a Notion document sequential-history bridge. Generic storage convergence covers ordinary and canonical recursive bases; document-history correctness for either remains open. The source findings do not justify production claims.
