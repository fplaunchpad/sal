# Remaining changes to the Sal paper

**15 October update:** the [priority-ordered technical review](paper1-technical-issues.md)
records the current open issues and completed local corrections. The comparison
below retains its historical baseline.

Compared with Overleaf **`bd18900` (14 October 2026)** and checked Sal
`paper1` **`12886ba`**, including the natural-specification proofs in `706036c`.
Locations below refer to this manuscript snapshot; definition numbers refer
to the [formal reference PDF](paper1-formal-reference/main.pdf).
This is the concise author-facing correction list. The
[section-by-section writing review](paper-writing-review.md) expands it with
contribution, exposition and evaluation gaps. GC is excluded from this paper.

The latest revision adds the introduction, expands the VC3 explanation and
removes the undefined `Supported` premise in VC2. These are no longer missing.
The operation-inequality guard and version-local lifting premise remain, as
does the correct diagnosis of no-op removal as a specification-compatibility
failure. **Manuscript VC4 is causal-delta and VC5 is shared redistribution**,
now aligned with the reference after its 15 October numbering correction.
General label projection and the recursive-base proof remain absent from the
active text.

## Changes still needed

1. **Complete the policy-law change (`ralin.tex:31,155–199`).** The new
   inequality guard does not establish that equal operations commute. Add
   equal-operation self-commutation on the same eligible event/state domain.
   Keep `rc` on operation payloads, but state the commutation obligations on
   their particular events. The raw contract guards distinct timestamps and
   different replicas; certified contracts retain supported concurrent events
   and represented-ready or invariant states. Unrestricted same-replica
   self-commutation would exclude efficient OR-set. Preserve no-chain and
   conditional commutation with their own stated guards.
   **Reference:** Definitions 4.5 and 4.8.

2. **Restore general labels and event-specific compatibility
   (`ralin.tex:138–153,177–181,220–239`).** Restore `f : Events → U` and
   `ops_f`; payload-only `ops` suffices for the ordinary OR-set but loses
   identities needed by other specifications. State
   `not SpecCommutes(f(a),f(b)) → not ImplCommutes(a,b)` for the actual events.
   Payload noncommutation only says that *some* metadata pair fails to commute.
   To match the reference criterion directly, require the witness to preserve
   specification-conflicting visibility, with compatibility as a sufficient
   way to obtain it. If the paper keeps `Laws` inside its RA definition,
   explicitly carry that assumption into the lifting theorem.
   **Reference:** Definitions 4.4–4.6; §6, equation (2).

3. **Make canonicality cover the induction's sets
   (`ralin.tex:49,250–275`; `proof_strategy.tex:61–89,136–162,271–317`).**
   The order and canonical-state definitions still require causal closure,
   while the VCs and Join lemma use weakly closed sets and peeled downsets.
   State finiteness and prove existence and uniqueness on that wider domain.
   In `Admissible`, replace the unbound `E` by `E_i`. VC2 now states support
   directly, but the canonical states in every VC still need the appropriate
   closure domain. This is the global canonical route; the certified extension
   below needs its own scope.
   **Reference:** §4, “Canonical States and Certified Replay”; §5.

4. **Require simulation transitions to exist (`seq_spec.tex:87–123`).**
   Conditions (ii) and (iii) are vacuous when the specification has no matching
   transition. Require matching update and query transitions directly, or
   state total deterministic updates and state-preserving queries. Quantify
   the complete event, including `t,r`, and use `f(e)`. The new lifting premise
   at lines 61–69 is sufficient for a chosen canonical witness; it need not be
   strengthened back to all event lists. The reference's Theorem 6.2 uses that
   stronger total premise, so it is not a verbatim match. At line 82, invoke
   the theorem's premise rather than the theorem being proved.
   **Reference:** Theorem 6.2 and its simulation assumptions; §6.2 for guarded histories.

5. **Add the certified extension (§3–6 and `rga.tex`).** State original
   issuance evidence, justified invariants, represented states and the separate
   sequential-history bridge. The general five-VC proof also needs explicit
   reconstruction dependencies and replay supply: commuting predecessors can
   still carry required anchor metadata. Its last-event choice must preserve
   both semantic order and metadata closure. These obligations support the
   same five merge equations; they are not supplied by acyclicity alone.
   Do not claim arbitrary-permutation uniqueness for every certified RDT.
   `rga.tex` is still only a heading and is not included by `main.tex`. Choose
   the implementation explicitly: Embedded RGA is not native tombstoned RGA.
   Include both the five-VC connection and the independent history bridge;
   local positional preparation alone is not the global correctness result.
   **Reference:** Definitions 4.7–4.8 and 5.1–5.4; Theorem 5.5; §6.2.

6. **Restore a precise recursive-base statement (`opsem.tex:118–122`;
   `proof_strategy.tex:519–527`).** The operational discussion still promises
   recursive merging, but the proof now only handles an allocated common
   ancestor. A recursive computation produces a *base state*, not necessarily
   an allocated “actual LCA”. Define its fold/resolver and justify its
   decreasing ancestry support, or explicitly restrict the theorem's scope.
   **Reference:** Definition 3.4 and Theorem 5.7.

7. **Fill implementation/evaluation with the actual coverage.** Report
   the 19 retained automation proof configurations separately from distinct
   ADTs and runtime packages. FugueMax now has a complete natural-origin
   history certificate through the five VCs, including recursive executions;
   only its former live-parent specification remains refuted. The earlier
   “20 positive results plus Fugue obstruction” summary is obsolete. The new
   Fugue bridge is not measured in the historical effort tables. Report
   [VC and bridge effort separately](../experiments/vc-automation/README.md),
   correcting that report's stale Fugue status before quoting it. The published
   bounded counter and two source flags have checked certificates outside
   the measured automation corpus. Do not sum these counts as distinct ADTs.
   The active ordinary Counter now supports unrestricted increment/decrement;
   the two increment-only duplicates have been removed. Use one Counter row
   and keep the bounded escrow counter separate. This does not relabel
   historical measurements.
   The published **Balegas et al., SRDS 2015, §III-B/Figure 1** design now has
   a checked five-VC and independent history bridge for ordinary and recursive
   merges. It uses a sender–recipient matrix `R`, decrement vector `U`,
   increment/decrement/transfer operations, and componentwise-max merge.
   Its proof retains the single-writer discipline: each replica writes only
   its row of `R` and entry of `U`; reconstruction retains those causal
   predecessors even though the additive operation effects commute.
   State the fixed replica universe, nonnegative amounts, valid issuer and
   recipient, nonself transfers, and sufficient source rights for decrement
   and transfer. The independent specification stores a scalar counter and
   per-replica balances; transfers preserve the scalar value, and conservation
   with nonnegative balances gives the lower bound. Distinguish the client
   counter query from the separate local-rights query. The existing
   published matrix/max design is the sole active bounded counter; the earlier
   independent-account and additive-budget experiments have been removed.
   [Published paper](https://asc.di.fct.unl.pt/~nmp/pubs/srds-2015.pdf) and
   [technical report, §III](https://asc.di.fct.unl.pt/~nmp/pubs/tr-corr-1-2015.pdf)
   are the authority; the Bismuth experimental implementation is not.
   Neem’s corrected enable-wins and disable-wins flags now also have five-VC
   and independent Boolean-history proofs for ordinary and recursive executions.
   Include them in implementation coverage; their queries are explicit additions
   to the F* source API. See Example 6.8 for both equations and policies.

   **Reference:** Example 6.7, “Published bounded counter”.

8. **Correct and complete the contribution claims
   (`introduction.tex:76–132`; abstract and closing sections).** Attribute
   concrete convergence to the canonical/represented-state theorem and its
   hypotheses, not to observational RA admission alone. Scope “all valid
   linearizations” to the raw replay theorem; certified results use their own
   domains. Say that the merge proof avoids assembling a witness from the
   chosen branch sequences, not that no history is ever constructed. Add the
   certified extension, Lean mechanization, shared independent specifications,
   and evaluated automation/coverage to the contribution list. The abstract,
   implementation, evaluation, related work and conclusion still need text.
   **Reference:** §4 canonical/replay results, §5 sufficient conditions and
   §6 sequential bridges; the [writing review](paper-writing-review.md)
   identifies the supporting artifacts and evaluation qualifications.

Small mathematical fixes: `proof_strategy.tex:49` should say that every
*other* downset member precedes the event in a respecting linear extension,
not that every member is directly related by `lo_E`. In `ralin.tex:296`, the
second list should contain `A_p`, not two copies of `A_q`. Use “all stored
versions” for `dom(S)` and distinguish replica heads (`ralin.tex:226,245`).
`opsem.tex:61,87` should union the event-set components of stored pairs.
Keep concrete implementation equality and the specification refinement function
`α`; no implementation-state observational quotient is required.

## Reference artifacts

The [natural-specification audit](natural-sequential-specifications.md)
separates positional/value-only client requests from generated replication
messages. Simple sets and counters now use set/integer sequential states with
checked equality of their complete former history languages. Queue has a
checked local enqueue/dequeue preparation theorem alongside its existing
concurrent named-head history theorem. FugueMax now has both the actual
physical positional refinement and the complete natural origin-list RA bridge
through the five VCs, for ordinary and recursive executions. Its sequential
language retains stable identities and deleted origins, but no coordinate
chains or structural parents. Native RGA now enforces the paper's reserved-zero
convention in both issuance and its identified sequential language. The reference’s
“Positional request preparation” paragraph states the checked local update
correspondence for native, Embedded and Sided RGA. Execution supplies the
freshness and representation invariants; the client supplies a position.

- [Formal reference PDF](paper1-formal-reference/main.pdf): checked split laws
  and certified results. Its manuscript correspondence appendix still targets
  `0450d48`; the updated lifting premise and VC numbering above supersede that map.
- [Interactive datatype reference](https://sal-datatype-reference.fizzyearth10.chatgpt.site/):
  implementation/specification equations and issuance guards. Its sole bounded
  counter entry is the published matrix/max design with its checked bridge.
- [Earlier manuscript patch](paper1-manuscript-reconciliation.patch): targets
  `0450d48`; do not apply it wholesale to the current manuscript.
