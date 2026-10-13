# Remaining changes to the Sal paper

Compared with Overleaf **`179d763` (13 October 2026)** and the checked
`paper1` development at `8680ec3`. Locations below refer to this manuscript
snapshot; definition numbers refer to the [formal reference PDF](paper1-formal-reference/main.pdf).

The latest revision adds the operation-inequality guard to `rc-non-comm`,
restricts the lifting premise to linear extensions of stored event sets, and
correctly says the no-op-remove example violates specification compatibility.
The five canonical merge equations remain; **VC4 is now causal-delta and VC5
is shared redistribution**, opposite to the reference's numbering. Compare
these by name. General label projection and the recursive-base proof paragraph
have been removed from the active text.

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
   In `Admissible`, replace the unbound `E` by `E_i`; define the still-used
   `Supported` predicate or remove its redundant use in VC2. This is the
   global canonical route; the certified extension below needs its own scope.
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
   **Reference:** Definitions 4.7–4.8 and 5.1–5.4; Theorem 5.5; §6.2.

6. **Restore a precise recursive-base statement (`opsem.tex:118–122`;
   `proof_strategy.tex:519–527`).** The operational discussion still promises
   recursive merging, but the proof now only handles an allocated common
   ancestor. A recursive computation produces a *base state*, not necessarily
   an allocated “actual LCA”. Define its fold/resolver and justify its
   decreasing ancestry support, or explicitly restrict the theorem's scope.
   **Reference:** Definition 3.4 and Theorem 5.7.

7. **Fill implementation/evaluation with the actual coverage.** Report
   23 named five-VC cases, including aliases and anchored Queue, with 22 positive
   history results and Fugue's checked specification obstruction. Report
   [VC and bridge effort separately](../experiments/vc-automation/README.md).
   The existing `BoundedCounter` is independent nonnegative replica accounts.
   The additional transferable-budget candidate has completed five-VC, history
   and budget proofs, but implements a different design from the published
   bounded counter. Use **Balegas et al., SRDS 2015, §III-B/Figure 1** as the
   design source: a sender–recipient transfer matrix, increment/decrement and
   transfer operations, and componentwise-max merge. Our candidate instead has
   aggregate accounting, additive three-way merge and no increment operation.
   Port and verify the published design before claiming that coverage; the
   Bismuth experimental implementation is not the authority.
   [Published paper](https://asc.di.fct.unl.pt/~nmp/pubs/srds-2015.pdf).
   **Reference:** Example 6.7 documents only the existing alternative candidate.

Small mathematical fixes: `proof_strategy.tex:49` should say that every
*other* downset member precedes the event in a respecting linear extension,
not that every member is directly related by `lo_E`. In `ralin.tex:296`, the
second list should contain `A_p`, not two copies of `A_q`. Use “all stored
versions” for `dom(S)` and distinguish replica heads (`ralin.tex:226,245`).
`opsem.tex:61,87` should union the event-set components of stored pairs.
Keep concrete implementation equality and the specification refinement function
`α`; no implementation-state observational quotient is required.

## Reference artifacts

- [Formal reference PDF](paper1-formal-reference/main.pdf): checked split laws
  and certified results. Its manuscript correspondence appendix still targets
  `0450d48`; the updated lifting premise and VC numbering above supersede that map.
- [Interactive datatype reference](https://sal-datatype-reference.fizzyearth10.chatgpt.site/):
  implementation/specification equations and issuance guards. The transferable
  candidate entry describes the alternative already proved, not the published algorithm.
- [Earlier manuscript patch](paper1-manuscript-reconciliation.patch): targets
  `0450d48`; do not apply it wholesale to the current manuscript.
