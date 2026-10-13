# Remaining changes to the Sal paper

Compared with Overleaf **`d3ad6ff` (13 October 2026)**, fetched and
fast-forwarded into `sal_paper`. The comparison uses the retained `paper1`
formalism, with Kartik's agreed split presentation: operation-distinct
`rc-non-comm` and separate equal-operation self-commutation. The production split interfaces in `SplitPolicy.lean` preserve the same
event and state domains and have checked adapters to the existing laws.

The latest paper already adds fresh-child forks, causal timestamp growth,
a greatest-common-ancestor definition, discussion of recursive bases, label
projection, specification commutation, and the distinguishing `readIds` answer
in the efficient OR-set example. These no longer need to be requested as new
additions. The five canonical VC equations match the retained canonical proof
route; they do not need replacing with the certified route's guarded equations.

## Changes still needed

1. **§4, commutation and replay laws (`ralin.tex:31,157–199`): use
   Kartik's split on eligible event pairs.** Keep `rc` on operation payloads. Reserve the term event replay order for the
   separate generic `EventOrder` interface; it is not an alternative definition
   of the paper’s `rc`.
   State `rc-non-comm` for unequal payloads, and state self-commutation
   separately for equal payloads. Both use the same event and state domain.
   The raw route retains distinct timestamps and different replicas; the
   certified route uses supported concurrent events and its specified invariant
   or represented-prefix domain. In supported configurations concurrency and
   distinctness supply the metadata guards. Do not universally lift
   self-commutation to all metadata pairs and all states: repeated local adds
   in efficient OR-set refute that claim. Preserve no-chain and conditional
   commutation. **Formal reference:** Definitions 4.5 and 4.8.

2. **§4, specification compatibility and RA definition
   (`ralin.tex:177–239`): apply the projection to the particular events.** Write
   `not SpecCommutes(f(a),f(b)) → not ImplCommutes(a,b)`; specification labels
   range over `U`, and the general witness uses `ops_f`, not OR-set-specific
   `ops`. Payload noncommutation says only that some metadata pair fails to
   commute; the order tests the actual event pair. For a one-to-one match with
   the reference, keep replay laws and compatibility as sufficient proof
   assumptions, and require the witness to preserve specification-conflicting
   visibility. The current definition instead makes all four laws prerequisites
   to the criterion; if retained, its lifting theorem must explicitly assume
   them. **Formal reference:** Definitions 4.4–4.6; §6, equation (2).

3. **§4–5, canonical-state domain (`ralin.tex:250–281`, VC3–VC5 in
   `proof_strategy.tex:133–214`): cover the sets used by the induction.**
   Determinacy and `can(E)` currently cover causally closed sets, but the VCs
   use peeled sets and noncommuting downsets that need only be weakly closed.
   State finiteness and establish canonicality on that wider domain. Keep
   this global result separate from the certified result comparing only legal
   causal replays. **Formal reference:** §4, “Canonical States and Certified
   Replay”; §5, canonical and represented Join routes.

4. **§6, simulation (`seq_spec.tex:90–114`): require matching transitions to
   exist.** The current implications are vacuous if the abstract machine has
   no update or query transition. Either state total deterministic updates and
   total state-preserving queries, or require existence of the matching
   transitions directly. Use `f(e)` in the general simulation. Also replace
   “the state it reaches” in `ralin.tex:138` unless determinism is assumed.
   The universal premise of `thm:lift` itself is appropriate for the total
   bridge. **Formal reference:** Theorem 6.2 and its simulation assumptions.

5. **§3–6 and the RGA case study: add the certified extension explicitly.**
   The current presentation covers the stronger all-state, all-replay route.
   To cover the certified RDTs, define the justified state domain, original
   issuance evidence, represented states and reconstruction/replay supply,
   then state correctness for certified executions. Give the separate history
   argument tying the specification witness to the stored answer. For Embedded
   RGA this supplements the same five-VC proof; it is not another merge proof.
   Do not extend arbitrary-permutation uniqueness to these scoped results.
   **Formal reference:** Definitions 3.4, 4.1, 4.7–4.8, 5.1–5.4; §6.2.

6. **§3, recursive bases (`opsem.tex:118–122`; `proof_strategy.tex:427–431`):
   distinguish a computed base state from an allocated ancestor version.**
   Recursive merging does not create an “actual LCA” that the ordinary merge
   rule can look up. Add a resolver or virtual-merge rule; specify the fixed
   fold order and decreasing ancestry-support argument. The required result
   covers both intersection events and the computed canonical state.
   **Formal reference:** Definition 3.2, Theorem 3.3, Theorem 5.7.

7. **Implementation/evaluation sections: describe the automation and the
   separate bridge cost.** Both sections are still headings. Explain how finite
   template obligations imply the five VCs, what datatype-specific evidence is
   supplied, and which sequential bridges are proved. Use the current
   [automation results](../experiments/vc-automation/README.md); do not infer a
   sequential bridge from VC discharge. In particular, retain the documented
   Fugue sequential-specification obstruction. Distinguish the 23 named five-VC
   cases (including aliases and the anchored Queue) from the older 22-package
   registry. The current “bounded counter” is independent nonnegative replica
   accounts; it does not yet establish coverage of the intended transferable
   counter. A corrected transferable-counter candidate now has separate five-VC,
   sequential-history and global-capacity proofs (formal reference,
   “Transferable-budget candidate”). Its correspondence with the intended paper
   datatype remains unresolved; do not count it as manuscript coverage yet.

Small consistency fixes: `opsem.tex:61,87` should take the union of event-set
components of `S(v)`, since `range(S)` contains state/event-set pairs. The RA
criterion quantifies over all allocated versions (`dom(S)`), while the lifting
explanation switches to heads (`seq_spec.tex:70`); use the intended scope
consistently. Keep concrete implementation equality and the specification
refinement function `α`; no implementation-state observational quotient is
needed.

## Reference artifacts

- [Interactive datatype reference](https://sal-datatype-reference.fizzyearth10.chatgpt.site/):
  implementation and sequential equations, issuance guards and checked coverage.

- [Formal reference PDF](paper1-formal-reference/main.pdf): numbered definitions
  cited above. The replay laws now use the agreed split formulation. The other manuscript
  mappings remain based on `0450d48`; this is not a full rewrite for `d3ad6ff`.
- [Earlier manuscript patch](paper1-manuscript-reconciliation.patch): applies
  to `0450d48`, **not** the newly fetched manuscript. Do not apply it wholesale;
  several changes are now present or have been rewritten by the authors.
- [Correctness audit](paper1-correctness-audit.md): supporting theorem scopes
  and dependencies; use this note for the current manuscript revision list.
