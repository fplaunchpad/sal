# Changes to the Sal paper

Compared against **Overleaf `0450d48`**, fetched again on 8 October 2026.
The live Overleaf source is unchanged. The Lean work is on `paper1`.

The paper should organize correctness around **two obligations**:

1. **Implementation correctness:** replay laws, five merge VCs and the required
   representation/issuance invariants establish correct stored states.
2. **Sequential-specification bridge:** one history explains the stored answer
   in the independent specification and respects the required orders.

**Both OR-set and Embedded RGA use the five-VC proof.** OR-set discharges the
second obligation by total sequential simulation. Embedded RGA constructs an
insertion-first history and proves its exact reconstruction and admission.
That history proof supplements the VCs; it does not replace them.

## Required revisions

- **§3, `opsem.tex`:** make causal timestamp monotonicity, fresh-child fork,
  greatest common ancestors and original issuance evidence explicit. Treat
  recursive virtual bases as an extension. These are premises of the execution
  proof. **Reference:** Definitions 3.1–3.2, 3.4; Theorem 3.3.
- **§4, `ralin.tex`:** define an explicit commutation domain and label
  projection, and require the same witness to preserve specification-conflicting
  visibility. The old definition admits the broken no-op removal example.
  **Reference:** Definitions 4.1–4.6; Example 6.1.
- **§4, replay laws and canonical states:** state the event guards precisely.
  Keep global public-order uniqueness separate from scoped uniqueness for legal
  causal replays. The latter does not justify arbitrary public-order witnesses.
  **Reference:** Definitions 4.5, 4.7–4.8; Theorem 4.9.
- **§5, `proof_strategy.tex`:** expose representation, uniqueness, finite replay
  supply and metadata reconstruction alongside the five equations. These are
  instantiated obligations, not an assumed Join result. Distinguish the exact
  OR-set's weak-closure Join from the represented certified extension.
  **Reference:** Definitions 5.1–5.4; Theorems 5.5, 5.7.
- **§6, `seq_spec.tex`:** state totality/determinism for the simulation method
  and specification-commutation compatibility for the strengthened criterion.
  Add the certified exact-history bridge without a universal uniqueness claim.
  **Reference:** Theorem 6.2, equation (2), and the scoped discussion after 6.4;
  the patch gives the exact-history theorem explicitly.
- **RGA case study:** the existing `rga.tex` is an unused heading naming
  tombstoned RGA. The patch adds an explicitly named **Embedded RGA** case,
  with the same five-VC chain and its separate history bridge. It includes the
  actual issuer and the independent specification's absent-anchor behavior.
- **§2, `motivation.tex`:** include the distinguishing read in the efficient-set
  example and distinguish per-version histories from a single global history.
  The update-only word currently displayed does not itself witness rejection.

Keep concrete implementation equality and the specification-refinement
function `α`. No implementation-state semantic abstraction is needed.

## Review artifacts

- [Formal reference PDF](paper1-formal-reference/main.pdf): definitions in the
  paper's notation; reference numbers above refer to this PDF.
- [Exact manuscript patch](paper1-manuscript-reconciliation.patch): replacements
  for seven source files, preserving the worked OR-set example and figures.
  It applies to `0450d48`; review it in a separate checkout before importing it
  into Overleaf. The combined proposed source compiles.
- [Correctness audit](paper1-correctness-audit.md): assumptions, conclusions,
  proof dependencies and the claim-by-claim evidence.

The revised theorem connections are machine-checked: unrestricted raw ordinary
and virtual payload correctness for the exact OR-set, and certified full-event
invariant-order correctness for Embedded RGA. The audit does not establish the
broader claim that every public-order RGA permutation has the same fold.
