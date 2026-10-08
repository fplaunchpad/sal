# Changes to the Sal paper

This note is for revising the paper, not navigating the Lean development.
It compares the **Overleaf snapshot `0450d48` (8 October 2026)** with the
completed metatheory. Section and definition numbers below are from the
18-page PDF rebuilt from that snapshot; source line numbers refer to its `.tex`
files. The earlier GitHub manuscript is no longer the comparison baseline.

The accompanying **[formal reference PDF](paper1-formal-reference/main.pdf)**
follows the paper’s Sections 3–6, notation and terminology. It gives
self-contained replacement definitions and theorem statements; its main text
requires no Lean knowledge. Appendix A maps manuscript statements to reference
statements, and Appendix B maps those statements to Lean declarations.
**Reference numbers below refer to this rewritten PDF**, not the paper. The metatheory is complete under the assumptions stated there.
The work below aligns the manuscript with those assumptions and conclusions.

## Latest Overleaf update: motivation

The latest update changes only `motivation.tex`; all seven formal changes below
remain outstanding, and their source locations and reference numbers still apply.
The formal reference has been rewritten around those formal sections. A new
direct Lean lifting lemma matches the paper’s witness-based argument without
requiring replay laws again at the lifting step; existing semantics and
implementation guarantees are unchanged.

In §2.3, “The specification changes with the implementation”
(`motivation.tex`, lines 227–252), make the observation witnessing the mismatch
explicit. Under the displayed transitions, the update-only word
`add(a,k1); add(a,k2); rem({(a,k2)})` is legal: it leaves `(a,k1)` behind.
To demonstrate rejection, include either the preceding
`readIds(a) => {(a,k2)}` (the specification would return both tags), or the
following `rd_a => false` (the specification would return true). Write the
removal argument as a singleton set, consistently with `rem(S)`.
This is a check of the transitions displayed in the manuscript, not a new claim
about the cited work's full formalism.

In the following global-order example (`motivation.tex`, lines 346–378),
complete the unfinished sentence at line 371 and state the distinction precisely:
individual versions have explaining histories, but no single global history has
projections explaining all versions. Avoid saying simply that no linearization
exists.

## 1. Make specification visibility part of RA-linearizability

**Where:** §4.1, Definition 4.4 (`ralin.tex`, lines 153–175), and §6's
“A convergent implementation which is not a set” (`seq_spec.tex`, lines 29–45).

**Change:** Require the *same* explaining history to respect visibility between
updates that do not commute in the sequential specification, as well as the
implementation's linearization order. Define specification commutation by
whether adjacent swaps preserve admitted histories in all surrounding contexts.

**Why:** In the broken set, implementation add and no-op remove commute.
The current definition therefore allows `[remove, add]`, explaining a `true`
query after the actual execution `[add, remove]`. The example currently refutes
the sufficient sequential-simulation premise, not Definition 4.4. The new
visibility clause retains add-before-remove and rejects the wrong answer.

**Reference:** Definitions **4.4** and **4.6**, Example **6.1**.

## 2. Make the specification's update labels a datatype choice

**Where:** §4.1, Definition 4.3 and the operation-projection paragraph immediately
after it (`ralin.tex`, lines 88–121).

**Change:** Replace mandatory erasure of timestamps and replica IDs with an
explicit mapping from events to specification labels. The ordinary-set
specification can still receive only `add(a)` and `remove(a)`. Identified RGA
and anchored Queue specifications retain the original identity inputs.

**Why:** Inserting, anchoring and deleting must refer to the same identities.
Reallocating IDs during sequential replay can change both ordering and targets.
This does not require the specification to copy the implementation's state.
Keep the specification as a prefix-closed history language; use a unique
“state reached by a history” only when assuming a deterministic machine.

**Reference:** Definition **4.4**, Example **6.5**.

## 3. Distinguish operation policies from event-level replay laws

**Where:** §4.1, the three displayed replay laws and “used here unchanged”
paragraph (`ralin.tex`, lines 123–152).

**Change:** The user supplies `rc` between operation payloads. Its event-level
noncommutation law applies with distinct timestamps and different replicas.
State the distinctness guards for conditional commutation too, retaining actual
noncommutation with the absorber. Keep no-chain explicit. Distinguish these
global sufficient laws from the certified scoped laws used below.

**Why:** Effects receive event metadata even though the policy sees payloads.
An unguarded law asks about pairs that the proof does not need to compare and
can exclude correct implementations, including efficient OR-set. Policy
conflict cannot replace actual noncommutation outside the exactness guard.

**Reference:** Definitions **4.1**, **4.5**, and **4.8**.

## 4. Define implementation commutation on a justified state invariant

**Where:** §4's “Notations”, Definition 4.1, and Theorem 4.5
(`ralin.tex`, lines 30–66 and 189–200).

**Change:** Introduce a concrete state invariant and define commutation over
states satisfying it. Use the same domain in both the causal-conflict and
absorber clauses of the linearization order. State invariant preservation and
the eligible-event/represented-state premises of the scoped replay theorem.

**Why:** Arbitrary malformed states create conflicts that never arise in the
represented datatype; this obstructs Embedded RGA under the current definition.
The invariant must be justified independently. Commutation must not require
both events to be freshly issuable together: that would hide genuine causal
dependencies. The scoped convergence theorem concerns legal causal replays;
it does not automatically cover every permutation of the public order.

**Reference:** Definitions **4.2–4.3** and **4.7–4.8**, Theorem **4.9**.

## 5. Add issuance evidence and the scoped specification bridge

**Where:** §3's Apply rule; §5.3, Theorem 5.2; §6, Theorem 6.1 and
“Discharging the premise” (`opsem.tex`, lines 54–65;
`proof_strategy.tex`, lines 351–369; `seq_spec.tex`, lines 47–94).

**Change:** State the original-issuer guard and retained mint evidence, and
qualify the scoped theorem by certified executions. Keep total sequential
simulation as one sufficient route. Add the route that constructs an
independently legal history for each stored event set and proves both order
requirements and agreement with the stored query. Strengthening Definition 4.4
also requires strengthening its lifting theorem accordingly.

**Why:** RGA/Queue cannot satisfy a premise over arbitrary lists containing
invented IDs, invalid anchors or live non-head removals. Original issuance
supplies useful evidence; it is not rechecked on reordered scratch states.
History legality and specification visibility are additional proof obligations
beyond convergence. A global commutation-compatibility condition is sufficient
for visibility, but a datatype may instead prove it for its selected witness.

**Reference:** Definitions **4.7** and **6.3**, Theorems **5.7**, **6.2**, and
**6.4**, and equation **(2)**.

## 6. State the merge proof's representation and reconstruction premises

**Where:** §5.1's `WeakClosed`, downset and `Admissible` definitions, VC1–VC5,
and §5.2's Join lemma and peeling argument (`proof_strategy.tex`,
lines 39–178 and 309–341).

**Change:** Relate each concrete state to its represented event history. Allow
metadata dependencies to retain commuting causal predecessors. State the
closure, dual maximality and reconstruction premises of the five equations,
and the existence and uniqueness facts needed by the induction. Intermediate
merge representations used in redistribution must come from smaller induction
calls, not an assumed Join theorem for the original union.

**Why:** A commuting predecessor can still supply a tag or anchor needed to
reconstruct an operation. Canonicality and closure under noncommuting visibility
alone do not describe the checked proof. Likewise, the dependency-past replay
called “the state the event saw” need not be its full original issuer state.
All equations can retain concrete equality.

**Reference:** Definitions **5.1–5.4**, Theorem **5.5**.

## 7. Match the operational semantics, including multiple merge bases

**Where:** §3's Fork description, Apply/Merge rules and Lemma 3.1
(`opsem.tex`, lines 48–76 and 112–120).

**Change:** Fork creates a fresh child version containing the source snapshot.
Timestamps increase along visibility, in addition to being unique. Define the
ordinary base as a **greatest** common ancestor. For multiple incomparable
maximal bases, specify recursive virtual-base construction and extend the
execution theorem to its scratch merges.

**Why:** An arbitrary maximal common ancestor need not contain every shared
event. The intersection lemma uses the event-origin/store invariant and a
*greatest* common ancestor. Recursive virtual bases handle the remaining graphs;
they are not implemented by selecting one base arbitrarily.

**Reference:** Definitions **3.1–3.2** and **3.4**, Theorems **3.3** and **5.7**.

## What can stay

Keep concrete state equality and §6's specification-refinement function `α`,
which relates implementation states to independent specification states. The main exposition need not add a separate
direct-Join proof route.

When adding case studies, the anchored Queue is a **separate design** from the
original Queue. The original Fugue issuer and live-anchor specification still
have an incompatibility under the stronger criterion; invariant-scoped
commutation alone does not fix it. See Examples **6.5–6.6**.
