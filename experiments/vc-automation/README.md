# Automating Sal’s five merge VCs

**All 23 current named instances have kernel-checked five-VC proofs.** The
finite equations close with Lean tactics (`simp`, `grind`, `tauto`, `omega`,
`aesop`); the final proofs require no external SMT solver. Implementations,
issuers, representations, policies and VC statements are unchanged.

## What does the RDT author supply?

Shared induction templates and soundness proofs are framework work. The author
supplies datatype mappings, finite-law instantiations and any required helper
lemmas. The table reports the current local proof/annotation code, charging
shared families once. Counts include statements and annotations, not just tactic
bodies; they exclude RDT implementation definitions and generic framework code.

| Instance | Approx. local code lines | Current author work |
|---|---:|---|
| Grow-only set | 10 | Commuting template, set extensionality and simplification. |
| Add-store | 1 | Reuse the same Add-store proof as grow-only set. |
| Finite add-store | 10 | Finite-set extensionality and simplification. |
| Counter | 5 | Additive-counter equations and `omega`. |
| Increment-only counter | 1 | Specialize the additive-counter proof. |
| PN-counter | 1 | Specialize it to signed increments. |
| Flat grow-only set | 7 | Pointwise Boolean equations. |
| Flat grow-only map | 1 | Specialize the Boolean-store proof. |
| Bounded Counter | 21 | Component decomposition, operation cases and `omega`. |
| LWW register | 6 | Maximum algebra, using its existing empty-policy port. |
| Native RGA | 21 | Component decomposition and finite membership equations. |
| TreeMove | 10 | Commuting template and insertion/union simplification. |
| AegisSheet | 10 | Commuting template and insertion/union simplification. |
| Ordinary OR-set | 274 | Finite equations, policy facts and replay/ordering connections. |
| Efficient OR-set | 359 | Finite equations and update/order/representation adapters. |
| MVR | 15 | Four record mappings, six finite laws and template instantiation. |
| Embedded RGA | 113 | Ordered-record mappings, finite laws, helper references and existing honesty projections. |
| Sided Embedded RGA | 112 | The corresponding sided-record mappings and finite laws. |
| Peritext Embedded RGA | 3 | Specialize the Embedded RGA theorem. |
| Queue (anchored enqueue) | 4 | Specialize the Embedded RGA theorem. |
| Sided Peritext Core | 209 | Text projection, store membership and component normalization; reuses the earlier Sided RGA adapter. |
| Sided Peritext RichCore | 11 | Reuse Core and adapt context fields. |
| FugueMax | 548 | Record/list adapters, generator lemmas and an issuance timestamp induction. |

These are current code-size estimates, not unavoidable human effort. One-line
reuse rows assume the parent proof exists. The
[declaration inventory](results/proof-effort.json) records source locations,
hashes and dependency totals; shared dependency totals must not be summed.
Core and Fugue retain their existing expansion routes.

## Certified templates: current boundary

MVR uses a [generic record template](GenericCertifiedRecords.lean). The author
provides record, identifier and overwrite projections and six finite laws:
carrier injectivity, empty initial state, birth timestamp, update membership,
merge membership and issuer target membership. In [MVR](AutomatedMVR.lean),
all six close with `simp`/`rfl`. The framework derives provenance, visible births,
freshness and overwrite coverage, then assembles the unchanged five VCs.

Embedded and Sided RGA use one [ordered-record template](GenericOrderedRecords.lean).
Its eight mappings describe records, identifiers, keys, updates and ordering;
ten finite laws describe initialization, update, merge and ordered equality.
The [instances](AutomatedRGA.lean) also project the existing certified
representation’s creator and chain evidence. The template derives replay
membership, sortedness, coherence, freshness and deletion coverage by generic
induction. **No RDT-specific history induction remains in MVR or either RGA
interface.** Queue and Peritext reuse the Embedded instance.

The [helper registry](OrderedRecordAutomation.lean) lets Lean select the raw
membership, sortedness and extensionality lemmas automatically. Each family
registers five helper names. `ordered_record_simp` performs membership rewriting;
`ordered_record` uses goal matching through a named Aesop rule set and `grind`.
The instance proofs no longer name those individual helpers. The registry
contains no history, VC or Join theorem.

RGA still requires explicit finite case analysis, representation projections
and the helper library itself. These are counted as author work, not hidden
behind the final theorem:

| Template instance | Local annotations/proofs | Retained RDT-specific helper proofs | Combined code |
|---|---:|---:|---:|
| MVR | 15 | 0 | 15 |
| Embedded RGA | 113 | 135 | 248 |
| Sided Embedded RGA | 112 | 143 | 255 |

There are also eight shared lines for identifier-membership reasoning, counted
once across the two RGAs. The shared selection registry/rules take 27 nonblank
source lines (including imports and declarations); these contain the ten
datatype helper registrations and shared conversion/tactic code. Retained
helper counts include transitive, source-written
RDT-module theorems for insertion/merge membership, sortedness and extensionality;
the Sided count includes its key-injection lemma. If those helpers are not already
available, the author must supply them. General coordinate, collection and order
library proofs are assumed available. The [helper inventory](results/template-effort.json)
lists the exact declarations; regenerate it with `measure_template_effort.py`.

The templates consume the **existing** issuance/execution evidence. They do not
automatically prove issuer honesty from an arbitrary new issuer. No new datatype
history invariant is assumed, and the dependency audit rejects reuse of the
previous MVR/RGA history adapters in the five new template-based bundles.
Automatically synthesizing the mappings and finite helper scripts remains open.

## Scope and reproduction

The 23 cases include aliases and specializations. Core/RichCore retain their
native-insert-only premise. Queue means anchored enqueue; the earlier unanchored
queue is historical and excluded. Five VCs feed the checked Join theorem, but
full RA-linearizability additionally needs the sequential bridge. Fugue’s
sequential-specification obstruction remains open. Sequential-bridge automation
is deferred; production bundles still use their existing proofs.

From the repository root, with production dependencies built:

```sh
python3 experiments/vc-automation/verify_expansion.py --automated
python3 experiments/vc-automation/measure_template_effort.py
```

This rebuilds all 23 cases, selecting the reusable templates for MVR, Embedded
RGA, Sided RGA, Queue and Peritext. The [combined audit](results/automated-audit.json)
records source hashes, standard Lean axioms and transitive dependencies. The
[scope inventory](transfer-inventory.json) identifies each theorem.
