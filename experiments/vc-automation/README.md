# Automating Sal’s five merge VCs

The common verification interface now lives in
[`Sal/MRDTs/Paper1/Automation`](../../Sal/MRDTs/Paper1/Automation).
Production five-VC proofs use its registered finite inputs, and the existing
Join, represented-version and RA certificates consume those proofs. This
directory contains the production audit tooling and effort reports.

The migration preserves implementations, issuers, operation policies,
representations, execution contracts and existing theorem statements. The 23
named cases include aliases and specializations. Queue means anchored enqueue;
the historical unanchored queue is excluded. Core/RichCore retain native
insert-only issuance. Fugue’s represented-version result uses the common VCs;
its independent sequential-specification bridge remains open.

## What does the RDT author supply?

A typed `CommonVerification.Input` supplies record/component mappings, finite
implementation laws and projections of existing representation or issuance
evidence. `register_mrdt_input input` registers it; `by mrdt_verify` constructs
all five VCs. Registration rejects completed correctness inputs. Shared
proofs derive replay, ordering, normalization and causal coverage. New datatypes
still need the finite laws and issuer evidence required by their selected
input constructor.

OR-set finite tactics unfold registered implementation definitions and solve
membership equations. Ordered-record inputs retain explicit constructor cases,
fresh-ID setup, coordinate facts and issuer projections. Core/RichCore use
ordered-text/product and query-lift inputs. Fugue uses archived-record and
certified-issuance inputs, with explicit chain validity and generator
preservation proofs. Sequential bridges remain the existing production proofs.

## How many expanded VCs, using Neem's convention?

Neem instantiates a fixed nine-case induction scheme for its bottom-up merge
rules. Its [F* interface](https://github.com/fplaunchpad/neem/blob/main/code/interface/App_mrdt.fsti#L83)
contains **21 merge VCs**: nine two-operation cases, nine one-operation cases,
one combined zero-operation case, and merge commutativity and idempotence.
The four policy obligations above that interface section are separate. This
counts schematic induction obligations, before splitting on an RDT's operation
constructors; it does not count helper lemmas or solver calls.

Using that convention, Sal's current **policy-based expansion has 17
merge/replay obligations**:

| Group | Schematic obligations |
|---|---:|
| Merge commutativity | 1 |
| Initial-state merge | 1 |
| Shared redistribution | 1 |
| [Local redistribution](../../Sal/MRDTs/Paper1/Automation/LocalAssembly.lean): base/step and freshness schemas | 7 |
| [Causal delta](../../Sal/MRDTs/Paper1/Automation/CausalCoverage.lean): base/step and freshness schemas | 7 |
| **Total** | **17** |

The [policy kit](../../Sal/MRDTs/Paper1/Automation/GenericPolicyExpansion.lean)
also requires **eight policy/event-order obligations**, reported separately:
two update-only equations and six classification/order laws. The full kit therefore has
25 fields, of which 17 belong to the merge/replay expansion. These are schema
occurrences in the templates: freshness proofs are shared across the local and
causal templates, and some base cases follow from generic lemmas. They are not
17 independent handwritten proofs.

Both OR-sets use this policy expansion. Ordinary OR-set additionally supplies
a full commutation characterization and an existing replay-witness projection;
efficient OR-set supplies seven mask-representation laws and a semantic
projection. These connect the implementation representation to replay and are
outside the 17 expanded merge obligations. The fully commuting specialization
instead supplies five direct finite merge equations, plus update commutation
and contract identity checks.

**There is no single framework-wide “five VCs expand to N” count today.** The
common command selects among family-specific templates. Certified-record
instances use a different route: five generic
[record-merge equations](../../Sal/MRDTs/Paper1/Automation/CertifiedExpansion.lean)
are proved once, with birth freshness, deletion coverage, common membership
and newborn freshness derived from issuance/replay evidence. The author
supplies implementation/representation laws: six for immutable records (MVR),
ten for ordered records (Embedded/Sided RGA, Peritext and Queue), or thirteen
for archived ordered records (Fugue). These are **interface laws, not
Neem-style expanded merge VCs**. Core reuses the ordered-record laws through a
product template; RichCore adds no merge-law obligation through query transport.
Fugue also uses nine auxiliary issuance-model laws to derive its issuer
evidence. Independent sequential-specification bridges are outside all these
counts.

## Current production evidence

[`results/production-audit.json`](results/production-audit.json) records the
actual production VC roots and existing public certificate endpoints, their
transitive dependencies, Lean axioms, declaration locations and source hashes.
It checks use of the common verifier and excludes earlier datatype VC/Join
proof routes. Its VC evidence closures are extracted from the actual submitted
`CommonVerification.verify` proof applications, separately from unchanged
sequential-history fields in certificate bundles.

[`results/production-effort.json`](results/production-effort.json) measures
current RDT-specific proof code. The main total includes the finite inputs,
annotations, automation calls, and all required datatype helper proofs already
present in the repository. For example, Embedded RGA requires 124 input/proof
lines plus 250 existing insertion, merge and coordinate-lemma lines: **374
lines in total**. Helpers may belong to that same RDT or be shared with another;
they are required proofs that automation reuses, rather than generates.

The historical estimate uses the direct production VC proofs at commit
[`e89cd6d`](https://github.com/fplaunchpad/sal/commit/e89cd6d), immediately before
the production automation migration. Both columns include required
RDT-specific helper proofs. They exclude implementation and contract
definitions, shared generic framework proofs, and sequential-specification
bridges. They count nonblank, noncomment lines of complete declarations, including statements and proof
bodies. They measure source footprint, not human time or proof difficulty.
Per-case totals overlap because instances share helpers, so do not sum the rows.

The current audit passes **23 named cases, 69 distinct public endpoints and 95
existing production roots**. These include aliases and family specializations.

| Instance | Before automation (lines) | With automation (lines) |
|---|---:|---:|
| Grow-only set | 40 | 17 |
| Add-store | 40 | 17 |
| Finite add-store | 28 | 17 |
| Counter | 49 | 14 |
| Increment-only counter | 49 | 14 |
| PN-counter | 49 | 14 |
| Flat grow-only set | 45 | 15 |
| Flat grow-only map | 45 | 15 |
| LWW register | 32 | 14 |
| Native RGA | 60 | 33 |
| Bounded Counter | 58 | 44 |
| TreeMove | 33 | 24 |
| AegisSheet | 26 | 17 |
| Ordinary OR-set | 336 | 106 |
| Efficient OR-set | 234 | 219 |
| MVR | 148 | 17 |
| Embedded RGA | 726 | 374 |
| Sided Embedded RGA | 773 | 420 |
| Peritext Embedded RGA | 726 | 374 |
| Sided Peritext Core | 872 | 426 |
| Sided Peritext RichCore | 882 | 430 |
| Queue (anchored enqueue) | 759 | 407 |
| FugueMax | 3377 | 953 |

Across all 23 cases, the estimated RDT-specific footprint falls from **5,921
to 2,053 distinct lines**, counting each shared source line once. The
[historical comparison](results/manual-effort.json) records the baseline
proof dependencies, source hashes and counting decisions. These are the costs
of the checked proof routes, not lower bounds on what a shorter proof could do.

The shared automation library is a separate, once-per-framework cost:
**2,758 code lines**, including its imports, tactics and annotations. It is
excluded from both RDT-specific columns. The measurement files retain the
per-declaration breakdown and the additional existing generic dependencies.

## What the reduction means

The combined RDT-specific footprint falls by about **65%**, but the reduction
is uneven. Efficient OR-set improves only **6%** (234 → 219): its earlier
proof was already compact, and the new interface still requires explicit
mappings and finite-law proofs. Embedded RGA improves **48%** (726 → 374),
while retaining its insertion, merge and coordinate lemmas.

The demonstrated result is reusable, kernel-checked proof assembly: shared
templates perform the history inductions, and Lean tactics discharge finite
obligations using supplied definitions and registered lemmas. The current
campaign does not require an external SMT solver. It does not discover new
templates, representations, issuer invariants or sequential specifications.
Authors still choose the template, supply its mappings and evidence, and prove
helper facts that the library cannot yet discharge. Further reductions depend
on deriving more of these inputs from the implementation and reusing more of
the list, ordering and coordinate proofs. Sequential-bridge automation remains
separate from this result.

## Reproduction

From the repository root:

```sh
scripts/check-mrdt-refactor.sh
scripts/check-paper1.sh
python3 experiments/vc-automation/verify_expansion.py --common
python3 experiments/vc-automation/measure_common_effort.py
```

The `--common` command delegates to `scripts/verify-paper1-automation.py`,
which builds the existing ledger and audits the current production roots.
The production controls under `Sal/MRDTs/Paper1/Automation` exercise missing
inputs and fields, rejected completed-correctness registrations, and false
finite equations. The source preservation report checks unchanged declaration
headers and semantic definition bodies across implementation, policy, issuance and execution contracts.
The positive/negative Lean comparator separately exercises full-contract
definitional equality; source comparison alone is not kernel type equality.

To reproduce the historical column, build `Sal.MRDTs.Paper1.Ledger` in a
separate checkout of `e89cd6d`, then run from the current repository:

```sh
python3 experiments/vc-automation/measure_manual_effort.py \
  --baseline-dir /path/to/built-e89cd6d-checkout
```

This reads the old kernel dependency graph and checks the measured source files
against that Git commit; it does not change the working branch.
