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

## Current production evidence

[`results/production-audit.json`](results/production-audit.json) records the
actual production VC roots and existing public certificate endpoints, their
transitive dependencies, Lean axioms, declaration locations and source hashes.
It checks use of the common verifier and excludes earlier datatype VC/Join
proof routes. Its VC evidence closures are extracted from the actual submitted
`CommonVerification.verify` proof applications, separately from unchanged
sequential-history fields in certificate bundles.

[`results/production-effort.json`](results/production-effort.json) measures
current production source footprints from those VC evidence closures. Author
inputs and finite proof declarations, production automation invocations,
retained datatype theorem helpers and the shared generic library are reported
separately. Complete source-written declarations are charged; existing
implementation and contract definitions are excluded from author totals.
Per-case rows overlap and must not be summed: campaign totals deduplicate
source file/line pairs. Source lines measure footprint, not human time or proof
difficulty. Induction/recursor scans are diagnostics, alongside the dependency
audit and manual review.

The current audit passes **23 named cases, 69 distinct public endpoints and 95
existing production roots**. These counts include aliases and family
specializations, rather than 23 independent designs.

| Instance | Author lines | Retained datatype helper lines |
|---|---:|---:|
| Grow-only set | 11 | 6 |
| Add-store | 11 | 6 |
| Finite add-store | 11 | 6 |
| Counter | 6 | 8 |
| Increment-only counter | 6 | 8 |
| PN-counter | 6 | 8 |
| Flat grow-only set | 7 | 7 |
| Flat grow-only map | 7 | 7 |
| LWW register | 10 | 4 |
| Native RGA | 23 | 10 |
| Bounded Counter | 23 | 21 |
| TreeMove | 12 | 12 |
| AegisSheet | 12 | 5 |
| Ordinary OR-set | 106 | 0 |
| Efficient OR-set | 219 | 0 |
| MVR | 17 | 0 |
| Embedded RGA | 116 | 250 |
| Sided Embedded RGA | 115 | 297 |
| Peritext Embedded RGA | 116 | 250 |
| Sided Peritext Core | 121 | 297 |
| Sided Peritext RichCore | 125 | 297 |
| Queue (anchored enqueue) | 116 | 250 |
| FugueMax | 253 | 700 |

The deduplicated campaign contains **937 author declaration lines, 30
registration/annotation/invocation lines and 1,044 retained datatype helper
lines**. Author rows include input statements, finite proof bodies and new
VC theorem declarations in full. Existing certificate bundles contribute only
their automation invocation lines; unchanged sequential-history fields are
excluded.

The reusable production library is a separate cost: **2,759 code lines**,
including imports, tactics and annotations, with charged instance lines in
mixed modules removed. Its actual VC dependency declarations occupy **2,027
lines**, and existing generic foundational theorem helpers occupy another
**658 lines**. The 11 shared registry annotation lines are included in the
library total. These library/dependency measurements overlap and must not be
added together. Paper1 helper dependencies are generic metadata, ordering and
convergence facts; the inventory does not omit datatype-specific certified
replay or issuer theorem helpers.

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
