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

For both OR-sets, `derive_mrdt_input` constructs the input from proof-free
`PolicyData` (the event comparison) and optional `MaskData` (the record type
and carrier/update/birth/kill maps). The frontend selects the existing replay
witness when no mask is supplied, or derives semantic-mask replay when a mask
is supplied. It builds the policy and mask templates and discharges their
finite laws from registered raw definitions. These instances supply no
per-obligation tactic scripts or completed datatype proofs. Their earlier helper
statements remain available for compatibility but are excluded from the
production VC-input dependency closure.

Embedded RGA supplies eight data maps in an ordered-record description,
raw-equation annotations and chain/code mappings. Required specialization
proofs and code-validity obligations count in its datatype footprint.
`derive_ordered_kit` constructs the ten finite laws using generic list and
lexicographic-order theorems, with raw recursive equations checked against the
implementation. Generic prefix-code lemmas derive coordinate injection; the
input frontend projects the existing issuance and replay contracts. Anchored
Queue and Peritext reuse this input. Existing datatype helper statements remain
public but the actual verifier-evidence audit rejects their reuse where the
generic route replaces them. Other ordered-record inputs retain explicit
finite proofs. Core/RichCore use
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

Both OR-sets use this policy expansion. The frontend additionally derives
ordinary OR-set's full commutation characterization and projects its existing
replay witness; for efficient OR-set it derives seven mask-representation laws
and projects the existing semantic representation. These connect the implementation representation to replay and are
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
for archived ordered records (Fugue). Embedded and Sided RGA’s ten fields are constructed
by the shared frontend. Fugue’s thirteen fields are derived from an archived
list description and ten finite implementation obligations. These are **interface laws, not
Neem-style expanded merge VCs**. Core reuses the ordered-record laws through a
product template; RichCore adds no merge-law obligation through query transport.
Fugue supplies nine finite issuance-model laws, derived from raw issuer
definitions and generic lookup, chain and minting arguments. Its coordinate
injection and tag validity follow from generic code composition with concrete
fixed-width, alphabet and raw-equation certificates. Independent sequential-specification bridges are outside all these
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
present in the repository. Compatibility helper statements retained solely to
preserve the public API are excluded when the production input bypasses them;
the dependency audit checks this for both OR-sets, the Embedded and Sided routes,
and Fugue.
Embedded RGA requires **60 lines**: 55 datatype input, mapping and equation
certificate lines plus 5 annotation/invocation lines, with no retained datatype
helper theorems. Anchored Queue requires **69 lines**, including 7 unary-code
helper lines and its two proof-packaging fields. Helpers may belong to that same RDT or be shared with another;
they are required proofs that automation reuses, rather than generates.

The historical estimate uses the direct production VC proofs at commit
[`e89cd6d`](https://github.com/fplaunchpad/sal/commit/e89cd6d), immediately before
the production automation migration. Both columns include required
RDT-specific helper proofs. They exclude implementation and contract
definitions, shared generic framework proofs, and sequential-specification
bridges. They count nonblank, noncomment lines of complete declarations,
including statements and proof bodies, plus required annotations and explicitly
identified proof-packaging fields. They measure source footprint, not human time or proof difficulty.
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
| Ordinary OR-set | 336 | 8 |
| Efficient OR-set | 234 | 26 |
| MVR | 148 | 17 |
| Embedded RGA | 726 | 60 |
| Sided Embedded RGA | 773 | 67 |
| Peritext Embedded RGA | 726 | 60 |
| Sided Peritext Core | 872 | 74 |
| Sided Peritext RichCore | 882 | 78 |
| Queue (anchored enqueue) | 761 | 69 |
| FugueMax | 3377 | 322 |

Across all 23 cases, the estimated RDT-specific footprint falls from **5,923
to 704 distinct lines**, counting each shared source line once. The
[historical comparison](results/manual-effort.json) records the baseline
proof dependencies, source hashes and counting decisions. These are the costs
of the checked proof routes, not lower bounds on what a shorter proof could do.

The shared automation library is a separate, once-per-framework cost:
**3,985 code lines**, including its imports, tactics and annotations. It is
excluded from both RDT-specific columns. The measurement files retain the
per-declaration breakdown and the additional existing generic dependencies.

## What the reduction means

The combined RDT-specific footprint falls by about **88%**. Efficient OR-set
improves **89%** (234 → 26); Embedded RGA improves **92%** (726 → 60).
Generic proofs replace the required datatype insertion, merge, order and
coordinate-injection helper theorems. Raw-equation certificates, chain/code
mappings and their annotations remain counted author inputs.

Against the immediately preceding `ffec6e9` production baseline, Embedded RGA
falls from **378 to 60 lines**, and anchored Queue from **413 to 69 lines**.
The [baseline snapshot](results/ordered-derivation-baseline.json) retains the
previous published 374/407 counts: the corrected comparison also charges four
concrete registry lines and Queue’s two unary-code proof-packaging fields.
The historical Queue comparison likewise charges those two fields (759 → 761).

Against production baseline `7e7ec86`, Sided Embedded RGA falls from **424 to
67 lines**, Core from **430 to 74**, RichCore from **434 to 78**, and FugueMax
from **959 to 322**. The [baseline snapshot](results/sided-derivation-baseline.json)
retains the checked declarations, registrations and source hashes. The submitted
VC inputs use no retained datatype helper theorems for these four cases. Their
remaining author code consists of data mappings, raw-equation certificates,
finite issuance adapters and concrete code-composition proofs. Fugue's result is
represented-state convergence; its checked sequential-specification obstruction
remains.

Against the immediately preceding production baseline `7880732`, this
OR-set derivation change reduces ordinary OR-set from **106 to 8 lines** and
efficient OR-set from **219 to 26 lines**, using the same counting rules.
The [baseline recount](results/orset-derivation-baseline.json) includes required
annotations and datatype helpers, including helpers defined under `Paper1`.
Neither final OR-set VC proof depends on retained datatype helper theorems or
cached finite-law proofs. Data annotations count even when elaboration inlines
them. Compatibility helper statements retained for public API preservation
count only when the production proof requires them. Local annotations used
only by those compatibility proofs are also excluded.

Shared templates perform the history inductions. For both OR-sets, the frontend
selects witness or mask replay from proof-free annotations and generates and
discharges the finite laws from implementation definitions. Embedded RGA and
Queue and Sided RGA use the ordered frontend described above; Core and RichCore
reuse the Sided input. Fugue uses archive, code-composition and issuance
derivations. Other families
still supply template mappings, finite evidence and helper facts that the
library cannot yet discharge. The campaign requires no external SMT solver;
it does not discover representations, issuer invariants or sequential specifications.
Sequential-bridge automation remains
separate from this result.

## Reproduction

From the repository root:

```sh
scripts/check-mrdt-refactor.sh
scripts/check-paper1.sh
python3 experiments/vc-automation/verify_expansion.py --common
python3 experiments/vc-automation/test_measurement_registration.py
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
