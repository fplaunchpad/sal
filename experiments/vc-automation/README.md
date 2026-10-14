# Automating Sal’s five merge VCs

The common verification interface now lives in
[`Sal/MRDTs/Paper1/Automation`](../../Sal/MRDTs/Paper1/Automation).
Production five-VC proofs use its registered finite inputs, and the existing
Join, represented-version and RA certificates consume those proofs. This
directory contains the production audit tooling and effort reports.

The migration preserves implementations, issuers, operation policies,
representations, execution contracts and existing theorem statements. The current
19 implementation/proof cases consolidate the grow-only set and generic AddStore
into one entry and consolidate the ordinary counter to unrestricted
increment/decrement (the former PN case). The two increment-only duplicates
are removed. Counts describe proof configurations, not distinct abstract
datatypes: FinsetStore and the pointwise Boolean FlatGrowOnly set implement the
same grow-only set semantics. FinsetStore remains the enumerable carrier needed
by Peritext. Queue means anchored enqueue;
the historical unanchored queue is excluded. Core/RichCore retain native
insert-only issuance. Fugue’s represented-version result uses the common VCs;
its original issuer now has a complete natural-origin sequential certificate
in `FugueMaxNaturalCertificate`. The former live-parent language remains
refuted; historical effort reports do not measure the new bridge. The 19-case automation inventory is distinct
from the 18-package production registry; the latter retains the historical queue.

Kartik's split policy interfaces are integrated and checked for these same
19 retained cases, with the original event/state scopes and five-VC dependencies.
The published Balegas matrix/max counter is the sole bounded-counter algorithm
in production. Its checked five-VC, sequential-history, local-safety and
global-union proofs live in
[`BalegasBoundedCounterAudit`](../../Sal/MRDTs/Paper1/BalegasBoundedCounterAudit.lean).
It is not a measured automation case. Its
[bounded exhaustive control](balegas-controls.py) checks 49,796 trace prefixes
with zero failures; ten Lean PASS+FAIL controls exercise the actual definitions.
The earlier independent-account and transferable-counter implementations have
been retired. Archived effort rows for `BoundedCounter` in the historical JSON files describe
the retired independent-account implementation, not Balegas.

The JSON/log reports in `results/` and the baseline directories retain fixed
historical measurements. Their old case inventories and source hashes do not
assert current source coverage. [Historical measurement provenance](results/historical-measurements.json)
records this boundary. The active audit script selects 19 retained cases;
[`transfer-inventory.json`](transfer-inventory.json) records that current selection.
No historical effort totals have been relabelled as measurements of Balegas.

Neem's corrected enable-wins and disable-wins flags also have separate checked
five-VC and Boolean-history proofs, audited by
[`NeemFlagAudit`](../../Sal/MRDTs/Paper1/NeemFlagAudit.lean). They are not yet
registered or measured automation cases. Their shared proof uses explicit
causal-prefix and live-event lemmas; it is not an automatic-discovery result.
[Exhaustive controls](neem-flag-controls.py) check 55,987 trace prefixes per
polarity with zero failures and catch the older scalar-flag mutant. Nine
Lean PASS+FAIL examples check the actual definitions.

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
preservation proofs. Sequential bridges have a separate measured experiment below.

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
RDT-specific proof code at its recorded source snapshot. The main total includes the finite inputs,
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

The recorded effort audit before consolidation covered **23 named cases,
69 distinct public endpoints and 95 existing production roots**. Its JSON reports
retain that historical inventory. The current audit scripts check 19 cases; the
grow-only set keeps the original five-VC and sequential-bridge checks.

| Instance | Before automation (lines) | With automation (lines) |
|---|---:|---:|
| Grow-only set | 40 | 12 |
| Finite add-store | 28 | 12 |
| Counter (former PN row) | 49 | 14 |
| Flat grow-only set | 45 | 13 |
| Flat grow-only map | 45 | 13 |
| LWW register | 32 | 14 |
| Native RGA | 60 | 17 |
| TreeMove | 33 | 19 |
| AegisSheet | 26 | 12 |
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
to 650 distinct lines**, counting each shared source line once. The
[historical comparison](results/manual-effort.json) records the baseline
proof dependencies, source hashes and counting decisions. These are the costs
of the checked proof routes, not lower bounds on what a shorter proof could do.

The shared automation library is a separate, once-per-framework cost:
**4,003 code lines**, including its imports, tactics and annotations. This whole-module count also
includes the one-line unused private compatibility helper. It is
excluded from both RDT-specific columns. The measurement files retain the
per-declaration breakdown and the additional existing generic dependencies.

## What the reduction means

The combined RDT-specific footprint falls by about **89%**. Efficient OR-set
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
Sequential-bridge automation is measured separately below.

## Shared reasoning across datatype families

`mrdt_representation [definitions]` discharges finite state equations by
unfolding the supplied definitions, decomposing extensional equality, exposing
constructor and conditional branches, and applying membership, Boolean and
linear-integer reasoning. The same command is used for Add-store, finite
add-store, flat counters, flat grow-only sets/maps, native RGA, TreeMove and
AegisSheet. These are seven retained input families; named counter and map
specializations reuse them. The historical eight-family/40-field measurement
also included the retired independent-account counter.

The author still supplies the implementation definitions to unfold, the input
packaging and any remaining commuting/evidence helpers. This is reusable
representation reasoning, not invariant discovery. Scalar counters already
had a two-line kernel proof, so their reuse provides a generality test rather
than a source reduction.

Against `fa96479`, the eight kernel declarations and their previously required private
helper shrink from **70 to 16 lines**, including theorem statements and tactic
arguments. The old private helper remains available but is absent from the production
proof dependencies. The new shared tactic costs **16 code lines**. This is a targeted
slice of the full costs in the table above, not an additional reduction to add
to those totals. Independent controls exercise unrelated representations and
reject a merge that drops one input and an incorrect arithmetic equation.

A separate `origin_subset_prefix` lemma transports an honest origin into a
visibility-respecting sequential prefix. TreeMove and AegisSheet share this
order argument while retaining their different tree-cycle and spreadsheet
correctness proofs. Both use finite event logs; they are not evidence of
different carrier representations. The set/function/arithmetic cases above
supply that test. Anchor legality and insertion adjacency remain explicit
where a datatype needs them.

The origin-prefix refactoring adds a **26-line shared module**. Its concrete
proof dependencies shrink from **46 to 28 lines** for TreeMove and **120 to 89**
for AegisSheet; their generic dependency closures increase by 66 and 43 lines, respectively. These
small reductions do not automate either datatype's sequential specification.
The [measurement](results/shared-pattern-measurement.json) records the fixed
baseline, complete production dependencies, shared costs and preservation
checks. The independent validation modules add 111 test lines, counted
separately from production proofs. Kernel controls also show why visibility order is necessary: reversing
`[1, 2]` retains the origin evidence but puts event `1` outside event `2`'s prefix.

## Sequential-history bridge experiment

The selected production bridges now use generic finite-set projection and
guarded-fold templates. The baseline is production commit `052b8fb`, after the
VC automation campaign. Counts are nonblank, noncomment source lines in complete
kernel-reached concrete declarations, including their statements, proof bodies,
wrappers and datatype descriptions. Shared framework code and semantic or
implementation definitions are reported separately.

| Production bridge | Before (lines) | Current (lines) |
| --- | ---: | ---: |
| Ordinary OR-set | 49 | 23 |
| Efficient OR-set | 48 | 24 |
| Issuance-certified Embedded RGA | 2,021 | 2,001 |

The roots include both OR-set `foldHistorySound` and
`commutationCompatibility` theorems, and Embedded RGA's
`canonical_valid_history`. Thus the RGA count includes ordering, visibility and
legal-history selection, in addition to sequential acceptance. The full
concrete helper closure includes execution and issuance invariants also used by
the VC proofs. These columns overlap the VC table above and must not be added
to it. The separate generic bridge library is **175 code lines** across
`ProjectedSimulation`, `FiniteSetSimulation`, `GenericGuardedFold` and
`Framework/SequentialInduction`, including
imports, macros and annotations. Embedded RGA also uses the new 24-line causal
issuance induction module. Bridge-only modules are excluded from the
4,003-line VC library measurement.

For the OR-sets, finite descriptions give raw record actions and independent
model actions; the library derives projection and observable commutation.
The actual production closures exclude the old `view_step` and
`elements_update` bridge proofs. Embedded RGA is a boundary experiment with no
substantial reduction: the generic template owns history induction and the
filter projection, while ordered-chain insertion adjacency and
execution/issuance legal-history selection retain substantial concrete proofs.
Both its acceptance and visibility paths exclude the old `embed_seq_sound`.
Fugue's former live-parent specification remains refuted. Its new natural-origin
bridge is checked but is not measured by this historical experiment.

The [baseline closure and measurement](bridge-baseline/measurement-052b8fb.json),
[baseline provenance and 23-case bridge inventory](bridge-baseline/production-audit-052b8fb.json),
and [current comparison](results/bridge-measurement.json) expose declaration
ranges, classifications, axioms and source hashes. The audit hashes the full
local import closure, including macros and description fields absent from
compiled proof expressions. Source preservation checks retain statements,
contexts and semantic definitions; Lean controls additionally pin all three
simulation relations to their original projections and exercise rejected
degenerate set actions. Old-dispatch negative controls check the dependency
gates themselves.

## Sequential bridges beyond OR-sets

`GuardedStateProjection` derives replay refinement, query agreement and history
acceptance from a supplied invariant, projection and local transition/observation
laws. Transitions need only correspond at justified states and legal extensions.
Execution and issuance evidence select a legal history; they do not replace the
five VCs or independently establish the datatype's sequential semantics.

The current experiment reduces structural proof work beneath that interface:

The following historical measurement table groups shared bridges; the duplicate
AddStore row has been consolidated with the grow-only set. Counts are nonblank, noncomment lines in the transitive
closure of each registered sequential-bridge theorem, including required helper
proofs and annotations. They do not measure just the final wrapper.

Refactoring audits are not required datatype-author proof cost. In particular,
`ORSetSharedSpecification.admits_iff` compares the two complete languages but
is not used to discharge either implementation's bridge. The analogous
log-to-set/counter language-preservation theorems are also audit results.
Count the shared sequential specification once as a datatype description,
each required implementation-specific bridge, and shared bridge helpers once
in the deduplicated total. Do not add optional equivalence audits to those
required proof costs. The historical measurements below have not been rerun
for the natural-specification campaign.

| Case | Classified proof/description lines | All concrete source lines | Main manual argument |
|---|---:|---:|---|
| Grow-only set (`AddStore`) | 9 | 26 | Direct update simulation |
| Finite AddStore | 5 | 22 | Direct update simulation |
| Counter (former PN) | 10 | 27 | Arithmetic update simulation; historical measurement |
| Flat grow-only set / map | 7 | 24 | Pointwise update simulation |
| LWW register | 744 | 829 | Legal ordering and last-write observation |
| Native RGA | 1,494 | 1,693 | Ordered replay and reference validity |
| TreeMove | 772 | 882 | Rendering, cycle checks and ordered replay |
| AegisSheet | 2,744 | 3,354 | Materialization, undo and overwrite semantics |
| Ordinary OR-set | 17 | 55 | Set projection description |
| Efficient OR-set | 18 | 56 | Live-element projection description |
| MVR | 314 | 420 | Certified replay and surviving writes |
| Embedded RGA / Peritext Embedded RGA | 2,001 | 2,199 | Coordinates, adjacency and legal-history selection |
| Sided Embedded RGA | 2,526 | 2,756 | Sided ordering and legal-history selection |
| Sided Peritext Core | 3,576 | 3,933 | Text/product refinement and history legality |
| Sided Peritext RichCore | 3,622 | 4,107 | Core refinement and query transport |
| Anchored Queue | 503 | 624 | Scheduling a legal queue history |
| FugueMax | — | — | Natural-origin bridge checked; not measured in this experiment |

The first numeric column uses an explicit proof/descriptor classifier. The
second includes **every concrete declaration kind**, including implementation
and independent specification definitions, so unclassified invariant definitions
cannot disappear from the accounting. These are source footprints, not author
time or counts of independent obligations. The [full report](results/seq-bridge-effort.json)
records the 17 distinct roots, shared dependencies and classification limits.
It reports 5,901 deduplicated shared source lines across these bridge closures,
including existing framework support; that is not the cost of a new library.

Do not sum these rows or add them to the VC column. Families share proofs, and
bridge proofs reuse execution/issuance invariants. Some registered VC roots are
whole certificate bundles that also contain the history proof. The OR-set
numbers here cover `foldHistorySound` alone; the preceding comparison also
includes commutation compatibility, so its 23/24-line counts have a wider scope.


AegisSheet's selected preservation declarations, including new helpers, shrink
from **210 to 130 lines**. Shared closure rules account for 22 saved lines;
removing duplicate same-origin/causal-origin semantic proofs accounts for the
other 58. The latter is proof reuse, not automatic discovery of cell or purge
semantics. In particular, the issuer-to-witness extraction remains explicit.

The shared rules transport witnesses upwards into a larger event carrier. They
do not infer validity in an arbitrary smaller origin from validity in a merged
prefix. The new control demonstrates why that inference is false. Fresh-key
uniqueness also needs freshness; issuance alone does not prove arbitrary semantic
invariants without an operation-specific local argument.

Embedded RGA now uses `issued_event_induction`: its callback receives the actual
issuer replay, the guard and the property for earlier events; configuration
causality supplies strict timestamp descent. This removes repeated causal
induction machinery. Its new guarded projection still supplies the substantial
local insertion proof. The descriptor adds concrete cost, so routing the bridge
through this interface is not itself a proof-size reduction.

TreeMove tests reuse of origin transport and the existing simulation interface.
Its node identifiers are not event timestamps, so the RGA timestamp/coordinate
birth argument does not apply to tree references. The new causal-induction
helper currently has one production family, Embedded RGA; no broader reuse is
claimed for it.

The existing `guarded_projection_step [definitions] using [local_laws]` tactic
can apply the shared closure and witness rules, as checked by the new controls.
There is no new solver and no invariant discovery. Concrete invariants,
projections, semantic extraction and local preservation lemmas remain author
inputs. AegisSheet and TreeMove production histories and Embedded RGA production
query refinement use guarded simulation. The independent machines, issuers and
public theorem assumptions are preserved.

The [durable baseline](certification-invariants-baseline/README.md) and
[complete comparison](results/certification-invariants-measurement.json) record
all concrete declarations, descriptors, annotations and helper dependencies,
whole changed files including retained helpers, and shared-library cost. The
baseline is the captured worktree after the guarded-interface experiment.
Across the same public endpoints before and after this campaign, the
deduplicated classified proof/description closure falls **7,799 → 7,788** lines;
all concrete declaration kinds fall **9,005 → 9,019**. These include both Paper1
and independent production sequential certificates, a wider scope than the
per-case table above. Embedded RGA's independent production bridge grows
**1,997 → 2,003** proof/description lines; the improvement is not uniform.

The refreshed whole-source comparison also includes later framework and instance
changes. It therefore does
not isolate the net source cost of the original abstraction campaign. The two
shared induction modules still cost 65 lines; the 23-case closure table above
retains its fixed registered scope. The modest change in the fixed
proof closures supports stopping further abstraction work here: the remaining
expensive arguments are largely datatype semantics. It does not establish
automatic sequential-bridge derivation.

Controls check births, fresh and duplicate keys, absent births, unsupported
origins, invalid downward transport and nonmonotone predicates. Existing
nonempty RGA traces, illegal-origin controls and Fugue's rejected live-parent language
remain checked. Trusted model definitions are unchanged; these proof refactors
do not constitute a new external validation of the source algorithms. The audit
preserves 484 existing declarations, with two reviewed sound-only certificate
proof replacements. The recorded production audit covered 23 cases and 95 roots before consolidation; both
repository gates passed at that measurement checkpoint, including 187 runtime tests
and 569 benchmark records. Those counts are historical evidence.

## Reproduction

From the repository root:

```sh
scripts/check-mrdt-refactor.sh
scripts/check-paper1.sh
python3 experiments/vc-automation/verify_expansion.py --common
python3 experiments/vc-automation/test_measurement_registration.py
python3 experiments/vc-automation/measure_common_effort.py
python3 scripts/check-paper1-bridge-contracts.py
python3 scripts/measure-paper1-bridges.py
python3 scripts/measure-paper1-shared-patterns.py
python3 scripts/measure-paper1-certification-invariants.py
python3 experiments/vc-automation/measure_bridge_effort.py
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
