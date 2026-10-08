# Automating Sal’s five merge VCs

**All 23 current named instances pass the common verification interface.**
The kernel checks the exact existing `Raw.MergeVCs` types. Implementations,
issuers, policies, representations and specifications are unchanged.

## What does the RDT author supply?

The author supplies record/component mappings, finite laws and projections of
existing representation or issuance evidence. A typed `Input` selects a shared
proof template; `mrdt_verify` assembles all five VCs. Registration rejects finished
VC proofs and direct correctness premises; the dependency audit checks hidden reuse. Generic templates derive replay, ordering, normalization
and coverage facts; current instance declarations contain no bespoke history
induction.

The following source-line counts include complete declaration statements,
annotations and proof bodies. “Instance” also includes input registration and
local definition annotations. “Retained helpers” charges the transitive closure
of source-written datatype theorem helpers, including coordinate and ordering
libraries. Existing implementation definitions and generic framework proofs are
excluded. A specialization includes the family work it consumes.

| Instance | Instance lines | Retained helper lines |
|---|---:|---:|
| Ordinary OR-set | 107 | 0 |
| Efficient OR-set | 221 | 0 |
| Grow-only set | 14 | 6 |
| Add-store | 14 | 6 |
| Finite add-store | 14 | 6 |
| Counter | 9 | 8 |
| Increment-only counter | 9 | 8 |
| PN-counter | 9 | 8 |
| Flat grow-only set | 10 | 7 |
| Flat grow-only map | 10 | 7 |
| LWW register | 10 | 4 |
| Sided Embedded RGA | 113 | 297 |
| Native RGA | 25 | 10 |
| Sided Peritext Core | 121 | 297 |
| Sided Peritext RichCore | 125 | 297 |
| Embedded RGA | 116 | 250 |
| Queue (anchored enqueue) | 115 | 283 |
| Peritext Embedded RGA | 114 | 250 |
| FugueMax | 253 | 700 |
| Bounded Counter | 25 | 21 |
| TreeMove | 14 | 12 |
| AegisSheet | 14 | 5 |
| MVR | 18 | 0 |

**Do not sum the rows:** family declarations and helpers recur under each
consumer. Across the campaign, deduplicating source file/line pairs gives
**984 instance declaration lines, 22 instance annotation/registration lines,
and 1,077 retained helper lines**. The shared finite-helper registries contribute
another **11 annotation lines**, recorded separately. Framework proof and tactic
implementation code is not included in these author-side totals.

These are reproducible source footprints, not estimates of human time or proof
difficulty. The [current effort inventory](results/common-effort.json) records
all declaration ranges, consumers, registration commands and source hashes.
Ranges come from Lean’s transitive dependency audit, rather than selected helper
names. Comment-stripped instance ranges contain no `induction` or explicit
recursor syntax; this diagnostic complements the dependency audit and manual
review, and does not by itself certify the meaning of every helper.

Lean selects registered maximum algebra for LWW and raw RGA membership, ordering and equality helpers from
the finite goals. OR-set finite tactics unfold registered raw definitions and
solve membership equations with `simp` and `grind`. Mappings, constructor cases,
fresh-ID setup and projections of existing certification evidence remain
explicit. Templates do not establish issuer honesty automatically for a new RDT.
Core/RichCore use generic ordered-text/product and query-lift inputs. Fugue uses
generic archived-record and certified-issuance templates; its chain-validity
annotation and finite generator-preservation proofs remain supplied author work.

## Scope and reproduction

The 23 cases include aliases and specializations. LWW retains its existing
empty-policy port. Core/RichCore retain their
native-insert-only premise. Queue means anchored enqueue; the earlier unanchored
queue is historical and excluded. Five VCs feed the checked Join theorem, but
full RA-linearizability additionally needs the sequential bridge. Fugue’s
sequential-specification obstruction remains open. Sequential-bridge automation
is deferred; production bundles still use their existing proofs.

From the repository root, with production dependencies built:

```sh
python3 experiments/vc-automation/verify_expansion.py --common
python3 experiments/vc-automation/measure_common_effort.py
python3 experiments/vc-automation/measure_helper_sources.py
```

The verifier rebuilds all 23 common roots, compares their complete VC types and
audits transitive proof dependencies against forbidden datatype correctness and
history adapters. The [combined audit](results/common-audit.json) records source
hashes, standard Lean axioms, dependencies and declaration locations. The
[scope inventory](transfer-inventory.json) identifies the unchanged targets.

Use `register_mrdt_input input` after defining a finite `CommonVerification.Input`,
then finish the unchanged VC theorem with `by mrdt_verify`. For a partial input,
`mrdt_obligations` exposes the remaining typed fields. The checked
[controls](CommonVerificationControls.lean) demonstrate missing-input and missing
`Shared` diagnostics, reject completed correctness registrations, and show that
false finite equations remain unproved. The common verification command also
runs the positive/negative full-contract comparison controls.
