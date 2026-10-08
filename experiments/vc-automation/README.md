# Five-VC automation experiment

Question: can Sal's existing five merge VCs be discharged automatically from
stated premises and datatype definitions, and what additional assistance is
necessary? This experiment preserves the original polymorphic propositions,
implementations, representation relations, and production proofs. It does not
attempt invariant discovery or the sequential-specification bridge.

**Scope correction:** the older matrix below tested unexpanded whole VCs.
The current campaign expands histories into finite equations, following Neem's
frozen-event and equation-shaped induction method. It targets Sal's actual five
indexed equations, whose nested local equation needs additional rules.

## Inductive expansion: current evidence

**Both OR-sets now obtain all five unchanged merge VCs through a kernel-checked
inductive-expansion route.** `ExpandedVCs.lean` exports
`NeemExpansion.Exact.expanded_vcs` and `NeemExpansion.Efficient.expanded_vcs`,
whose types use the existing production `Raw.MergeVCs`, representation and
metadata scheme. The production bundles have not been replaced.

The root independently rebuilt all 15 modules in this route and audited both
complete theorem dependency closures. Only standard Lean axioms occur
(`propext`, `Quot.sound`, `Classical.choice`); no old VC, Join or datatype
state/history invariant proof occurs. Existing finite event-policy facts and
generic replay/order theorems are reused. `ExpandedPolicy.lean` obtains the
conditional-commutation law from the new equation induction, avoiding the old
invariant-based policy proofs. Evidence: `results/expansion-audit.json`,
`results/expansion-audit.log`, and `results/expansion-build.log`.

The local proof strengthens its induction hypothesis to quantify over the
intermediate state. It jointly replays only the nested common/opposite scopes,
whose combined order is proved acyclic in `LocalCoverage.lean`. Singleton
causal-past equations then permit an independent replay of the causal past.
This preserves the original nested merge and avoids requiring incompatible
side histories to share a linearization. Freshness is itself an equation
propagated by finite base/step rules, not a supplied state invariant.

The causal proof keeps the final event frozen. Common steps, commuting local
steps and strict policy predecessors preserve the equation. A later absorber
resets it after the last conflicting local event; `CausalCoverage.lean` derives
that event from the original maximality and metadata premises.

The efficient representation already uses a semantic live/dead predicate.
`EfficientReplayAdapter.lean` derives canonical replay from this **existing
representation**, using newly proved finite update/event certificates and the
generic collection induction in `InductiveMask.lean`. No extra datatype
state/history invariant or previous representation-invariant theorem is supplied.
The merge-VC inductions themselves use equation-shaped hypotheses.

### Reproduce and interpret the result

With production imports already built, run:

```sh
python3 experiments/vc-automation/verify_expansion.py
```

This rebuilds the experimental dependency graph, checks both original five-field
bundle types and rejects unexpected axioms or forbidden transitive proof
references. The experiment needs neither an external SMT solver nor a solver
axiom for its successful complete route.

The generic soundness components are `LocalAssembly.raw_local_redistribute` and
`CausalCoverage.raw_causal_delta`; the other three fields follow from finite
merge algebra. The full bundles assemble these components without an assumed
Join theorem. The local bridge uses seven kernel fields (including a seed
obtained from merge algebra); several additional local kernels were measured
but are not required by the final route. The original 21 F* leaves are retained
as a faithful comparison, not presented as sufficient for Sal's nested VC.

Automatic: finite collection equations after explicit unfolding, operation
case splits and pointwise specialization of equality hypotheses. Manual:
choosing the stronger equation hypotheses, proving nested-scope enumeration,
last-conflict/absorber coverage, and assembling representation adapters. There
is no automatic invariant discovery or generic VC-expansion generator here.

### Backend comparisons

`InductiveLeaves.lean` translates all **21 F* merge obligations** for each
OR-set: 42 kernel-checked proofs. These retain frozen final events, insertion
positions, timestamp/replica guards and equation hypotheses. The source map is
`inductive-source-map.json`; fourteen larger schemata are reproducibly translated
by `translate_neem_leaves.py`. The [source audit](neem-induction-audit.md)
distinguishes the F* inventory from the paper's printed table.

| Obligation family | Native checked | lean-smt checked | Lean-auto/Z3 checked | Z3 solver-only |
|---|---:|---:|---:|---:|
| Original F* merge leaves, both sets (42) | 42 | 24 | 4 | 32 |
| Additional local/freshness leaves, both sets (22) | 22 | 20 | 4 | 18 |
| Causal-delta step kernels, both sets (8) | 8 | 4 | 0 | 8 |

The original-leaf campaign contains 126 trials; the local campaign contains 66,
and the causal campaign contains 24.
Lean-auto's checked cases close through internal simplification, not checked
external-solver reconstruction. Original-leaf failures were translation or
incomplete solver responses; the two local lean-smt failures were incomplete
solver responses. Four causal lean-smt trials also returned incomplete responses.
Native Lean checked every finite equation in these campaigns.

Each backend gets identical explicit preparation: destruct operations, unfold
implementation definitions, specialize equality hypotheses at an arbitrary set
member, and normalize collection membership. The remaining solver receives no
datatype correctness lemmas. This is automation **after explicit expansion and
preparation**, not automatic discovery of the induction or its coverage proof.
`run_inductive.py` records backend calls, standard versus solver axioms,
dependencies, template/source hashes, timings and failure stages.

The root independently verified all 216 trial source/template hashes, coverage
and forbidden-dependency checks. Results and generated sources are archived in
`results/inductive-campaign.{json,tar.gz}` and
`results/local-campaign.{json,tar.gz}` and `results/causal-campaign.{json,tar.gz}`.
Six initial causal trials failed because a local `.olean` was missing; those
setup failures are archived separately in `causal-setup-failures.tar.gz`. The
table uses the reruns after building that dependency.
Native leaf audits are in `results/inductive-native-audit.json` and
`results/local-native-audit.json`.

The defeater/ghost examples are regression evidence for the **already known**
gap between Neem's original obligations and Sal's nested local VC. They are not
a new obstacle or the campaign's result. The current bridge proves additional
finite equations for that VC. Earlier exploratory modules (`InductiveBridge`,
`InductiveCoupled`, `InductiveResidual`, `InductiveCycleResidual`, and the ghost
countermodel modules) retain the derivation history; they are not needed to
assume any desired Join theorem.

Issuance-certified RGA and queue automation remains outside this campaign.
Their existing correctness proofs are unaffected; transferring this method
will require guarded expansion and preservation of issuance/reachability evidence.

## Earlier experiment: unexpanded whole VCs

The pilot closes **6 of the 10 OR-set VCs** with common finite-set normalization
and native `grind only`. They are commutativity, initialization and shared-event
redistribution for each set. The causal-delta and local-redistribution VCs remain
unsolved by the tested configurations. No complete Embedded RGA VC is closed by
the common matrix or the specialized-hint refinement.

| Pipeline | Generic-tier checked OR-set VCs / 10 | Generic-tier unchecked verdicts / 10 | Checked RGA VCs / 5 |
|---|---:|---:|---:|
| Native simp/grind | 6 | 0 | 0 |
| Lean-auto + Duper | 4 | 0 | 0 |
| lean-smt + cvc5 | 6 | 0 | 0 |
| Lean-blaster + Z3 | 0 | 2 | 0 |
| Lean-auto + Z3 | 0 | 6 | 0 |
| Lean-auto + cvc5 | 0 | 6 | 0 |

Definitions-only closes none. Initial broad helper hints add no new solved case
and sometimes break an otherwise successful translation. The separate 54-run
refinement specializes those hints to the current types/instances/prefix code;
it also closes none of its nine previously unsolved cases. These are results
under the documented preprocessing and limits, not impossibility results for
the tools or the obligations.

The initial 270-run matrix contains 27 checked attempts, 21 unchecked successful
verdicts, 217 failures and five whole-process timeouts. Counts include repeated
cases at different assistance levels. The 54 specialized attempts all fail.
Failure logs distinguish translation, solver-response, solver-timeout and
search/preprocessing issues; many never reach proof search. In particular,
these failures do not establish that a VC is false. Duper's two generic shared
cases hit the whole-process bound; lean-smt and grind close them.

**Recommendation:** use the checked native normalization as the first layer.
Keep lean-smt as a reconstructing SMT comparison, but this pilot provides no
additional VC coverage to justify making it a production dependency. Blaster
is useful for solver experiments, not production proof completion at its
current trust boundary. No solver speed ranking is claimed.

The next experiment instead constructs the finite base/step obligations of
Neem-style history induction, retaining frozen events and the merge equations
as induction hypotheses. It must prove these leaves imply the current five
VCs; merely porting F* signatures does not establish that bridge. The old
[residual map](notes-cases.md) identifies facts used by the existing direct
proofs, not invariants that the new experiment may supply to its leaf solvers.

A deliberately manually structured RGA commutativity control does close using
whitelisted sortedness/toFinset lemmas and `grind only`; it is retained in
`StructuredRGAControl.lean` and **not counted as automated whole-VC success**.
It confirms that organizing the helper applications matters. The Blaster
propositional-abstraction probe is likewise reported separately.

The six native proofs are packaged as a reusable tactic and checked alternative
in `NativeProofs.lean`. Production theorem statements and bundles are unchanged.
A claim that all five VCs are now automatic would exceed this evidence.

## Cases and evidence

`Cases.lean` contains the five `ConcreteMRDT.Raw.MergeVCs` fields for exact
OR-set, efficient OR-set, and Embedded RGA (15 obligations). Ephemeral Lean
`#check` casts verify that the copied generic propositions match the actual
structure fields definitionally. They do not supply any instance's VC proof.
`premises.json` records the explicit library/helper whitelist and exclusions.

Three assistance levels are measured:

- `definitions`: expose the datatype signature and merge definition for sets;
  remove irrelevant context for set commutativity/initialization; no added
  theorem hints. Embedded RGA retains its opaque signature at this level.
- `generic`: additionally apply finite-set extensionality and normalize union,
  intersection, difference and empty membership for OR-sets. For the three
  purely algebraic fields, remove context unused by the normalized goal.
  Embedded RGA unfolds its signature; no datatype-specific list normalization
  is silently supplied.
- `helpers`: generic preprocessing plus explicitly listed, polymorphic local
  helper facts concerning representation, membership and sortedness. These are
  substantial existing mathematical lemmas, not discovered automatically.
  Solved VC equations, Join theorems, and existing bundles are excluded.

Every row retains its generated Lean source, stdout/stderr, elapsed wall time,
axioms, direct Sal proof references, transitive Sal theorem dependencies and
source SHA-256. A successful elaboration is classified as `checked` only if
its axiom audit contains no solver/admission axiom and its dependency audit
finds no prohibited result. Solver-trusting successes are `solver_only`.
Failed Lean elaborations may generate temporary sorry terms; their exit status
prevents them being counted as successes. These files are experimental inputs,
not production imports.

The `failure_stage` field is a diagnostic classification of the log, not a
proof that the encoding or solver is incomplete. A failure never refutes the
VC (each VC already has an independent production proof).

## Reproduce

Use Lean 4.28.0 and build the existing Sal modules first:

```sh
lake build Sal.MRDTs.Paper1.GuardedRawORSetReplay Sal.MRDTs.Paper1.CertifiedRGAVCAlgebra
lake env lean experiments/vc-automation/Cases.lean
```

Initialize the isolated integrations using their READMEs:

- [Lean-auto and Duper / Z3 / cvc5](lean-auto/README.md)
- [lean-smt and native cvc5](lean-smt/README.md)

Root Lake dependencies are unchanged. Blaster uses Sal's existing pinned fork.
The standalone cvc5 executable for Lean-auto and the native cvc5 library for
lean-smt have different versions, recorded in the integration directories.
This is a comparison of usable pipelines, not a controlled solver-version race.

```sh
python3 experiments/vc-automation/run.py \
  --tools grind,blaster,auto-duper,auto-z3,auto-cvc5,smt \
  --families Exact,Efficient,Embedded \
  --tiers definitions,generic,helpers --seconds 30 \
  --out results/campaign
```

Trials run sequentially, each in a separate Lean process. Each receives a
30-second whole-process wall limit, a maximum 20-second solver limit, and
1,000,000 Lean heartbeats (Blaster internally disables heartbeats). The
20-second solver limit applies to external SMT calls; Duper/grind are bounded
by Lean resources and the outer wall limit. Wall time
includes elaboration, preprocessing, solving, proof reconstruction and audit;
Lake environment discovery occurs outside that timer. It is not solver CPU
time. No speed ranking should be inferred from a single run.

`grind only` excludes its global theorem database. `simp only` has explicit
normalization lemmas. The other tools receive local hypotheses, including
explicit helper facts at the helper tier. The transitive dependency audit
checks successes against solved-VC leakage. Generated instance proofs and
metadata-scheme law proofs can appear merely through types; direct references
are retained separately to explain them.

Initial `pilot`, `definitions`, `normalized` and `smoke` directories are harness
bring-up evidence, not the final campaign: some used opaque definitions,
pre-fix adapters or a misspelled normalization lemma. Only `campaign` uses the
final uniform protocol. The sources and logs make those distinctions auditable.

## Controls and trust boundary

Integration controls check a true implication and reject a missing-premise or
false proposition. Full-field positive controls independently establish that
the wrappers and audit can accept exact OR-set commutativity and shared VCs.
See the integration logs and `notes-cases.md`. No randomized testing is used:
this experiment measures automation on already proved, unchanged propositions.

Machine-readable results are in [campaign.json](results/campaign.json) and
[specialized.json](results/specialized.json). Exact generated sources and logs
are preserved in the matching `.tar.gz` archives. Extract them under `results/`
and run `python3 summarize.py results/campaign` from this directory to verify
source hashes and checked-proof axioms. `export_results.py` also checks full
Cartesian coverage of both experiments. Exploratory bring-up files are archived
separately and excluded from the measured totals.

## Controlled helper refinement

The initial matrix deliberately supplies the whole family helper whitelist as
polymorphic facts. This can expose translation failures unrelated to the VC.
A separate refinement fixes type/instance parameters (and RGA's prefix code)
and omits helpers for OR-set fields already closed by generic normalization:

```sh
python3 experiments/vc-automation/run.py \
  --tools grind,blaster,auto-duper,auto-z3,auto-cvc5,smt \
  --families Exact,Efficient --fields causal_delta,local_redistribute \
  --tiers helpers --helper-mode specialized --seconds 30 \
  --out results/specialized
python3 experiments/vc-automation/run.py \
  --tools grind,blaster,auto-duper,auto-z3,auto-cvc5,smt \
  --families Embedded --tiers helpers --helper-mode specialized --seconds 30 \
  --out results/specialized
```

Do not pool these attempts as repeated measurements of the original helper
configuration. Each generated source records the exact hints used.

Blaster's supplementary `lean-auto/ProbeBlaster.lean` additionally generalizes
normalized finite-set membership atoms to arbitrary propositions, then removes
the set variables. This sound but extra preprocessing avoids its `Quot`
translation failure on the commutativity example. It is a separate probe, not
silently added to the common matrix.

## Reusable checked result

`NativeProofs.lean` packages the six successful OR-set fields using one
`native_set_vc` tactic: definition unfolding, finite-set extensionality,
explicit membership simplification and `grind only`. It has no external solver
dependency and does not use an existing VC theorem. Run it with:

```sh
lake env lean experiments/vc-automation/NativeProofs.lean
```

Each exported theorem retains the original full field proposition and prints
its axiom/dependency audit. The production bundles retain their existing
proofs; the experiment supplies a checked reusable alternative rather than
introducing experimental SMT dependencies into them.

## Final validation

Both `scripts/check-paper1.sh` and `scripts/check-mrdt-refactor.sh` passed,
including 187 runtime tests and validation of 569 benchmark records. The primary
agent reran the six native proofs, structured RGA control, and all backend
positive/negative controls. The logs are in `results/verification.tar.gz`.
An independent Sol 6.1 review audited all 27 checked matrix rows for statement
fidelity, standard axioms, source hashes and absence of final-VC proof leakage.
`export_results.py` verifies the complete 270 + 54 trial coverage before export.
