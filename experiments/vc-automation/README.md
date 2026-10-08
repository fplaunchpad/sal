# Five-VC automation experiment

Question: can Sal's existing five merge VCs be discharged automatically from
stated premises and datatype definitions, and what additional assistance is
necessary? This experiment preserves the original polymorphic propositions,
implementations, representation relations, and production proofs. It does not
attempt invariant discovery or the sequential-specification bridge.

## Measured result and recommendation

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

The next useful automation work is a checked transformation from represented
states to pointwise freshness/coverage facts, followed by collection algebra.
For RGA it also needs the sorted-list/toFinset conversion. The existing
representations and issuance invariants are supplied; this is invariant
exploitation, not invariant discovery. The [residual map](notes-cases.md)
identifies the exact missing facts and compares these whole obligations with
Neem's smaller generated induction VCs.

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
