# Isolated lean-auto integration

Research question: can a fixed automation invocation close the five paper1 VCs without using the existing VC proofs? A false control closing, or an additional proof axiom in a purported reconstructed proof, falsifies the stronger claim of trustworthy automation. The formal oracle is Lean 4.28 checking the resulting declaration and `#print axioms`; SMT success alone is solver evidence.

Dependencies are fixed by `lakefile.lean` and `lake-manifest.json`. The root Sal Lake project is unchanged.

| Component | Revision/version |
| --- | --- |
| Lean | 4.28.0 |
| lean-auto | 1f8a3b2f31366ec7da2a160e634004c52be6631e |
| Duper | 82606cd26168cb5e30e8e47375f0b3f091e769e0 |
| Batteries | 495c008c3e3f4fb4256ff5582ddb3abf3198026f |
| Z3 executable | 4.16.0, `/opt/homebrew/bin/z3` |
| cvc5 executable | 1.4.2, git 282d5e0 |

Run `lake update` and `lake build VCAuto` here to initialize the project. Duper's release fetch fell back to a successful source build. The adapter in `VCAuto.lean` follows the upstream README interface for this revision.

Use the matching `PreambleDuper.lean`, `PreambleZ3.lean`, or `PreambleCvc5.lean` before the common benchmark statements. The tactic is `auto`; explicit unfold directives use `auto u[definition,...]`. The harness controls all additional hints. Run `lake env lean FILE.lean` from this directory. When importing Sal, append the root project's Lean path to this project's generated `LEAN_PATH`.

Standalone cvc5 is downloaded from `https://github.com/cvc5/cvc5/releases/download/cvc5-1.4.2/cvc5-macOS-arm64-static.zip` and extracted to `/tmp/sal-vc-auto-cvc5-dist`. Add `/tmp/sal-vc-auto-cvc5-dist/cvc5-macOS-arm64-static/bin` to `PATH` to enable it. The executable and dependencies are deliberately outside production sources.

The native Duper backend reconstructs a proof. Inspect the axiom output for each successful declaration. Standard axioms such as `propext`, `Classical.choice`, and `Quot.sound` are distinguished from custom assumptions.

SMT preambles explicitly set `auto.smt.trust true`. This pinned revision cannot reconstruct the SMT proof and closes successful goals using the custom axiom `Auto.Solver.SMT.autoSMTSorry`. Such results count as SMT `unsat` evidence, never kernel reconstructed proof. Both SMT preambles trace the solver response and limit solver time to 20 seconds. False controls must produce `sat`/failure, not a closed theorem.

`ControlDuper.lean`, `ControlZ3.lean`, and `ControlCvc5.lean` exercise a positive implication chain and a negative missing-premise case. Expected results are independent of the implementation. No existing VC theorem is supplied as a hint.

Integration controls passed for all three backends. Duper's positive control uses only `[propext, Classical.choice, Quot.sound]`. Both SMT positive controls also use `autoSMTSorry`. Z3 traces `Unsat` for the positive and `Sat` for the negative. cvc5's positive traces `Unsat`; its negative proof attempt fails as required (the pinned adapter suppresses the model parse diagnostic).

cvc5 compatibility fix: set `auto.smt.dumpHints.limitedRws false`. The pinned lean-auto default otherwise passes `--hints-only-rw-insts`, which cvc5 1.4.2 rejects. The initial positive control then failed with `Incomplete input`; that was an integration error, not a logical outcome. The final cvc5 preamble contains the fix.

Downloaded cvc5 ZIP SHA-256: `24397f7d022e755876ca836193d4c5f9c1d4326f0f6c01f7d7fc1ddd6bc5096c`.

## Actual merge-commutativity probe

`ProbeDuper.lean`, `ProbeZ3.lean`, and `ProbeCvc5.lean` retain the common `VCAutomation.Exact.merge_comm` statement unchanged. All three succeed after explicit model-definition reduction, removal of irrelevant replay-context hypotheses, finite-set extensionality, and membership normalization:

```lean
unfold VCAutomation.Exact.merge_comm VCAutomation.merge_comm_goal
intro C E₁ E₂ l a b h₁ h₂ h₃ h₄ h₅ h₆ h₇
clear h₁ h₂ h₃ h₄ h₅ h₆ h₇ C E₁ E₂
dsimp only [Sal.MRDTs.Paper1.ORSet.D, Sal.MRDTs.Paper1.ORSet.merge]
apply Finset.ext
intro x
simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
auto
```

This exposes a propositional membership equivalence to the backend. It uses generic Finset facts, no existing VC theorem. The Duper proof has only standard axioms. Z3 and cvc5 trace `Unsat` and add `autoSMTSorry` as documented above. Retained `.log` files record these outcomes. The opaque baseline's SMT translation produced a duplicate sort declaration for the model's projected application-operation type; reducing the goal and removing irrelevant context avoids that translation defect.

## Blaster controls and quotient isolation

Run `lake env lean experiments/vc-automation/lean-auto/ControlBlaster.lean` from the root project. Its positive implication control reports `Valid` and uses `sorryAx`. Its `#guard_msgs` negative control requires the expected falsification and counterexample `P=true`, `Q=false`. Both checks pass.

`ProbeBlaster.lean` keeps the same actual Exact merge-commutativity goal and finite-set normalization as above. Blaster cannot translate the remaining Finset quotient context directly. The following additional proof-preserving propositional abstraction removes that translation barrier and reports `Valid`:

```lean
dsimp only [Sal.MRDTs.Paper1.ORSet.D] at l a b
generalize hl : (x ∈ l) = L
generalize ha : (x ∈ a) = A
generalize hb : (x ∈ b) = B
clear hl ha hb l a b x
rename_i inst
clear inst α
blaster (timeout: 10) (random-seed: 1)
```

The resulting declaration uses `sorryAx` alongside standard Lean axioms. This is solver evidence, not proof reconstruction. The abstraction proves a stronger propositional tautology for arbitrary membership truth values; it changes neither the public VC statement nor any model definition. Logs are retained next to both files. No campaign or runner change was made.
