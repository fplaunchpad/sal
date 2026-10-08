# Isolated lean-smt integration

Research question: can a fixed solver invocation close the five paper1 VCs without existing VC proofs? A false control closing, or a reconstructed declaration depending on `sorryAx`, refutes the stronger claim of trustworthy automation. Lean checking and per-declaration axiom audits are the formal oracle. Solver success alone does not validate the encoded VC semantics.

This Lake project uses Lean 4.28.0. `lake-manifest.json` pins all transitive dependencies. Root Sal dependencies are unchanged.

| Component | Pin |
| --- | --- |
| lean-smt | f58d19d5d0803fcccb5ccb1b4473774dd2ae9f9a |
| lean-auto | 20cd555d5b5b99c82059a8e868a4912e8101f63b |
| lean-cvc5 FFI | ef0efbf437ae79124c65557c13aa5bfcee948f80 |
| Native solver | cvc5 1.3.2 |
| Mathlib | 8f9d9cff6bd728b17a24e163c9402775d9e6a365 |

Run `lake update`, then `lake build Controls`. Run `./run-lean.sh Controls.lean`; it must pass. Run `./run-lean.sh FalseControl.lean` and `./run-lean.sh ControlMissingPremise.lean`; both must exit nonzero. These outcomes were observed on this machine. The positive proof uses only `propext`, `Classical.choice`, and `Quot.sound`.

`Preamble.lean` supplies imports/options for common benchmarks. Use `smt (timeout := some 20) [*]`, with unfolding/helper premises selected by the common harness. `integration.json` records the invocation. Append root Sal's generated `LEAN_PATH` to this project's path when importing Sal. The native plugin is `.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib` on macOS arm64.

The FFI uses a downloaded static cvc5 1.3.2 library, independently of any installed cvc5 executable. Dependency setup succeeded; lean-auto fell back from its absent release to a source build.

The tactic defaults to `trust := false` and reconstructs solver proofs in Lean. The imported dependency has a `sorry` in experimental BitVec bitblasting. Audit every successful theorem: the positive control's clean axiom set does not establish this for other proofs. Supported theories include uninterpreted functions and linear integer/real arithmetic with quantifiers. Higher-order/dependent expressions may require monomorphization or selected unfolding. No complete-VC proof or proof bundle is supplied as a hint.
