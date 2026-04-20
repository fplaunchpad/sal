# `sal`: Multi-modal Verification of Replicated Data Types

This repository contains a port of various CRDTs and MRDTs from the Neem framework to Lean. It also comes equipped with a custom tactic called `sal` and a counterexample generation and visualization framework. 

## Steps to run

Clone this repository, then install [elan](https://github.com/leanprover/elan) (the Lean toolchain manager). From the repo root, run `lake exe cache get` to download the prebuilt Mathlib oleans — this takes a few minutes and is required before any file will type-check in a reasonable time.

Do **not** run `lake update`: the committed `lake-manifest.json` is pinned to a working v4.26.0-compatible set, and `lake update` will resolve the `main` / `master` dependencies (Blaster, smt, batteries, aesop, etc.) to newer commits that break the build. The Lean version in `lean-toolchain` must stay at `v4.26.0`.

The various proofs are in the [Neem](CaseStudies/Neem) directory. Open each Lean file in VS Code to run the verification conditions interactively, or run `lake lean <path-to-file.lean>` from the command line. The `run_files.sh` script checks every `.lean` file under a given directory.

# Data structures implemented and description

| **RDT**                          | **dsimp + grind** | **Lean Blaster** | **Fallback to ITP** |
|----------------------------------|:------:|:------:|:-------------------:|
| Increment-only counter MRDT      | 24     | 0      | 0                   |
| PN-counter MRDT                  | 24     | 0      | 0                   |
| OR-set MRDT                      | 3      | 21     | 0                   |
| Enable-Wins Flag MRDT            | 9      | 14     | 0                   |
| Efficient OR-Set MRDT            | 2      | 22     | 0                   |
| Grows-only set MRDT              | 24     | 0      | 0                   |
| Grows-only map MRDT              | 22     | 0      | 2                   |
| Replicated Growable Array MRDT   | 15     | 9      | 0                   |
| Multi-valued Register MRDT       | 24     | 0      | 0                   |
| Increment-only counter CRDT      | 24     | 0      | 0                   |
| PN-counter CRDT                  | 16     | 2      | 6                   |
| Multi-Valued Register CRDT       | 24     | 0      | 0                   |
| OR-set CRDT                      | 4      | 19     | 1                   |


# Counterexample generation using Plausible

Our implementation of the `en-wins flag` was erroneous, and it did not pass the `inter_right_1op` VC. Earlier, the counterexample needed to be worked out manually, but we can now automatically generate small counter-examples. The [Plausible](https://github.com/leanprover-community/plausible) generator was used to generate minimal examples. The section of code can be checked out [here](https://github.com/pranavramesh2003/Neem_Loom/blob/master/CaseStudies/Neem/en_wins_flag.lean#L312). We prove that both the pre and post conditions are decidable under a suitable upper bound, and generate counter examples. Subsequently, we use [Logging](https://leanprover.github.io/functional_programming_in_lean/monads.html#logging)-style monads to derive the computation tree for the left and right hand sides of the `ensures` equality. [This file](CaseStudies/Neem/WriterMonad_ENflag.lean) shows the computation path logged as a list and the subsequent visualization in HTML. 

# Proofs generated using Harmonic's Aristotle

Subseqent attempts to verify the VCs which fallback to ITP were successful using the [Aristotle](https://aristotle.harmonic.fun/dashboard/docs/overview) framework. Now, all of the data structures mentioned in the table above have complete proofs. 