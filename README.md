# `sal`: Multi-modal Verification of Replicated Data Types

Sal is a Lean 4 framework for verifying state-based CRDTs and Mergeable Replicated Data Types (MRDTs) under replication-aware (RA) linearizability. It combines kernel-checkable automation (`dsimp + grind`), SMT-aided automation (`lean-blaster`), and AI-assisted interactive theorem proving, and it uses Lean's property-based testing (Plausible) plus a ProofWidgets-based visualizer to generate and display counterexamples when a verification condition fails. The approach builds on the F★-based Neem framework of Ramesh et al. (see the [paper](https://kcsrk.info/papers/sal_jan26.pdf) for details and references).

## Steps to run

Clone this repository, then install [elan](https://github.com/leanprover/elan) (the Lean toolchain manager). From the repo root, run `lake exe cache get` to download the prebuilt Mathlib oleans — this takes a few minutes and is required before any file will type-check in a reasonable time.

Do **not** run `lake update`: the committed `lake-manifest.json` is pinned to a working v4.26.0-compatible set, and `lake update` will resolve the `main` / `master` dependencies (Blaster, smt, batteries, aesop, etc.) to newer commits that break the build. The Lean version in `lean-toolchain` must stay at `v4.26.0`.

Open each Lean file in VS Code to run the verification conditions interactively, or run `lake lean <path-to-file.lean>` from the command line. The `run_files.sh` script checks every `.lean` file under a given directory.

## Repository layout

- [`CaseStudies/Interfaces/`](CaseStudies/Interfaces) — Sal's decidable `set` and `map` interfaces (`Set_extended`, `Map_extended`).
- [`CaseStudies/Tactics/`](CaseStudies/Tactics) — the `sal` tactic (`Sal.lean`) and usage examples (`SalExample.lean`).
- [`CaseStudies/Fstar_like_implementations/`](CaseStudies/Fstar_like_implementations) — CRDT and MRDT implementations written in the F★-style signature used in the paper, split into `CRDTs/` and `MRDTs/`.
- [`CaseStudies/Lean_based_implementations/`](CaseStudies/Lean_based_implementations) — alternative implementations using Lean's native `Set` type.
- `CaseStudies/WriterMonad_*.lean` — logging-monad traces used by the ProofWidgets-based counterexample visualizer.
- [`CaseStudies/Sandbox/`](CaseStudies/Sandbox) — scratch / exploratory files kept for reference; not part of the evaluated benchmark suite.

## Data structures implemented and description

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


## Counterexample generation using Plausible

The enable-wins flag MRDT has a known subtle bug: it fails the `inter_right_1op` VC. Sal uses [Plausible](https://github.com/leanprover-community/plausible) to automatically generate small counterexamples rather than requiring the developer to construct one by hand. See [`CaseStudies/Fstar_like_implementations/MRDTs/SAL/en_wins_flag.lean`](CaseStudies/Fstar_like_implementations/MRDTs/SAL/en_wins_flag.lean) for the decidability witnesses and Plausible invocation. To visualize the counterexample's execution trace, we use a [logging-style writer monad](https://leanprover.github.io/functional_programming_in_lean/monads.html#logging) to record each intermediate state; [`CaseStudies/WriterMonad_ENflag.lean`](CaseStudies/WriterMonad_ENflag.lean) shows the computation path rendered as HTML via ProofWidgets.

## Proofs generated using Harmonic's Aristotle

The remaining VCs that fall back to interactive theorem proving in the table above were discharged using [Aristotle](https://aristotle.harmonic.fun/dashboard/docs/overview). All benchmarks in the table now have complete proofs.
