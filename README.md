# `sal`: Multi-modal Verification of Replicated Data Types

Sal is a Lean 4 framework for verifying state-based CRDTs and Mergeable Replicated Data Types (MRDTs) under replication-aware (RA) linearizability. Rather than discharging every verification condition with a single backend, Sal stages automation by *trustworthiness*: it first attempts kernel-verified proof reconstruction, falls back to an SMT backend only when that fails, and finally hands remaining obligations to an AI-assisted interactive theorem prover — all while keeping the trusted computing base (TCB) as small as the VC allows. When a VC is in fact invalid, Sal uses Plausible (property-based testing) together with a ProofWidgets-based visualizer to turn the failure into an inspectable counterexample execution trace.

The approach builds on the F★-based **Neem** framework of Soundarapandian, Nagar, Rastogi, and Sivaramakrishnan (OOPSLA 2025), which reduces RA-linearizability for a data type to a fixed set of VCs over `do`, `merge`, and `rc`. Sal is the Lean port of that reduction plus a multi-modal tactic, counterexample pipeline, and custom decidable set/map interfaces that make `grind` effective on RDT goals.

## Paper

Pranav Ramesh, Vimala Soundarapandian, KC Sivaramakrishnan. *Sal: Multi-modal Verification of Replicated Data Types.*

- PDF: <https://kcsrk.info/papers/sal_jan26.pdf>

## Headline result

Across the 13 case studies (312 VCs total; 24 VCs per RDT), Sal discharges:

- **215 VCs (68.9%)** with kernel-verified automation (`dsimp + grind`) — TCB not enlarged.
- **87 VCs (27.9%)** with `lean-blaster` (SMT-aided, enlarges the TCB to include Z3).
- **9 VCs (3.0%)** via interactive proving, all closed using Harmonic's Aristotle, whose outputs are kernel-checked so the TCB is still not enlarged.

## The `sal` tactic

The tactic lives in [`CaseStudies/Tactics/Sal.lean`](CaseStudies/Tactics/Sal.lean) and tries three strategies in order, stopping at the first one that succeeds:

1. **`dsimp` + `grind`** — lightweight SMT-style automation with proof reconstruction; the result is a kernel-checkable proof term. This stage is preferred because it does not enlarge the TCB. We deliberately skip `aesop` at this stage because its verification times on these RDT goals were prohibitive.
2. **`lean-blaster`** — encodes the goal to Z3. More powerful (especially for higher-order functions and lambdas) but sacrifices proof reconstruction, so the TCB grows to include the SMT solver. Invoked with a wall-clock timeout (default 30 s) so a stuck goal cannot hang.
3. **`dsimp` + `aesop` + `all_goals (try grind)`** — a broader proof-search fallback. Remaining goals are then typically closed interactively with tactics produced by Aristotle.

The tactic takes a heartbeat budget (default 400 000) that caps Lean-side elaboration across all three stages, and a separate `smtTimeoutSec` budget (default 30 s) for the SMT stage. See the docstring in `Sal.lean` for how to tune them.

Minimal example (see [`CaseStudies/Tactics/SalExample.lean`](CaseStudies/Tactics/SalExample.lean) for more):

```lean
import CaseStudies.Tactics.Sal

example (a b : Nat) : a + b = b + a := by sal
```

## Custom set and map interfaces

Lean's standard `Set α := α → Prop` is convenient for hand-written proofs but fights automation (membership is a proposition, not a Boolean). Sal introduces *decidable* versions where `grind` can compute:

```lean
abbrev set (a : Type) [DecidableEq a] := a → Bool

structure map (key : Type) [DecidableEq key] (value : Type) where
  mappings : key → value
  domain   : set key
```

Every lemma on these types is annotated with `@[simp, grind]` and (where useful) a `grind_pattern`, building a domain-specific rewrite database that lets `grind` discharge set/map goals without SMT assistance. Files live in [`CaseStudies/Interfaces/`](CaseStudies/Interfaces).

## Counterexample generation and visualization

When automation fails because the implementation is actually wrong, Sal makes the failure inspectable rather than opaque:

- **Plausible** generates concrete counterexamples for decidable VCs. The canonical demo is the enable-wins flag MRDT, which contains a known bug from prior work (the `inter_right_1op` VC fails); Plausible rediscovers a minimal failing execution automatically. See [`CaseStudies/Fstar_like_implementations/MRDTs/SAL/Enable_Wins_Flag_MRDT.lean`](CaseStudies/Fstar_like_implementations/MRDTs/SAL/Enable_Wins_Flag_MRDT.lean).
- **ProofWidgets trace visualizer.** A [logging-style writer monad](https://leanprover.github.io/functional_programming_in_lean/monads.html#logging) instruments `do` and `merge` to record intermediate states, and a ProofWidgets component renders the LCA, left branch, right branch, and merge result as a vertical diagram (paper Figure 3). See [`CaseStudies/WriterMonad_ENflag.lean`](CaseStudies/WriterMonad_ENflag.lean) and the other `WriterMonad_*.lean` files.
- **Universe tracking for functional sets.** Since Sal's `set` type is a `α → Bool` predicate and may be infinite, the visualizer augments abstract sets with a concrete `HashSet` of elements added or removed during execution, so the state can be displayed concretely (paper §3.3).

## Benchmark results

Per paper Table 2 (DG = `dsimp + grind`; LB = `lean-blaster`; ITP = Aristotle-assisted interactive proof):

| **RDT**                          | **DG** | **LB** | **ITP** |
|----------------------------------|:------:|:------:|:-------:|
| Increment-only counter MRDT      | 24     | 0      | 0       |
| PN-counter MRDT                  | 24     | 0      | 0       |
| OR-set MRDT                      | 3      | 21     | 0       |
| Enable-Wins Flag MRDT            | 9      | 14     | 0       |
| Efficient OR-Set MRDT            | 2      | 22     | 0       |
| Grows-only set MRDT              | 24     | 0      | 0       |
| Grows-only map MRDT              | 22     | 0      | 2       |
| Replicated Growable Array MRDT   | 15     | 9      | 0       |
| Multi-valued Register MRDT       | 24     | 0      | 0       |
| Increment-only counter CRDT      | 24     | 0      | 0       |
| PN-counter CRDT                  | 16     | 2      | 6       |
| Multi-Valued Register CRDT       | 24     | 0      | 0       |
| OR-set CRDT                      | 4      | 19     | 1       |

Two patterns from the paper: MRDTs generally need less SMT than CRDTs because three-way merges express causality directly, and map-based reasoning stresses current Lean automation more than set-based reasoning (the 8 remaining ITP goals are concentrated in map-heavy RDTs).

## Steps to run

Clone this repository, then install [elan](https://github.com/leanprover/elan) (the Lean toolchain manager). `elan` will read `lean-toolchain` and install Lean `v4.28.0` on first use. From the repo root, run `lake exe cache get` to download the prebuilt Mathlib oleans — this takes a few minutes and is required before any file will type-check in a reasonable time.

`lake update` is safe to run on this branch — the `lakefile.toml` pins `mathlib` to `v4.28.0` and pins `Blaster` to the `chore-bump-lean-4.28` branch of [`kayceesrk/Lean-blaster`](https://github.com/kayceesrk/Lean-blaster), a fork whose upstream (`input-output-hk/Lean-blaster`) does not yet have a v4.28-compatible branch. Once the upstream catches up we will switch back.

Open each Lean file in VS Code to run the verification conditions interactively, or run `lake lean <path-to-file.lean>` from the command line. The `run_files.sh` script checks every `.lean` file under a given directory.

## Repository layout

- [`CaseStudies/Interfaces/`](CaseStudies/Interfaces) — Sal's decidable `set` and `map` interfaces (`Set_Extended`, `Map_Extended`, `Map_Extended_With_Lean_Set`).
- [`CaseStudies/Tactics/`](CaseStudies/Tactics) — the `sal` tactic (`Sal.lean`) and usage examples (`SalExample.lean`).
- [`CaseStudies/Fstar_like_implementations/`](CaseStudies/Fstar_like_implementations) — CRDT and MRDT implementations in the `⟨Σ, σ₀, do, merge, rc⟩` signature used in the paper (§2), split into `CRDTs/` and `MRDTs/` — these contain the thirteen benchmarks reported in Table 2. The `Counterexample_Visualization/` subdirectory holds the logging-monad traces (`WriterMonad_*.lean`) that feed the ProofWidgets visualizer.
- [`CaseStudies/Sandbox/New_CRDTs/`](CaseStudies/Sandbox/New_CRDTs) — eleven additional state-based CRDTs (LWW / MAX / MIN registers, LWW Element Set, LWW Map, MAX Map, Grow-Only Set / Multiset, Shopping Cart, Priority Queue, and an Add-Win CRPQ adapted from Zhang et al. 2023). Not part of the paper's evaluation; serves as a stress-test of the `sal` tactic beyond the original benchmarks.

## License

MIT; see [LICENSE](LICENSE).
