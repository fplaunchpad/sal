# `sal`: Multi-modal Verification of Replicated Data Types

Sal is a Lean 4 framework for verifying state-based CRDTs and Mergeable Replicated Data Types (MRDTs) under replication-aware (RA) linearizability. Rather than discharging every verification condition with a single backend, Sal stages automation by *trustworthiness*: it first attempts kernel-verified proof reconstruction, falls back to an SMT backend only when that fails, and finally hands remaining obligations to an AI-assisted interactive theorem prover — all while keeping the trusted computing base (TCB) as small as the VC allows. When a VC is in fact invalid, Sal uses Plausible (property-based testing) together with a ProofWidgets-based visualizer to turn the failure into an inspectable counterexample execution trace.

The approach builds on the F★-based **Neem** framework of Soundarapandian, Nagar, Rastogi, and Sivaramakrishnan (OOPSLA 2025), which reduces RA-linearizability for a data type to a fixed set of VCs over `do`, `merge`, and `rc`. Sal is the Lean port of that reduction plus a multi-modal tactic, counterexample pipeline, and custom decidable set/map interfaces that make `grind` effective on RDT goals.

## What's verified

The suite currently contains **29 RDTs** — 18 CRDTs and 11 MRDTs — with all 24 RA-linearizability VCs closed on every one (696 kernel-verified VCs in total). Everything is checked on Lean `v4.28.0` against the `chore-bump-lean-4.28` branch of a [Blaster fork](https://github.com/kayceesrk/Lean-blaster).

**CRDTs** ([`Sal/CRDTs/`](Sal/CRDTs)):

- Registers & counters: `Increment_Only_Counter`, `PN_Counter`, `LWW_Register`, `MAX_Register`, `MIN_Register`, `Multi_Valued_Register`, `Bounded_Counter` (Sypytkowski 2019 / Balegas et al. 2015 — PN-counter plus a sparse per-replica-pair `transfers` map for quota redistribution).
- Sets & maps: `OR_Set`, `Grow_Only_Set`, `Grow_Only_Multiset`, `LWW_Element_Set`, `LWW_Map`, `MAX_Map`.
- Sequences & structured data: `RGA` (Replicated Growable Array — the sequence CRDT underlying Automerge / Yjs, in its state-based formulation as a grow-only `Map OpId (char, afterId, deleted)`), `Peritext` (Litt et al. CSCW 2022 — rich text = RGA + formatting marks represented as a flat `set AnchorAttachment`), `Shopping_Cart`, `Priority_Queue_Insert_Only`, `Add_Win_Priority_Queue` (adapted from Zhang et al. 2023).

**MRDTs** ([`Sal/MRDTs/`](Sal/MRDTs)):

- `Increment_Only_Counter`, `PN_Counter`, `Multi_Valued_Register`, `Grow_Only_Set`, `Grow_Only_Map`, `OR_Set`, `OR_Set_Efficient`, `Replicated_Growable_Array`, `Add_Win_Priority_Queue` (adapted from Zhang et al. 2023 — drops the CRDT's tombstone set since the LCA handles Add-Wins directly, leaving `set (add_ts, elem, value) × set (inc_ts, elem, amount)`), `Peritext` (Litt et al. CSCW 2022 — RGA substrate plus `set AnchorAttachment`; RGA's tombstones are structurally load-bearing since later inserts reference earlier char ids, so this MRDT keeps all components grow-only and uses pointwise-union merge, mirroring `RGA_MRDT`), `Enable_Wins_Flag` (intentionally buggy — drives the Plausible counterexample demo; the bug manifests on `inter_right_1op`).

## The `sal` tactic

The tactic lives in [`Sal/Tactic/Sal.lean`](Sal/Tactic/Sal.lean) and tries three strategies in order, stopping at the first one that succeeds:

1. **`dsimp` + `grind`** — lightweight SMT-style automation with proof reconstruction; the result is a kernel-checkable proof term. This stage is preferred because it does not enlarge the TCB. We deliberately skip `aesop` at this stage because its verification times on these RDT goals were prohibitive.
2. **`lean-blaster`** — encodes the goal to Z3. More powerful (especially for higher-order functions and lambdas) but sacrifices proof reconstruction, so the TCB grows to include the SMT solver. Invoked with a wall-clock timeout (default 30 s) so a stuck goal cannot hang.
3. **`dsimp` + `aesop` + `all_goals (try grind)`** — a broader proof-search fallback. Remaining goals are then typically closed interactively with tactics produced by Harmonic's Aristotle, whose outputs are kernel-checked so the TCB is still not enlarged.

Stages 1 and 3 are guarded against `sorryAx` in the resulting proof term: aesop's default mode can otherwise close a goal with a silent `sorry` placeholder. Stage 2 is intentionally *not* guarded, because Blaster trusts Z3's "valid" verdict via `MVarId.admit` — that is Blaster's TCB-enlarging mechanism.

The tactic takes a heartbeat budget (default 400 000) that caps Lean-side elaboration across all three stages, and a separate `smtTimeoutSec` budget (default 30 s) for the SMT stage. See the docstring in `Sal.lean` for how to tune them.

Minimal example (see [`Sal/Tactic/SalExample.lean`](Sal/Tactic/SalExample.lean) for more):

```lean
import Sal.Tactic.Sal

example (a b : Nat) : a + b = b + a := by sal
```

Many post-paper CRDTs in the suite are proved with a uniform kernel-verifiable pattern — `rcases` over the operation family, `refine ⟨?_, …, ?_⟩` to split the state's components, then `simp +decide [*]` and `grind` — and avoid Blaster entirely. A few stubborn VCs still need Blaster or an Aristotle-assisted intermediate lemma (e.g. `LWW_Map_CRDT` uses `merge_do_lex_max`); those calls stay inside the three-stage pipeline. For the full recipe of translating an op-based CRDT into Sal's state-based signature and closing the 24 VCs, see [`docs/porting-op-based-crdts.md`](docs/porting-op-based-crdts.md).

## Custom set and map interfaces

Lean's standard `Set α := α → Prop` is convenient for hand-written proofs but fights automation (membership is a proposition, not a Boolean). Sal introduces *decidable* versions where `grind` can compute:

```lean
abbrev set (a : Type) [DecidableEq a] := a → Bool

structure map (key : Type) [DecidableEq key] (value : Type) where
  mappings : key → value
  domain   : set key
```

Every lemma on these types is annotated with `@[simp, grind]` and (where useful) a `grind_pattern`, building a domain-specific rewrite database that lets `grind` discharge set/map goals without SMT assistance. Files live in [`Sal/Interfaces/`](Sal/Interfaces).

The Boolean-predicate representation is grind-friendly only as a *top-level* state component. Nesting a `set` inside a map value — e.g. `map K (set V)` — forces grind to prove function equality via `funext` and typically defeats it. Where possible, flatten: represent `map K (set V)` as `set (K × V)`. The Peritext CRDT is the clearest example in the suite: its formatting marks were originally a `map (OpId × Bool) (set MarkOp)`, which left 5 of 24 VCs stuck; flattening to a top-level `set AnchorAttachment` closes all 24.

## Counterexample generation and visualization

When automation fails because the implementation is actually wrong, Sal makes the failure inspectable rather than opaque:

- **Plausible** generates concrete counterexamples for decidable VCs. The canonical demo is the Enable-Wins Flag MRDT, which contains a known bug from prior work (the `inter_right_1op` VC fails); Plausible rediscovers a minimal failing execution automatically. See [`Sal/Counterexample_Visualization/WriterMonad_Enable_Wins_Flag.lean`](Sal/Counterexample_Visualization/WriterMonad_Enable_Wins_Flag.lean).
- **ProofWidgets trace visualizer.** A [logging-style writer monad](https://leanprover.github.io/functional_programming_in_lean/monads.html#logging) instruments `do` and `merge` to record intermediate states, and a ProofWidgets component renders the LCA, left branch, right branch, and merge result as a vertical diagram. See [`Sal/Counterexample_Visualization/`](Sal/Counterexample_Visualization).
- **Universe tracking for functional sets.** Since Sal's `set` type is a `α → Bool` predicate and may be infinite, the visualizer augments abstract sets with a concrete `HashSet` of elements added or removed during execution, so the state can be displayed concretely.

## Steps to run

Clone this repository, then install [elan](https://github.com/leanprover/elan) (the Lean toolchain manager). `elan` will read `lean-toolchain` and install Lean `v4.28.0` on first use. From the repo root, run `lake exe cache get` to download the prebuilt Mathlib oleans — this takes a few minutes and is required before any file will type-check in a reasonable time.

`lake update` is safe to run — `lakefile.toml` pins `mathlib` to `v4.28.0` and pins `Blaster` to the `chore-bump-lean-4.28` branch of [`kayceesrk/Lean-blaster`](https://github.com/kayceesrk/Lean-blaster), a fork whose upstream (`input-output-hk/Lean-blaster`) does not yet have a v4.28-compatible branch. Once the upstream catches up we will switch back.

Open each Lean file in VS Code to run the verification conditions interactively, or run `lake lean <path-to-file.lean>` from the command line. The `run_files.sh` script checks every `.lean` file under a given directory.

## Interactive playgrounds

Browser demos for every RDT in the suite live in [`demos/`](demos) (Vite + React + TypeScript, one hand-ported module per RDT). All 29 RDTs have a playground — 18 CRDTs + 10 MRDTs.

- **CRDT playgrounds** spin up three replicas, let you apply local ops per replica, and merge any pair directionally (source → target, like `git merge`). There's also a "Merge all" button that folds every replica's state into a single join and assigns it back, so you can watch replicas snap to the same value in one click. Toggle **Show concrete state** to expose the lattice representation.
- **MRDT playgrounds** organise history like git. Every local op creates a 1-parent commit; every merge creates a 2-parent commit with the LCA computed from the DAG (BFS on ancestors). A toggleable SVG history graph shows per-replica lanes with colour-coded commits (op commits solid, merge commits dashed, HEADs ringed thicker); click any past commit to inspect its full state.
- **Lattice-law invariants** are property-checked with [fast-check](https://fast-check.dev/) per RDT: CRDTs get idempotence / commutativity / associativity / strong convergence; MRDTs get left identity / right identity / commutativity (the MRDT `merge(l,a,a) ~ a` analog is NOT a law — the closed-form counter MRDT violates it by design; MRDTs only promise convergence given a coherent history DAG, which the playground supplies at runtime).

```sh
cd demos
npm install
npm run dev       # http://localhost:5173
npm run test      # 28 fast-check suites, ~1.5 s
npm run build     # TS + Vite production bundle
```

See [`demos/README.md`](demos/README.md) for the `CRDTSpec` / `MRDTSpec` interfaces, file layout, and deployment. [`.github/workflows/demos-deploy.yml`](.github/workflows/demos-deploy.yml) publishes to GitHub Pages on every push to `main` that touches `demos/**`.

## Repository layout

- [`Sal/Interfaces/`](Sal/Interfaces) — Sal's decidable `set` and `map` interfaces (`Set_Extended`, `Map_Extended`, `Map_Extended_With_Lean_Set`).
- [`Sal/Tactic/`](Sal/Tactic) — the `sal` tactic (`Sal.lean`) and usage examples (`SalExample.lean`).
- [`Sal/CRDTs/`](Sal/CRDTs) — 18 state-based CRDTs in the `⟨Σ, σ₀, do, merge, rc⟩` signature.
- [`Sal/MRDTs/`](Sal/MRDTs) — 11 state-based MRDTs.
- [`Sal/Counterexample_Visualization/`](Sal/Counterexample_Visualization) — the `WriterMonad_*.lean` logging-monad traces that feed the ProofWidgets visualizer.
- [`demos/`](demos) — Vite + React + TypeScript playgrounds, one per RDT. CRDT demos do two-way merge; MRDT demos maintain a git-style commit DAG with LCA-driven three-way merge and a toggleable history visualisation.
- [`docs/porting-op-based-crdts.md`](docs/porting-op-based-crdts.md) — recipe for porting a new op-based CRDT into Sal's state-based signature.

## Paper

Pranav Ramesh, Vimala Soundarapandian, KC Sivaramakrishnan. *Sal: Multi-modal Verification of Replicated Data Types.*

- PDF: <https://kcsrk.info/papers/sal_jan26.pdf>

The paper evaluates Sal on 13 RDTs (4 CRDTs + 9 MRDTs), 312 VCs total (24 per RDT). The breakdown across the three stages (DG = `dsimp + grind`; LB = `lean-blaster`; ITP = Aristotle-assisted interactive proof):

- **215 VCs (68.9%)** via DG — TCB not enlarged.
- **87 VCs (27.9%)** via LB — TCB enlarged to include Z3.
- **9 VCs (3.0%)** via ITP, all closed using Aristotle, whose outputs are kernel-checked — TCB not enlarged.

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

Since publication the suite has grown from 13 to 29 RDTs, and most of the added CRDTs were proved with the uniform kernel-verifiable pattern described under *The `sal` tactic*, without invoking Blaster for the majority of VCs. A refreshed DG/LB/ITP breakdown across all 29 RDTs is future work. The [`papoc2026`](https://github.com/kayceesrk/sal/tree/papoc2026) branch snapshots the repo at the paper-artifact state.

## License

MIT; see [LICENSE](LICENSE).
