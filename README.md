# `sal`: Multi-modal Verification of Replicated Data Types

Sal is a Lean 4 framework for verifying state-based CRDTs and Mergeable Replicated Data Types (MRDTs) under replication-aware (RA) linearizability. Rather than discharging every verification condition with a single backend, Sal stages automation by *trustworthiness*: it first attempts kernel-verified proof reconstruction, falls back to an SMT backend only when that fails, and finally hands remaining obligations to an AI-assisted interactive theorem prover — all while keeping the trusted computing base (TCB) as small as the VC allows. When a VC is in fact invalid, Sal uses Plausible (property-based testing) together with a ProofWidgets-based visualizer to turn the failure into an inspectable counterexample execution trace.

The approach builds on the F★-based **Neem** framework of Soundarapandian, Nagar, Rastogi, and Sivaramakrishnan (OOPSLA 2025), which reduces RA-linearizability for a data type to a fixed set of VCs over `do`, `merge`, and `rc`. Sal is the Lean port of that reduction plus a multi-modal tactic, counterexample pipeline, and custom decidable set/map interfaces that make `grind` effective on RDT goals.

## What's verified

The suite currently contains **29 RDTs** — 17 CRDTs and 12 MRDTs — with all 24 RA-linearizability VCs closed on every RDT the standard VC schema applies to. Two MRDTs sit outside that count for different reasons: `Enable_Wins_Flag_known_broken` is an intentionally-buggy demo fixture, and the tombstone-free RGA is *provably outside the schema* (its commutation only holds conditioned on reachable states) — it instead carries a direct, kernel-checked end-to-end theorem: RA-linearizability **up to observational equivalence** at every reachable configuration, under an honest-delivery assumption (see the metatheory entry below). That's **648 VCs** for state convergence (27 × 24), of which the vast majority are **kernel-checked** (no TCB-enlarging admits) and a small residue of stage-2 Blaster-admits remain in a few files (`OR_Set_MRDT`, `OR_Set_Efficient_MRDT`, `Add_Win_Priority_Queue_MRDT`, `Multi_Valued_Register_MRDT`) — validated by Z3 via the `sal` tactic's SMT stage but not yet kernel-reconstructed.

**Every RDT** carries a `*_ReadSide.lean` companion (and a `*_SPOT.lean` of small concrete-execution tests) alongside its `*_CRDT.lean` / `*_MRDT.lean`. The Tier-C RDTs (`Peritext`, `RGA`, `Add_Win_Priority_Queue`, `OR_Set` plain and efficient, `Multi_Valued_Register`, `LWW_Element_Set`) carry substantive intent-preservation theorems matching paper claims; the Tier-A RDTs carry mechanical 30–60 line files documenting the obvious read so a reader can confirm at a glance that it is in fact obvious. Per-RDT crosswalks for the Tier-C papers:

- [`docs/peritext-vs-paper.md`](docs/peritext-vs-paper.md) — Litt et al. CSCW 2022, Ex 1 / 2 / 3 / 5 / 7 / 8 intent-preservation.
- [`docs/rga-vs-paper.md`](docs/rga-vs-paper.md) — Roh et al. JPDC 2011, causal-order preservation, tombstone monotonicity, deterministic concurrent-insert tiebreak.
- [`docs/aw-crpq-vs-paper.md`](docs/aw-crpq-vs-paper.md) — Zhang et al. Internetware 2023, Add-wins headline + LWW innate + acquired-Σ + `get_max`.
- [`docs/or-set-vs-paper.md`](docs/or-set-vs-paper.md) — Shapiro et al. INRIA RR-7506, Add-Wins on lookup with sequential-Add-then-Remove extinguishment.
- [`docs/mvr-vs-paper.md`](docs/mvr-vs-paper.md) — Shapiro et al. INRIA RR-7506 §3.2.2, classical replace-on-write semantics with concurrent-writes-both-survive + sequential-writes-supersede.
- [`docs/lww-element-set-vs-paper.md`](docs/lww-element-set-vs-paper.md) — Shapiro et al. INRIA RR-7506 §3.3.4, LWW-comparison lookup with `lookup_after_add_with_fresh_ts` + `remove_at_higher_ts_extinguishes`.

The methodology — the Tier-A/B/C distinction, when read-sides are needed, the snapshot-in-op-payload pattern, and the spec-validation lesson from `in_span_boundary` — is documented in [`docs/readside-projections.md`](docs/readside-projections.md).

Everything is checked on Lean `v4.28.0` against the `chore-bump-lean-4.28` branch of a [Blaster fork](https://github.com/kayceesrk/Lean-blaster).

### CRDTs ([`Sal/CRDTs/`](Sal/CRDTs))

**Registers & counters:**
- `Increment_Only_Counter`
- `PN_Counter`
- `LWW_Register`
- `MAX_Register`
- `MIN_Register`
- `Multi_Valued_Register` — classical replace-on-write MVR via the snapshot-in-op-payload trick (Shapiro et al. INRIA RR-7506 §3.2.2). State `(writes, removed)`; concurrent writes survive via additive merge, sequential writes overwrite via the snapshot. **+ read-side**: `is_visible_value`, `concurrent_writes_both_visible`, `sequential_write_supersedes`. See [`docs/mvr-vs-paper.md`](docs/mvr-vs-paper.md).
- `Bounded_Counter` — Sypytkowski 2019 / Balegas et al. 2015. PN-counter plus a sparse per-replica-pair `transfers` map for quota redistribution.

**Sets & maps:**
- `OR_Set` — Shapiro et al. INRIA RR-7506. **+ read-side**: `lookup`, `add_wins_over_concurrent_remove`, `add_then_remove_extinguishes`. See [`docs/or-set-vs-paper.md`](docs/or-set-vs-paper.md).
- `Grow_Only_Set`
- `Grow_Only_Multiset`
- `LWW_Element_Set` — Shapiro et al. INRIA RR-7506. Per-element latest-add-ts and latest-remove-ts maps; `lookup` uses strict-`>` comparison (remove-wins on tie). **+ read-side**: `lookup_after_add_with_fresh_ts`, `remove_at_higher_ts_extinguishes` (independent intent theorems); `lookup_def` (definitional unfolding of `lookup`, not a behavioural guarantee — renamed from `latest_write_wins`, which overstated it). See [`docs/lww-element-set-vs-paper.md`](docs/lww-element-set-vs-paper.md).
- `LWW_Map`
- `MAX_Map`

**Sequences & structured data:**
- `RGA` — Replicated Growable Array, the sequence CRDT underlying Automerge / Yjs, in its state-based formulation as a grow-only `Map OpId (char, afterId, deleted)`. **+ read-side**: `visible_lt` four-rule DFS-traversal predicate, `causal_order_visible_lt`, `tombstone_monotone_under_remove`, `concurrent_insert_tiebreak_deterministic`. See [`docs/rga-vs-paper.md`](docs/rga-vs-paper.md).
- `Peritext` — Litt et al. CSCW 2022. Rich text = RGA + formatting marks represented as a flat `set AnchorAttachment`. **+ read-side**: paper Ex 1 / 2 / 3 / 5 / 7 / 8 intent-preservation theorems. See [`docs/peritext-vs-paper.md`](docs/peritext-vs-paper.md).
- `Shopping_Cart`
- `Add_Win_Priority_Queue` — adapted from Zhang et al. 2023. **+ read-side**: `lookup`, `add_wins_over_concurrent_rmv`, LWW innate, MCW-collapsed-to-Σ acquired, `get_max`, `inc_increases_acquired`. See [`docs/aw-crpq-vs-paper.md`](docs/aw-crpq-vs-paper.md).

### MRDTs ([`Sal/MRDTs/`](Sal/MRDTs))

- `Increment_Only_Counter`
- `PN_Counter`
- `Multi_Valued_Register` — classical MVR with the same `(writes, removed)` shape as the CRDT but standard three-way merge per component. **+ read-side** (mirrors the CRDT side). See [`docs/mvr-vs-paper.md`](docs/mvr-vs-paper.md).
- `Grow_Only_Set`
- `Grow_Only_Map`
- `OR_Set` — **+ read-side** (mirrors the CRDT side via three-way merge). See [`docs/or-set-vs-paper.md`](docs/or-set-vs-paper.md).
- `OR_Set_Efficient` — compressed variant with `(rid, ts, elem)` triples and per-replica deduplication. **+ read-side** with the same headline theorems on the triple representation.
- `Replicated_Growable_Array` — the tombstoned MRDT RGA (`Sal/MRDTs/RGA_with_tombstones/`). **+ read-side** with relational `readSeq_visible` and the three RGA intent theorems. See [`docs/rga-vs-paper.md`](docs/rga-vs-paper.md).
- `RGA_Tombstone_Free` — the canonical RGA (`Sal/MRDTs/RGA/`): the **tombstone-free, path-carrying RGA**: deletes really remove (no tombstone set); each op carries its target's recorded ancestor path, and merge rehomes survivors along it. Provably outside the standard 24-VC schema (commutation is reachability-conditioned, and a prefix-free variant is impossible — `RGA_PrefixFree_Impossible.lean`); verified instead by a direct end-to-end theorem, `rga_ra_linearizable3_eq`: RA-linearizability up to observational `≈` at every reachable configuration under honest delivery, via the applicability-conditioned metatheory ([`Sal/ConditionedMRDTs/MRDT_Instances/RGA/RA_Lin.lean`](Sal/ConditionedMRDTs/MRDT_Instances/RGA/RA_Lin.lean)). An **eq-variant** (`RGA_Tombstone_Free_Eq_MRDT.lean`) shows the `≈` is purely representational: a normalizing delete pins ghost payloads to the default, on normal forms the observational equivalence *is* structural equality, and the variant's folds are the normal forms of the original's. See [`Sal/MRDTs/RGA/doc/why-the-path-matters.pdf`](Sal/MRDTs/RGA/doc/why-the-path-matters.pdf).
- `Add_Win_Priority_Queue` — adapted from Zhang et al. 2023. Drops the CRDT's tombstone set since the LCA handles Add-Wins directly, leaving `set (add_ts, elem, value) × set (inc_ts, elem, amount)`. **+ read-side**. See [`docs/aw-crpq-vs-paper.md`](docs/aw-crpq-vs-paper.md).
- `Peritext` — Litt et al. CSCW 2022. RGA substrate plus `set AnchorAttachment`. RGA's tombstones are structurally load-bearing (later inserts reference earlier char ids), so this MRDT keeps all components grow-only and uses pointwise-union merge, mirroring `RGA_MRDT`. **+ read-side**. See [`docs/peritext-vs-paper.md`](docs/peritext-vs-paper.md).
- `Enable_Wins_Flag` — enable-wins boolean flag, per-replica map of `(counter, flag)`.
- `Enable_Wins_Flag_known_broken` — intentionally buggy variant preserved as a demo fixture. Drives the Plausible counterexample demo; the bug manifests on `inter_right_1op`.

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

Browser demos live in [`demos/`](demos) (Vite + React + TypeScript, one hand-ported module per RDT). 28 of the 29 RDTs have a playground — 17 CRDTs + 11 MRDTs (the tombstone-free RGA does not have one yet).

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
- [`Sal/CRDTs/`](Sal/CRDTs) — 17 state-based CRDTs in the `⟨Σ, σ₀, do, merge, rc⟩` signature.
- [`Sal/MRDTs/`](Sal/MRDTs) — 12 state-based MRDTs.
- [`Sal/Counterexample_Visualization/`](Sal/Counterexample_Visualization) — the `WriterMonad_*.lean` logging-monad traces that feed the ProofWidgets visualizer.
- [`demos/`](demos) — Vite + React + TypeScript playgrounds, one per RDT. CRDT demos do two-way merge; MRDT demos maintain a git-style commit DAG with LCA-driven three-way merge and a toggleable history visualisation.
- [`docs/porting-op-based-crdts.md`](docs/porting-op-based-crdts.md) — recipe for porting a new op-based CRDT into Sal's state-based signature.
- [`ROADMAP.md`](ROADMAP.md) — open research threads (Neem soundness metatheory, op→state transfer, the tombstone-free/prefix-free RGA results) with status and entry points.
- [`docs/metatheory-note/joinpeel-note.pdf`](docs/metatheory-note/joinpeel-note.pdf) — a self-contained paper-style note: why the original VCs are inadequate (worked counterexamples), the set-relative repair and the Join Lemma, the new `JoinPeelVCs`, and the mechanization.
- [`Sal/ConditionedMRDTs/mrdt-metatheory.pdf`](Sal/ConditionedMRDTs/mrdt-metatheory.pdf) — the self-contained paper-style note on the MRDT (ternary-merge) metatheory, complete in one document: what an MRDT is and how to describe one (with the counter, the OR-set and the tombstone-free RGA as worked examples), the corrected flat metatheory (the eight VCs with intuition, the delta contract and why no lattice contract can exist, the causal-delta equation, the LCA lemma erratum, the defeater execution, the discharged production catalogue — with TikZ execution diagrams), the conditioned metatheorem with the end-to-end pen-and-paper proof for the tombstone-free RGA, the open questions with their kernel-checked findings, and the mechanization map.
- [`Sal/CRDTs/Metatheory/`](Sal/CRDTs/Metatheory) — the Neem soundness meta-theorem for binary-merge CRDTs, corrected: machine-checked counter-models refute the paper's merge-case proof and show the 24-VC bundle insufficient (a *reachable* non-RA-linearizable execution under `CoreVCs` + full semilattice laws); the repaired chains `CoreVCs + JoinPeelVCs ⇒ RA-lin` and the CD ladder `CoreVCs + ACI + inflation + CD ⇒ RA-lin` are proved end-to-end (0 sorries), with CD proved the exact minimal residual. See its `README.md` and `FINDINGS.md` (A1–A9, drafts A10–A12).
- [`Sal/ConditionedMRDTs/`](Sal/ConditionedMRDTs) — the ternary (three-way merge) metatheorem over the version DAG: the LCA lemma as a reachability invariant, a validated VC set (`CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3`), and kernel-checked end-to-end RA-linearizability for **all 12 production MRDTs** through one generic conditioned framework: the eleven flat datatypes (OR-Set, OR-Set-efficient, Enable-wins flag, Grow-Only Set and Map, Increment-Only and PN counters, tombstone RGA, Peritext, Multi-Valued Register, Add-Wins Priority Queue) at the identity instantiation with their VC discharges under `MRDT_Instances/` (one directory per RDT), and the **tombstone-free RGA** — provably outside the VC schema — at full generality (`MRDT_Instances/RGA/RA_Lin.lean`): RA-linearizability up to observational `≈` at every reachable configuration, from a single honest-delivery assumption (born accuracy + applicable delivery), kernel-clean. Beyond the production mirrors, five born-conditioned instances: the **bounded (escrow) counter** — convergence is flat, and the bound `value ≥ 0` is a kernel-checked safety theorem at every version of every reachable configuration whose history satisfies the client applicability contract (`bc_version_inv`, `MRDT_Instances/BoundedCounter/`); and the **mergeable queue** of Peepul (PLDI'22 *Certified Mergeable Replicated Data Types*) — concurrent enqueues form a non-commuting clique, so no `rc` assignment exists and the flat VC engine is structurally unavailable; its Join Lemma is instead proved **directly**, exhibiting Peepul's three-way merge as the linearization witness at every merge, giving per-version RA-linearizability under honest delivery (`queue_ra_linearizable3`, `MRDT_Instances/MergeableQueue/`), with the dequeue `applicable` head-check discharging honesty (`qHonest_of_applicable`); and the **FWW reservation register** — first-writer-wins with the arbitration timestamp in the payload (a min-semilattice, the positive complement to the `lww_merge_needs_timestamps` kill-test), whose winner is characterized at every reachable version (`fww_version_min`, honesty-free) and whose claim-when-unset discipline is deliberately consumed by no theorem: "unset" is not stable under concurrent honest extension, so a merge-based register is a reservation, never a mutex; the **LWW register** — the max-semilattice dual, with-metadata arbitration carried in the payload so its eight VCs are pure `max`-algebra and its winner `lww_version_max` is characterized at every reachable version (honesty-free, `MRDT_Instances/LWWRegister/`), the resolution of the `lww_merge_needs_timestamps` kill-test in the LWW rather than FWW direction; and **BudgetCart** — a budgeted shopping cart (OR-set contents with add-wins `rc`, per-replica spend *derived* from live instances so removal refunds the adder automatically), convergent through the OR-set route (`BCart_ra_linearizable3_eq`) with its budget-safety theorem delivered **hypothesis-gated** (`bcart_version_inv_gated`): the ungated obligation is provably false because vis-only causal folds are enumeration-dependent under concurrent add/remove — the instance that forces Open Question 8 (rc-oriented causal witnesses). The composition kit (`Sal/ConditionedMRDTs/Metatheory/Product*.lean`) turns the binary heterogeneous product of conditioned MRDTs into once-only theorems — convergence (concatenation join witness), safety (one-sided causal witnesses; the two-sided form is provably impossible), and the ≈-quotient lift — and its first real consumer is **composed Peritext** (`MRDT_Instances/Peritext_Composed/`): rich text as RGA ⊗ marks (`peritextComposed_ra_linearizable_up_to_eq`, up to ≈_RGA × =; marks resolved at read time by the RGA's own path-climbing, render ≈-congruence kernel-checked), against a from-scratch alternative assessed structurally infeasible. The **canonical fused Peritext** (`MRDT_Instances/Peritext/`) is the tombstone-free-*and*-live alternative: characters and boundary marks share one RGA (`PeritextElt = char ⊕ boundary`), so mark endpoints ride document order directly rather than freezing tree paths; it carries the same convergence capstone (`peritext_ra_linearizable_up_to_eq`) plus *independent* positional intent theorems (`render_id_active_iff_between`, `render_span_before`), at the cost of non-atomic mark placement (the mark-positioning trilemma — atomic / tombstone-free / live, pick two). Superseded routes, impossibility results, and plans live under `Development/`.
- [`Sal/MRDTs/RGA/doc/why-the-path-matters.pdf`](Sal/MRDTs/RGA/doc/why-the-path-matters.pdf) — a visual (TikZ) account of why the tombstone-free RGA needs the operation path, and why a prefix-free variant cannot be VC-verified.

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
