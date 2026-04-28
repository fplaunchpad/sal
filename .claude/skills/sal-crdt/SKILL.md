---
name: sal-crdt
description: Use when adding a state-based CRDT or MRDT to the Sal framework, closing residual VCs on an existing one, or otherwise working inside /Users/kc/repos/sal. Covers the ⟨Σ, σ₀, do_, merge, rc⟩ signature, the 24 RA-linearizability VCs, the proof-closing playbook (per-component decomposition, flatten nested sets, Aristotle intermediate lemma), and the streaming-build monitoring technique needed for multi-minute `lake build` runs.
---

# Working on Sal CRDTs

Sal is a Lean 4 framework for verifying state-based CRDTs and MRDTs under replication-aware (RA) linearizability. Each RDT is specified as ⟨Σ, σ₀, `do_`, `merge`, `rc`⟩ and must discharge **24 VCs** that follow a fixed shape.

## Repository map

- [`Sal/CRDTs/`](../../../Sal/CRDTs/) — 18 state-based CRDTs.
- [`Sal/MRDTs/`](../../../Sal/MRDTs/) — 9 state-based MRDTs (three-way merge).
- [`Sal/Tactic/Sal.lean`](../../../Sal/Tactic/Sal.lean) — the three-stage `by sal` tactic (`dsimp + grind` → `blaster` → `dsimp + aesop + grind`).
- [`Sal/Interfaces/`](../../../Sal/Interfaces/) — decidable `set α := α → Bool` and `map key value` with `@[simp, grind]` lemmas.
- [`docs/porting-op-based-crdts.md`](../../../docs/porting-op-based-crdts.md) — **read this first** when porting a new op-based CRDT. It contains the five-step translation recipe, judgment calls, and proof-closing playbook. This skill is the short pointer; that doc is the full reference.
- [`README.md`](../../../README.md) — the "What's verified" catalog. Update when adding a new RDT.
- `lean-toolchain` pins Lean `v4.28.0`; `lakefile.toml` pins `mathlib` to `v4.28.0` and `Blaster` to `chore-bump-lean-4.28` of [`kayceesrk/Lean-blaster`](https://github.com/kayceesrk/Lean-blaster).

## Adding a new CRDT

1. **Copy a skeleton** from an existing CRDT of similar shape. Registers → `LWW_Register_CRDT`. Set-of-ops → `Grow_Only_Set_CRDT`. Projected log with causality-in-op → `RGA_CRDT`. Nested structured state → `Peritext_CRDT` (after refactor).
2. **Follow the five-step recipe** in `docs/porting-op-based-crdts.md`: pick Σ as a lattice, fold prepare+effect into `do_`, define `merge` as the join, define `rc`, then `by sal` on the 24 VCs.
3. **Update the catalog** in `README.md` under "What's verified" and adjust the RDT count (currently 27 = 18 CRDTs + 9 MRDTs).

## Closing stuck VCs

When a `by sal` doesn't close, reach for these in order (all detailed in `docs/porting-op-based-crdts.md`):

1. **Per-component decomposition** — kernel-verifiable, no SMT:
   ```lean
   := by
     intro h
     rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
       refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
       simp +decide [*] at h ⊢
     all_goals grind
   ```
   Works when Σ is a product and `eq` is a conjunction of per-component equalities.
2. **Flatten nested sets.** `map K (set V)` defeats grind (funext obligation). Refactor Σ to `set (K × V)`. Peritext is the canonical example of this refactor unblocking 5 stuck VCs.
3. **Aristotle-generated intermediate lemma.** For goals where an auxiliary fact makes the main theorem a one-liner. Pattern: `LWW_Map_CRDT` uses `merge_do_lex_max` and `lem_0op_aux`. Submit via `aristotle submit --project-dir <path> --wait`.
4. **TODO sorry with diagnostic.** Paste the failing `grind` state into the comment. Makes the next pass cheaper.

## Critical principle: keep state and ops grind-friendly

Prefer `Sal/Interfaces/Set_Extended.lean` and `Sal/Interfaces/Map_Extended.lean` as the first choice for Σ components. They're instrumented with `@[simp, grind]` and `grind_pattern` lemmas designed to make `grind` effective on RDT goals.

The broader automation rule is: **avoid any construction that forces grind/simp to reason about function equality pointwise**. Known-hostile patterns:

- `map K (set V)` — nested predicate forces funext.
- A map's `mappings` field built via `iter_upd` with a **conditional lambda** (e.g., splice-at-`do_` rewriting children based on an `if`).
- `rc` with nested conditionals producing non-`Either` results — branches multiply during norm-simp.
- `open Classical` combined with `noncomputable def` introducing `propDecidable` terms into `do_`/`merge`.

**Prefer `set (K × V)` tuples over `map K V` whenever `do_` would otherwise need per-key conditional rewrites.** The Peritext flattening refactor generalizes: Peritext went from `map (OpId × Bool) (set MarkOp)` to `set AnchorAttachment`. The same logic applies whenever splice or rewrite semantics would force a conditional lambda into a map's mappings field.

### Diagnostic signatures

If `by sal` fails with any of:

- `aesop: internal error during proof reconstruction: goal N was not normalised`
- `aesop: error in norm simp: simp failed: maximum number of steps exceeded`
- `(deterministic) timeout at 'whnf'` during theorem elaboration

…suspect a function-valued term in `state`, `do_`, or `merge`. **Reshape the state before reaching for manual proofs.** Manual proofs over a hostile state representation remain painful at every VC; a representation fix closes many at once.

## Building and monitoring

`lake build Sal.CRDTs.X` on a CRDT file can take 5–20 minutes (each `by sal` that reaches stage 2 spawns Z3 with a 30 s timeout, and there are 24 VCs). Don't sit and watch — use the streaming pattern:

```
Bash(run_in_background: true): lake build Sal.CRDTs.<name> 2>&1
# Then in the same turn:
Monitor(persistent: false, timeout_ms: 1800000):
  tail -f <output-path> | grep -E --line-buffered \
    "^error:|^warning:.*sorry|<file>\.lean:[0-9]+:.*(error|failed|sorry)|Built |Build completed|exited"
```

Each matching line lands as a notification. Keep working on something else until events arrive. If CPU drops to 0 and no "Built" event fires, the build is stuck — `ps aux | grep lean` to confirm.

## Sanity checks before declaring "done"

- `grep -c "sorry" <file>.lean` returns 0.
- `lake build Sal.CRDTs.<name>` exits 0 with no `error:` or `sorry` in the output.
- `README.md` "What's verified" catalog reflects the new RDT.
- No `by blaster` or `by aesop` calls outside `Sal/Tactic/Sal.lean` — all tactic invocations on RDT theorems go through `by sal` or the manual kernel-verifiable pattern.

## ReadSide and SPOT layers (Tier C RDTs)

The 24 VCs prove **state convergence**. The headline user-facing
claim — "the count is `incs − decs`", "`e` is in the OR-Set",
"this character is bold" — lives in a **read-side projection**,
not in the convergence proof. Methodology doc:
[`docs/readside-projections.md`](../../../docs/readside-projections.md).
Triage: every RDT gets a read-side + SPOT file. Tier C
(OR-Set / Peritext / RGA / MVR / AW-CRPQ / LWW-Element-Set) —
substantive proofs of paper claims. Tier A (counters / registers /
sets / maps / cart) — mechanical 30–60 line files that document
the obvious read so the next reader can confirm it is obvious.

**ReadSide theorems** (`<RDT>_ReadSide.lean`, sibling to the CRDT/MRDT file):

1. `def query` — the headline projection (`lookup`, `is_visible_value`,
   `formatted_visible`, …). Often `noncomputable` for `∃` over `set`.
2. **Convergence at the read.** `eq s₁ s₂ → query s₁ = query s₂`.
   Trivial: `subst` on plain-`=` `eq`, structural induction on
   propositional `eq`.
3. **Two to four intent theorems** lifting paper headlines. Recurring
   shapes: `add_wins_over_concurrent_*`, `*_then_*_extinguishes`,
   `*_after_*`, plus 1–2 RDT-specific (`causal_order_visible_lt`,
   `bold_expand_in_span_visible`, `innate_record_unique`).

**Concurrency encoding** — two equivalent conventions:
- *Literal* (used in OR-Set, RGA, MVR, AW-CRPQ readsides): the
  theorem's statement contains `merge (do_ s o₁) (do_ s o₂)` with
  `rid₁`, `rid₂` as universal parameters. The "concurrent" shape
  is in the theorem's form.
- *Abstract* (used in Peritext readside): the theorem takes any state
  `s` with the relevant ops' effects already present (e.g.
  `mark_present s addOp = true ∧ mark_present s remOp = true`).
  Concurrency is implicit — such a state arises by concurrent
  application from different replicas.
Both are paper-faithful; the SPOT layer is what makes the concurrent
shape concrete.

**SPOTs** (`<RDT>_SPOT.lean`, sibling to the ReadSide file):

Small Proof-Oriented Tests — pin each headline read-side claim onto a
concrete `do_`/`merge` trace with literal arguments. Two roles:
regression tests against refactors, and verified API documentation.

Discharge styles, in order of preference:
1. **Apply the readside theorem with literal arguments.** Cleanest;
   demonstrates the universal theorem firing on a specific instance.
2. `refine ⟨witness, ?_, ?_⟩ <;> decide` — when the membership
   predicate (`mem`/`contains`) reduces on literals.
3. `simp [hσ, do_, merge, ...]` for facts like `after_of σ c p = true`,
   `visible σ c = true`. Often closes directly on the Peritext maps
   substrate (CRDT side).

**Critical pitfalls (audit these in every SPOT):**

- **Match rids to the paper's framing.** If the paper claim is
  *"concurrent X from different replicas"*, use distinct `rid`s
  (e.g. `(ts₁, 0, op₁)` and `(ts₂, 1, op₂)`). Same rid is only for
  ops a single replica issues sequentially. With `rc := Either`
  everywhere, sequential `do_; do_` on different rids converges to
  the same state as a literal merge of two divergent branches —
  use it freely as the state-based stand-in for concurrent.
- **Don't degenerate the scenario.** A theorem with universal
  premises (e.g. `∀ m', mark_present σ m' → ...`) trivially admits
  states with one or zero such ops — the premises become vacuous.
  That's a *valid invocation* but doesn't exercise the paper's
  scenario. For "overlapping same-type Adds" (Peritext Ex 2), set
  up *two* AddMarks of the same type with truly overlapping spans;
  for "concurrent Add wins over Rem", actually have both ops in
  the state.
- **Inline structured-type literals.** `let m : MarkOp := ⟨…⟩`
  blocks projection reduction (`m.startSide`, `m.markType`) inside
  `simp`. Pass the literal tuple/anonymous-constructor directly to
  the theorem and to `mark_present`/`in_span_visible` calls.
- **State the read-side claim in projection vocabulary.** A
  read-side theorem's conclusion should use the projected query
  (`is_visible_value`, `lookup`, `formatted_visible`, …) — not raw
  membership in a state component. `ts ∈ removed` only invalidates
  the specific `(ts, v)` witness; `¬ is_visible_value σ v` is the
  headline claim and requires extra premises (coverage of all
  visible witnesses, inequality with the new written value).
  Convention: keep both — `<theorem>_witness` for the building
  block, `<theorem>_value` for the headline (see MVR's
  `sequential_write_supersedes_witness` / `_value`). If a SPOT
  has to use raw `rintro/simp/grind` to close a "no longer
  visible" claim, the value-level read-side theorem is missing.
- **`mark_present`-uniqueness pattern.** When a readside premise has
  `∀ m', mark_present σ m' = true → P m'`, build a uniqueness lemma:
  ```lean
  have h_uniq : ∀ m' : MarkOp, mark_present σ m' = true →
      m' = literal₁ ∨ m' = literal₂ ∨ … := by
    intro m' h_pres
    simp [hσ, ..., mark_present, marks_of, do_, add,
          _root_.singleton, union, empty] at h_pres
    rcases m' with ⟨_, _, _, _, _, _, _⟩
    grind
  ```
  The `rcases m'` *before* `grind` is what makes it work — it
  destructures the structured type into fields so `grind` can
  collapse the AnchorAttachment-injectivity disjunction
  componentwise.

## Commit style

Follow recent commits on `main`:

- `Peritext_CRDT: all 24 VCs closed via flat-set mark representation (19/24 -> 24/24)`
- `LWW_Map_CRDT: close remaining 4 VCs via Aristotle-generated intermediate lemmas`
- `add RGA_CRDT (state-based sequence CRDT; Peritext dependency)`

Pattern: `<RDT name>: <action> (<before>/<24> -> <after>/<24>)` for VC-closing work; `add <RDT>_<flavor> (<one-line pedigree>)` for new RDTs. The user's global preference is no `Co-Authored-By: Claude...` trailer.
