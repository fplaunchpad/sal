# Tombstone-free flat-set RGA MRDT — living plan

Source: `_references/Formalising-the-Merge.pdf` (Summer Internship 2026 working
notes, 28 Jun 2026). This is the third RGA attempt in the repo, distinct from
`RGA_Tree` (inductive-tree state) and `RGA_Tree_Path`. Here the state is a
**flat keyed collection of records**, which is the representation `sal`'s
automation is calibrated for.

## Design (from the PDF)

- Record `(t, e, a)`: identity `t`, element `e`, birth-anchor `a` (`0` = root).
- State `Σ` = well-formed finite set of records. wf = unique ids + anchors
  resolve + acyclic parent map. So `Σ` is a rooted ordered tree on
  `{0} ∪ ids(σ)`, *no tombstones*.
- `do_`:
  - `Ins(e, a)` at ts `t`: add record `(t, e, a)`.
  - `Del(x)`: `splice(σ, x)` — drop `x`, rehome each child of `x` onto `anc_σ(x)`.
- `merge(L, A, B)` three-way:
  - `I` = OR-set survival on **identities**:
    `(ids L ∩ ids A ∩ ids B) ∪ (ids A ∖ ids L) ∪ (ids B ∖ ids L)`.
  - `β(t)` = birth-anchor by region (L / A∖L / B∖L).
  - `climb_I(a)` = walk up `anc_L` skipping dead ids to nearest live anchor or 0.
  - result `= {(t, el(t), climb_I(β(t))) | t ∈ I}`.
- `rc`: PDF gives the RGA-order clause (concurrent same-anchor inserts ordered
  by ts). PDF states "two clauses" but only specifies one (incomplete).

## Encoding decisions

- **State = `map ℕ (ℕ × ℕ)`** (`id ↦ (elem, anchor)`), `0` = root. A `set`
  (`α → Bool`) can't extract elements, but `splice`/`climb` need `anc_σ(x)`
  lookups, so a `map` is required. id-uniqueness is then structural (map keys).
- **`climb` fuel**: on wf states `anc(t) < t` (you insert *after* an existing,
  hence older, node), so the parent chain strictly descends and `climb` from
  anchor `a` terminates in ≤ `a` steps. Fuel = the anchor's value `a` is
  computable and total on arbitrary states.
- **`do_` guard dropped** (like `RGA_CRDT`): `Ins` always records, even with a
  dangling anchor. The PDF's `(a = 0 ∨ a ∈ ids)` guard only adds *more*
  non-commuting pairs; dropping it isolates the analysis to the splice
  mechanism, which is the actual subject of the notes.

## Key analytical finding (pre-verification)

The merge is a correct convergent three-way merge — it reproduces all 8 PDF
scenarios. But the **deletion is physical excise** (tombstone-free splice), and
that is the same obstruction `RGA_Tree` documented:

- `Ins(e, x)` (insert after `x`) does **not** commute with `Del(x)`:
  - `Ins; Del`: record is added then rehomed onto `anc(x)` — it survives.
  - `Del; Ins`: `x` is gone, so the new record dangles (or is lost).
  These are different states ⇒ `rc(Ins(e,x), Del(x))` must be non-`Either`.
- That non-`Either` entry makes **`cond_comm_base` non-vacuous**, and the trio
  `(Ins(e1,p), Del(p), Ins(e3,p))` is a concrete counterexample: LHS keeps
  `e1` (rehomed), RHS keeps neither. So `cond_comm_base` fails.

This is the tombstone tax: physical excise destroys the anchor a concurrent
insert needs, so insert-after-deleted can't commute with delete. The flat-set
representation changes the *automation* story (sal handles `do_`/merge over
keyed records far better than over inductive trees) but **not** the RA-
linearizability obstruction. Same verdict as `RGA_Tree`, reached structurally.

## Verification plan / status

| Item | Status |
|---|---|
| State, init, helpers (`anc`/`el`/`ids`) | ✅ |
| `do_` (Ins / Del=splice) | ✅ |
| `merge` (I / β / climb) | ✅ |
| `#eval` oracle: all 8 PDF scenarios reproduce | ✅ exact match |
| `#eval`: `cond_comm_base` counterexample (LHS ≠ RHS) | ✅ |
| `climb_fixpoint` lemma | ✅ proven |
| `merge_idem` (under `wf`) | ✅ proven |
| `no_rc_chain` | ✅ proven |
| `cond_comm_base_violated` (counterexample proven) | ✅ proven |
| `merge_comm`, `lem_0op` (under `wf` + `consistent`) | ⏳ sorry (Aristotle-scale) |
| Write-up of RA-linearizability verdict | ✅ below |

## Path-carrying variant (`RGA_Path_MRDT.lean`)

Resolution that keeps the state tombstone-free and recovers the VCs: operations
carry the ancestor path of their anchor/target, and `do_` reparents via the path
when the anchor was spliced away. Same flat-set state, same merge.

- **Op type**: `Ins : ℕ → List ℕ → ℕ` (elem, prefix, anchor), `Del : List ℕ → ℕ`
  (prefix, target). State stores only the immediate anchor; the prefix interior
  is ghost.
- **`do_`** uses `resolve` (nearest live element of `anchor :: prefix`). When the
  anchor is live, `resolve = anchor` and the path is untouched.
- **`rc = Either`** everywhere: all consistent-path pairs commute.

Results (all built, 1 sorry):

| Item | Status |
|---|---|
| 8 PDF scenarios (merge unchanged) | ✅ reproduce |
| `cond_comm_base` trio CONVERGES (`trio_converges`) | ✅ proven (native_decide) |
| inconsistent paths DIVERGE (`inconsistent_diverges`) | ✅ proven |
| `cond_comm_base` holds (vacuous, `rc = Either`) | ✅ proven |
| `no_rc_chain` holds (vacuous) | ✅ proven |
| `ins_path_free` (path unused when anchor live = erasure) | ✅ proven |
| `merge_idem` (under `wf`) | ✅ proven |
| `rc_non_comm'` (reachability-conditioned) | ✅ **proven** — no sorry, axioms `[propext, Classical.choice, Quot.sound]` |
| merge family (`lem_0op`, `base_2op`, `inter_*`/`ind_*`) | ⏳ as splice variant: `wf` + `accurate` + climb lemmas |

**`rc_non_comm'` (closed via ultracode workflow + focused agents).** The naive
`rc_non_comm` (`rc = Either ↔ ∀ s commute`) is *false*: two inserts where one
anchors at the other's fresh id don't commute. The correct, proven statement
conditions `commutes_with` on `accurate` (op path = real ancestor chain) +
`fresh_ts` (Ins id fresh, nonzero) + `contains s 0 = false`. Premise discovered
and exhaustively validated (`violations = 0`, `fresh_ts` load-bearing), then
proven by full case analysis:
- Ins/Ins: `resolve` invariance under `upd` at a fresh key (`resolve_upd_notMem`).
- Ins/Del: hinges on `resolve_doDel_self` — after deleting `x`, resolving `x`'s
  own chain lands on `anc s x`, matching the order where the insert is rehomed.
- Del/Del: `collapse` lemma — when `x1`'s parent is `x2`, path-uniqueness
  (`IsAncPath_unique`) forces `p1 = x2 :: p2`, so both orders' cross-filtered
  resolves agree (`resolve_doDel`, `resolve_filter_ne`, `isancpath_resolve_self_filter`).
Helper lemmas all kernel-checked; no `native_decide` in the proof.

**Reading.** The splice variant proves `cond_comm_base` *false*; the path variant
proves the same statement *true* (vacuously) and shows the same trace converge.
The obstruction is relocated from a structural-state fact to an op-level
path-consistency premise, which is lighter (op-local, no state induction) but not
free. Going all the way to path-as-identity would make consistency definitional
and drop the premise, at the cost of depth-growing identities (the conservation
principle once more).

## Verdict (to be confirmed by the build)

Tombstone-free RGA (any representation, this flat-set one included) does **not**
satisfy the full 24 VCs: `cond_comm_base` fails because physical excise makes
insert-after-deleted non-commute with delete. The merge formula itself is sound
and converges. The salvageable, paper-faithful claim is **state convergence of
the merge**, with operation-ordering correctness living in the read-side
projection (as in `RGA_CRDT`).
