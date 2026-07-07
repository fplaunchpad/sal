# Agent notes: RGA MRDT attempts

Read this before touching anything under `Sal/MRDTs/RGA*`. It indexes the
several RGA designs in this repo, records which one is proved, and points at the
per-directory `PLAN.md` files for detail.

For the **end-to-end RA-linearizability proof of the tombstone-free RGA in the
generic conditioned metatheory framework** (the active research arc — the
`Sal/MRDTs/Metatheory/Development/` files), jump to the task list at the bottom:
[End-to-end RA-linearizability in the generic framework](#end-to-end-ra-linearizability-in-the-generic-framework--task-list).

## Authoritative, proved result

`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean` — tombstone-free RGA with
path-carrying operations, flat-set state `map ℕ (ℕ × ℕ)` (id ↦ element, anchor).

- Deletion physically removes the id from the domain (`del` ⇒ `contains` drops
  it); there is no tombstone/graveyard set in the state.
- Concurrent safety comes from each op carrying its leaf's ancestor path;
  `resolve` climbs the path to the nearest live ancestor when the anchor/target
  was spliced away. This is what replaces tombstones.
- Proof status: builds clean (0 errors, 0 `sorry`). `rc_non_comm'` is proved,
  i.e. every operation pair commutes (`rc = Either` everywhere), via
  `insins_comm`, `insdel_comm`, and `deldel_comm`. Conditioned on well-formed
  histories (`accurate`: the op's claimed path is the true ancestor chain;
  `fresh_ts`; `contains s 0 = false`).
- Build check: `timeout 300 lake env lean Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean`

## The other RGA designs

| Variant | Where it lives | State | Status |
|---|---|---|---|
| RGA (original) | `Sal/MRDTs/RGA/` (main) | tombstone + read-side projection | committed, 0 sorry; different design, kept |
| RGA_Splice | branch `wip/rga-splice` | flat set, splice delete | predecessor of RGA_Tombstone_Free; `do_`-level non-commutation (`cond_comm_base`); superseded |
| RGA_Tree | branch `wip/rga-tree` | literal inductive tree | WIP, open sorries (MRDT 1, ReadSide 1, Refinement 6; not build-verified) |
| RGA_Tree_Path | branch `wip/rga-tree-path` | inductive tree + ghost path | early WIP, 17 sorry-bearing lines |

Design one-liners:
- RGA_Splice / RGA_Tombstone_Free: flat keyed records, OR-set survival on identities, merge
  reparents survivors by climbing the LCA ancestor chain. RGA_Tombstone_Free adds the op
  path so the single-replica `do_` also commutes.
- RGA_Tree: tree is the primary state, `Remove` excises and re-parents children
  one level up; merge recovers convergence with an LCA-driven orphan walk.
- RGA_Tree_Path: same tree state, each op additionally carries the full
  root-to-target path (ghost in practice: `do_` reads only the target).

## Git organization

main keeps only the proved/working designs:
- `Sal/MRDTs/RGA/` (original tombstone-based MRDT, already committed).
- `Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean` (proved tombstone-free path-carrying
  RGA).

The broken / superseded / WIP attempts are parked on branches (not lost):
- `wip/rga-splice`     — `Sal/MRDTs/RGA_Splice/RGA_Splice_MRDT.lean`
- `wip/rga-tree`       — `Sal/MRDTs/RGA_Tree/`
- `wip/rga-tree-path`  — `Sal/MRDTs/RGA_Tree_Path/`

To inspect or resume one: `git checkout <branch>`. To read a single file without
switching: `git show <branch>:<path>`.

## Resuming an attempt

- Build a single file (always wrap, the proofs are heavy):
  `timeout 300 lake env lean <path>.lean 2>&1 | tail -40`.
- Do not run `lake build` of a fresh target and do not use worktrees; build the
  specific file.
- "declaration uses sorry" in this repo can be a Z3-validated Blaster admit, not
  necessarily an open goal.
- Each design has a living `PLAN.md` in its directory; update it as work lands.

---

# End-to-end RA-linearizability in the generic framework — task list

The active research arc: an **unconditional, kernel-clean, Lean-mechanized proof
of RA-linearizability for the tombstone-free RGA** in the generic conditioned
metatheory framework. Working files live in `Sal/MRDTs/Metatheory/Development/`.

**Target theorem.** `IsRALinearizable3 C` for every reachable, honestly-executed
config `C`, with `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` and
**zero admitted combinatorial hypotheses**.

**The capstone is already built and kernel-clean.**
`RGA_Skeleton.lean → rga_RA_linearizable_skeleton` wires the entire chain to the
unconditional conclusion `IsRALinearizable3 C`, typechecked with 0 `sorry`, with
the residual admitted as **explicit named hypotheses** (ordinary hypotheses, not
`sorry`). This is deliberate: every type is locked, so discharging a hypothesis
cannot hit a downstream type mismatch. The skeleton takes 7 arguments:

- **Legitimate scope** (stay — the honest/reachable premises any linearizability
  theorem carries): `C` (the config), `hReach` (C reachable), `hgenW` (events
  well-formed).
- **To discharge** (combinatorial/algebraic obligations): `hEnum`, `hReady`,
  `hMergeInputs`, `hBA`. Discharging these four = end-to-end.

Status legend: ✅ done · 🟡 mechanical / close · 🔴 open.

## Target 1 — `hEnum` (the δ-enum) — ⚠️ REFUTED AS STATED (2026-07-07); needs re-phrasing

Produce `π₀` enumerating the delta `D = (ev₁∪ev₂)\(ev₁∩ev₂)` with `listPermOf`,
`respects loOnEq`, and `noopFeasible` from the LCA fold `applySeqR init_st ρ₀`.
This is the only genuinely novel obligation.

**⚠️ REFUTATION (commit 7a7ff9c, `RGA_HEnum_Refutation.lean`, kernel-clean):
`hEnum` as typed in the skeleton is FALSE.** Counterexample: `insOpE` creates
node 1; `delOpE ∈ LCA` deletes it; `insOnX ∈ delta` is anchored ON node 1 and
CONCURRENT with `delOpE` (branch 1 ran `insOnX` first — `ρ₁ = [insOpE, insOnX,
delOpE]` is noopFeasible). Every hEnum premise holds; the forced `π₀ = [insOnX]`
is neither accurate at `σ₀` (anchor dead) nor a no-op (writes id 3). The
LCA-first SHAPE `ρ₀ ++ π₀` pre-applies LCA deletes concurrent with delta
inserts; no ordering freedom *within* π₀ can fix that. A `_guardSlot` partial
application proves the refuted statement is the skeleton's slot verbatim.

The RDT itself is fine (`raw_fold_rehomes`): `do_` rehomes via the carried path,
`merge` reproduces it via `climb`. What is false is the noopFeasible/accuracy
BOOKKEEPING at the delta fold. Layer resolution: **update layer (from-init
branch folds) → applicable+noopFeasible is the right condition; merge delta fold
(from σ₀) → rehome-correctness (`Faithful`/`ClimbFaithful`, GenDisc-like) is the
right condition** — accuracy is provably wrong there.

**Fix analysis.** The merge half of `hCanon_of_leaves` consumes only the three
BRANCH CanonMatch facts; the union CanonMatch exists solely for
`merge ≈ fold-from-σ₀`, and is plausibly TRUE in the counterexample — only the
engine's noopFeasible ROUTE to it is unachievable. Both fix options need the
same math (Faithful-at-prefix for delta ops at LCA-first prefixes):
* **(B, recommended)** re-base the δ-fold obligation from `noopFeasible` to
  `Faithful`/`ChainFaithful` and generalize the engine's per-op premise
  (`ChainOK`-from-`Faithful` instead of from-`accurate`). Rides the completed
  LINCHPIN infrastructure (`chainFaithful_at_interleaved_fold`,
  `RGA_InterleavedThreading`). Gate: probe `chainOK_of_accurate_ins` → does it
  extend to Faithful (rehomed anchors)?
* **(A)** keep the engine, produce the union CanonMatch from a from-init enum
  (noopFeasible from init IS achievable — the counterexample's
  `[insOpE, insOnX, delOpE]`), transport to the LCA-first fold — but the
  transport needs the same Faithful-based swap machinery
  (`general_swap_bothFaithful`), so it smuggles B's math in anyway.

Still-valid pieces: `loOnEq` causal collapse (rc=Either ⟹ `loOnEq ⊆ vis`), the
eq-commutation dead end, δ-B order existence, all `RGA_FoldMembership` /
`RGA_NoopFeasible_Accurate` preservation lemmas (they apply to the from-init /
branch layer and to any Faithful re-base).

Sub-task ledger (⚠️ pre-refutation framing — C2–C5 were the accuracy-based plan;
under the Faithful re-base the establishment/order questions recur in Faithful
form, with C1's preservation lemmas reusable):

- ✅ **A — acyclicity / loOnEq collapse.** `RGA_LoOnEq_Causal.lean`
  (`loOnEq_causal_iff`, `loOnEq_imp_vis`, `not_loOnEq_of_not_vis`,
  `not_loOnEq_cross_branch`), `RGA_DeltaEnum.lean` (`exists_min_of_irrefl_trans`).
- ✅ **B — order existence (perm + respects loOnEq).**
  `RGA_DeltaEnum.lean → exists_loOnEq_enum`.
- ✅ **C1 — noopFeasible foundation.** `RGA_FoldMembership.lean`
  (`contains_applySeqR_of_no_del`, `isAncPath_applySeqR_of_chainSafe`,
  `ins_accurate_at_prefix_of_lca_chain`), `RGA_NoopFeasible_Accurate.lean`
  (`noopFeasible_head_at`, `ins_accurate_of_noopFeasible`).
- 🔴 **C2 — delta-anchored establishment.** Inserts anchored on delta-*created*
  nodes (not in the LCA `σ₀`): accuracy from the chain π₀ itself builds. Needs an
  establishment invariant along the fold — a fold-agreement bridge (`σ_i^{π₀}`
  agrees with `σ_i^{branch}` on chain keys because interleaved ops are
  `chainSafe`), reusing each branch's noopFeasibility via
  `ins_accurate_of_noopFeasible`. *Genuine multi-lemma development.*
- 🔴 **C3 — delete case appOrNoop.** Each delete in π₀ is applicable-or-noop at
  its prefix: `delOK_of_appOrNoop_del` (`RGA_NoopFeasible_CanonFold.lean:134`,
  exists) when target live via C1/C2 preservation; else noop = delete-of-absent.
- 🔴 **C4 — delete-deferred order `R = loOnEq ∪ protect` + its acyclicity.** Makes
  the `chainSafe` hypotheses of C1–C3 *achievable* (`protect(i,d)` = insert i →
  delete d when d removes a node on i's anchor chain). Does **not** reduce to a
  rank function (a causally-shallow delete must sort *after* a causally-deep
  insert) → needs a `TransGen`/reachability argument. Ingredients built
  (`not_loOnEq_cross_branch`, `ins_accurate_of_noopFeasible`); assembly not.
  *The hardest piece.*
- 🔴 **C5 — assembly.** Thread C1–C4 through `noopFeasible_of_prefixApp`
  (`ConditionedExecutionModel.lean:275`, exists) → `noopFeasible π₀` from the LCA
  fold = the third δ-enum obligation.

C2 + C4 are the last substantive proofs. **Everything below Target 1 is
engineering** — the framework already dictates its shape (types locked by the
skeleton).

## Target 2 — `hReady` (4× `EngineReady`) — reachability plumbing

For each of the 4 folds (ρ₀ over ev₁∩ev₂, ρ₁ over ev₁, ρ₂ over ev₂, union ρ₀++π₀
over ev₁∪ev₂), produce `EngineReady = ⟨E ⊆ events, listPermOf, noopFeasible from
init, ∃R.(ids0 ∧ WfOpGenQ ∧ RefEdge ∧ respects)⟩`.

- 🟡 **2.1 perms + set-inclusion.** `listPermOf` for ρ₀/ρ₁/ρ₂ from hEnum context;
  union via append; `ev₁∩ev₂, ev₁∪ev₂ ⊆ events` set algebra.
- 🟡 **2.2 noopFeasible from init.** ρ₀/ρ₁/ρ₂ given; union via `noopFeasible_append`
  (`GenericEqQuotient_NF.lean:172`) of the ρ₀-part (given) + π₀-part (hEnum's C5
  output).
- 🔴 **2.3 `ids0`** (∀ o∈E, o.1 ≠ 0) — from the framework Lamport clock /
  `distinct_ts`.
- 🔴 **2.4 `WfOpGenQ` per event** — honest-execution well-formedness (F1/F2 thread).
- 🔴 **2.5 `RefEdge E R`** — anchor references become order edges under the causal
  order R (`causal_mono` thread).
- 🔴 **2.6 `respects ρ R`** — branch enum respects R, from `RefEdge ⊆ loOnEq` via
  `loOnEq_anchor_edge` (`RGA_ConvergenceEq.lean:554`, exists at **WfOpQ**).
  ⚠️ **needs a WfOpA restatement** (skeleton uses `WfOpA`; same init_st-witness
  technique).

## Target 3 — `hMergeInputs` (merge-glue leaf bundle) — algebraic tail

One 7-way conjunction over the 4 folds. Largest volume; pure algebra, no novelty.

- 🔴 **3.1 / 3.2** σ₀ forest invariants I1 (`anc y < y`) and I2 (parent-live).
- 🟡 **3.3** `contains σ₀ 0 = false` (root is not a real node).
- 🔴 **3.4** per-id causal set-algebra (insertedIn/deletedIn, 8 clauses across folds).
- 🔴 **3.5** per-survivor membership (survivor inserts present in the right branch
  enum, 4 clauses).
- 🔴 **3.6** per-survivor `CanonBirthBridge` — reduced by
  `canonBirthBridge_per_survivor` (`RGA_BirthBridge.lean:32`) to 4 carriers;
  **deep residual = `BranchInv`-I4.** The deepest sub-residual of the whole arc.

## Target 4 — `hBA` (born-applicable at each apply) — from the guard rebase

Per apply step of a reachable execution: `qapplicable ∧ (∀ s', applicable ⟹
WfOpA)`. The guard rebase made this **intrinsic**: `WfOpA = WfOpQ ∧ accurate`, and
`applicable = accurate ∧ fresh_ts ⟹ WfOpA` given `WfOpQ` from honesty.

- 🟡 **4.1** `applicable ⟹ WfOpA` from the guard — foundation built
  (`appOrNoop_qsig` at `BornApplicable_Guard.lean:63`, `rgaInvPresA`,
  kernel-clean).
- 🔴 **4.2** `qapplicable` at each reachable apply step (from `hReach` + the guard).

## Target 5 — final assembly + hygiene

- 🔴 **5.1** Instantiate `rga_RA_linearizable_skeleton` with the discharged 1–4 →
  the **unconditional** theorem (only `C`, `hReach`, `hgenW` remain, as honest
  scope).
- 🔴 **5.2 axiom audit** — `#print axioms` on the final theorem ⊆
  `{propext, Classical.choice, Quot.sound}`, **no `sorryAx`** anywhere in the
  transitive chain.
- 🔴 **5.3** Update `README.md` ("What's verified" catalog, RDT count, file refs)
  and this file when the capstone lands.
- 🔴 **5.4** Consider promoting the `Development/` files onto the mainline RGA path
  (or document the promotion).

## Critical path & research/engineering split

```
  hEnum ─┬─ A ✅  B ✅  C1 ✅
         └─ C2 🔴  C4 🔴  →  C3  →  C5      ← last research content
                                            │  (union fold consumes π₀)
  hReady ── 2.3 / 2.4 / 2.5 / 2.6 (F-threads)
                                            ▼
  hMergeInputs ── 3.1 / 3.2 / 3.4 / 3.5 / 3.6 (BranchInv-I4)   ← pure algebra
                                            │
  hBA ── 4.1 🟡  4.2 🔴
                                            ▼
                    5.1 assemble → 5.2 axiom audit → 5.3 README
```

- **Research (nearly closed):** `hEnum` C2 + C4. Once those land, the
  RGA-in-generic-framework *question* is answered — the delta-enum construction
  and its noopFeasibility are the only parts that are not mechanical.
- **Engineering tail (last-20%-takes-80%):** `hReady` F-threads, all of
  `hMergeInputs` (esp. `BranchInv`-I4), `hBA` 4.2. Volume, not novelty.
- **Recommended order:** finish `hEnum` (C2 → C4 → C3 → C5) first; it closes the
  research question and produces the π₀ the union folds of `hReady`/`hMergeInputs`
  consume. Then the remaining three targets are a discharge grind against
  fully-typed obligations — parallelizable and deferrable.
