# Phase 1 plan: formal op-based ⇒ state-based transfer for CRDTs

## Goal

Mechanically prove in Lean:

> For every Sal state-based CRDT $\mathcal{D}$ that satisfies the 24 VCs,
> its canonical op-based counterpart $\mathcal{O}$ (in the sense of
> Liittschwager et al.'s emulation $\mathcal{G}$) is RA-linearizable.

This reduces to two subgoals we prove independently and then compose:

- **Bridge:** $\mathcal{D}$ satisfies the 24 VCs $\Longrightarrow$
  every reachable configuration of $\mathcal{S}_\mathcal{D}$ is
  RA-linearizable. (Follows the Sal paper's bottom-up linearization
  proof, appendix §A.2–A.4.)
- **Transfer:** RA-linearizability is a weak trace property, and weak
  simulation implies weak trace inclusion; so RA-lin of $\mathcal{D}$
  transfers to $\mathcal{O}$ via Liittschwager et al.'s canonical
  emulation. (Follows arXiv:2504.05398v2 §4, Corollary "Emulation
  Preserves Weak Trace Properties".)

## Status summary

| # | Step | Status |
|---|------|--------|
| 0 | Scaffolding (signature, TS, RA-lin skeleton) | **DONE** |
| 1 | Transcribe the 24 VCs into `SatisfiesVCs` | **DONE** |
| 2 | Bridge theorem: base / CreateReplica / Query cases | **DONE** |
| 3 | Bridge theorem: Apply case | **DONE** |
| 4 | Bridge theorem: Merge case (hardest) | **PARTIAL** (refactored to monolithic existential; both-empty case closed; two inductive cases sorry) |
| 5 | End-to-end smoke test on Grow-Only Set | **DONE** |
| 6 | Instantiate bridge for remaining CRDTs | TODO |
| 7 | Op-based TS (Liittschwager §3.3) | **SCAFFOLDED** |
| 8 | Weak simulation + weak trace machinery | **DONE** |
| 9 | Canonical op→state emulation $\mathcal{G}$ | **SCAFFOLDED** |
| 10 | Weak simulation proof for $\mathcal{G}$ | TODO |
| 11 | Transfer theorem | **SCAFFOLDED** |

## Steps in detail

### 0. Scaffolding — DONE

Files landed in `Sal/Emulation/`:

- `Labeled_TS.lean` — generic LTS, executions, reachability.
- `CRDT_Signature.lean` — `CRDTSig` structure; `RcRes`; `Op`; `commutes`.
- `CRDT_TS.lean` — configuration (per-replica state & event set + vis),
  four rules (CreateReplica / Apply / Merge / Query), `initConfig`,
  `labeledTS`.
- `RA_Linearizability.lean` — `lo_C`, `rc-non-comm`, `cond-comm`,
  `IsRALinearizable`, stubbed `ra_linearizable_of_vcs`.

### 1. Transcribe the 24 VCs into `SatisfiesVCs` — DONE

All 24 fields of `SatisfiesVCs` now present in `RA_Linearizability.lean`:

`rc_non_comm`, `no_rc_chain`, `cond_comm_base`, `merge_comm`,
`merge_idem`, `base_2op`, `ind_lca_2op`, `inter_right_base_2op`,
`inter_left_base_2op`, `inter_right_2op`, `inter_left_2op`,
`inter_lca_2op`, `ind_right_2op`, `ind_left_2op`, `base_1op`,
`ind_lca_1op`, `inter_right_base_1op`, `inter_left_base_1op`,
`inter_right_1op`, `inter_left_1op`, `inter_lca_1op`, `ind_left_1op`,
`ind_right_1op`, `lem_0op`.

Names match the per-CRDT theorem names in `Sal/CRDTs/*.lean` exactly,
so building a `SatisfiesVCs (D_CRDT)` instance for any existing CRDT
will be field-by-field plumbing.

Two helpers introduced: `distinctOps o₁ o₂ := o₁.time ≠ o₂.time` and
`differentReplicas o₁ o₂ := o₁.rep ≠ o₂.rep` — these replace the
Bool-returning `distinct_ops` / `!= get_rid` of the existing code.

### 2. Bridge theorem — trivial cases — DONE

Landed in `RA_Linearizability.lean`:

- `initConfig_RA_lin` — base case; `π = []` witnesses RA-lin for
  replica 0 at σ₀ with empty event set.
- `RA_lin_preserved_createReplica` — takes the equations about
  `C'.N`, `C'.L`, `C'.vis` as ingredients (rather than a `Step`
  hypothesis); new replica uses `π = []`, old replicas re-use IH with
  unchanged `lo`.
- `Query` case of the main induction is `exact ih` (configuration is
  unchanged).

`ra_linearizable_of_vcs` now has a working induction scaffold with two
remaining `sorry`s: `apply` (step 3) and `merge` (step 4).

### 3. Bridge theorem — Apply case — DONE

Landed:
- `applySeq_append_single` — trivial, closed.
- `lo_shrink_under_apply` — the key monotonicity lemma. Closed.
  States: `lo C' p q → lo C p q` when the new vis is `C.vis ∪ (ev × {e})`
  and neither `p` nor `q` equals `e`.
- `Configuration` gained invariant fields `dom_eq`, `vis_src`,
  `vis_tgt` — "vis only relates observed events" is now structural.
- `RA_lin_preserved_apply` — **fully closed, no auxiliary hypotheses**.
  The degenerate `C.vis e a` case is ruled out by `C.vis_src` directly.

No outstanding sub-lemmas. Step 3 is finished.

### 4. Bridge theorem — Merge case — PARTIAL (machinery laid down)

Strategy document: [`MERGE_PROOF.md`](MERGE_PROOF.md).

Landed in `Sal/Emulation/Merge_Linearization.lean`:
- `restrictTo` — sub-list of a list restricted to a `Set`
  (noncomputable via `Classical`).
- `merge_witness π₁ π₂ ev₁ ev₂` — concrete list definition:
  `π₁|_{ev₁ ∩ ev₂} ++ π₁|_{ev₁ \ ev₂} ++ π₂|_{ev₂ \ ev₁}`.
- Three supporting lemmas stated, bodies `sorry`:
  - `merge_witness_perm` — `listPermOf result (ev₁ ∪ ev₂)`.
  - `merge_witness_respects` — respects `lo C`.
  - `merge_witness_state` — `applySeq σ₀ result = D.merge s₁ s₂`.
- `RA_lin_preserved_merge_via_witness` — the closure of the Merge case,
  **fully assembled** from the three sub-lemmas. Once they're closed,
  this theorem is done; then replace `RA_lin_preserved_merge` in
  `RA_Linearizability.lean` with a single-line call.

**Effort remaining:**
- `merge_witness_perm`: ~1 day (list/set manipulation, uses `List.filter` preserves `Nodup`).
- `merge_witness_respects`: ~3–5 days (paper Lemma 1 / Lemma 2 in §4.1).
- `merge_witness_state`: 2–3 weeks (the bottom-up induction; uses all 24 VCs).

The load-bearing step. Given RA-lin witnesses for both merge inputs,
construct one for the merged state. Follows the paper's bottom-up
template:

- Decompose `L r₁` and `L r₂` into the six sub-event sets
  $L^a_1, L^b_1, L^a_2, L^b_2, L^a_\top, L^b_\top$.
- Push events through the merge using `base_2op`, `ind_*`, `inter_*`.
- Use `merge_comm`, `merge_idem` to normalize.
- Discharge `lo` constraints via `rcNonComm` and `condComm`.

**Effort:** 2–4 weeks. Single hardest proof in Phase 1.

### 5. Smoke test on Grow-Only Set — DONE

Landed in `Sal/Emulation/Instances/Grow_Only_Set.lean`:
- `D : CRDTSig` instance wrapping the top-level
  `concrete_st`, `init_st`, `do_`, `merge`, `rc` from
  `Sal/CRDTs/Grow_Only_Set_CRDT.lean`.
- `toRcRes` bridge between per-file `rc_res` and generic `RcRes`.
- `distinctOps_iff`, `differentReplicas_iff` — `simp` lemmas linking
  Prop-valued versions to Bool-valued `distinct_ops` / `get_rid`.
- `D_rc_Either`, `D_rc_not_Fst`, `D_rc_Fst_iff_False` — helpers
  capturing "`D.rc = Either` always" used by the vacuous VCs.
- `D_satisfies_VCs : SatisfiesVCs D` — **all 24 fields closed**:
  - 14 vacuous VCs (premise requires `Fst_then_snd`) closed by
    `intros; simp_all`.
  - 8 real-content VCs (`base_2op`, `ind_lca_2op`, `ind_left_2op`,
    `base_1op`, `ind_lca_1op`, `ind_left_1op`, `ind_right_1op`,
    `lem_0op`) plumbed to the corresponding `_root_.*` Sal theorems.
  - `rc_non_comm` bridges the Prop/Bool premise conjunction.
  - `merge_comm`, `merge_idem` direct delegation.

Validates that the generic `SatisfiesVCs` struct matches the concrete
Bool-valued theorem statements in Sal's existing files. One down,
17 CRDTs to go (but the pattern is mechanical — probably a day for
the rest once a macro is written).

**Effort remaining:** zero, for Grow-Only Set. End-to-end
`ra_linearizable_of_vcs D_satisfies_VCs` still fires a `sorry` via the
Merge case, but the plumbing on the upstream side is all solid.

### 6. Instantiate bridge for remaining CRDTs — TODO

17 remaining CRDTs. Each already has the 24 theorems; bundle into
`SatisfiesVCs`. Consider a macro if the shape is uniform.

**Effort:** 1 day per CRDT, or batch with a macro (~1 week total).

### 7. Op-based TS — SCAFFOLDED

Landed in `Op_Based_TS.lean`:
- `OpCRDTSig` — ⟨Σ, σ₀, prepare, effect, query, rc⟩ with `Msg` type.
- `OpConfiguration` — ⟨Γ, Σ, β⟩ (event trace, per-replica state,
  message buffer).
- `OpLabel` — update / query / deliver; `deliver` is silent.
- `OpStep` — three rules matching Liittschwager Fig. op-global-rules.
- `enabled` predicate encoding causal delivery over `hb`.
- `opInitConfig`, `opLabeledTS` lifting into the generic `LabeledTS`.

Compiles cleanly. No theorems proved; no `sorry`s needed in this file.

**Effort remaining:** 0. Ready for consumption by `Emulation.lean`.

### 8. Weak simulation + weak trace machinery — DONE

Landed in `Weak_Simulation.lean`, fully proved:

- `coerceLabel`, `SilentPreserving` — explicit label-coercion helpers
  for working with `hLabel : T₁.Label = T₂.Label` without elaboration
  surprises.
- `silentStep`, `silentClosure` (τ*).
- `weakStep` (τ*-α-τ* inductive).
- `isWeakExecution` (chain of observable weak steps) and `weakTrace`.
- `WeakSim T₁ T₂ hLabel` — simulation structure with `rel` + `step`.
- `silentClosure_lift` — a T₁ silent closure lifts to a T₂ silent
  closure under a weak simulation (induction on `ReflTransGen`).
- `weakStep_lift` — a T₁ weak step lifts to a T₂ weak step, case-
  splitting on silent vs. observable.
- `isWeakExecution_lift` — the execution-chain lift.
- `weakSim_sound` — **closed**. Every weak trace of `s` maps to a
  weak trace of any `R`-related `t` in `T₂`.

All theorems kernel-verified; no sorries.

### 9. Canonical op→state emulation $\mathcal{G}$ — SCAFFOLDED

Landed in `Emulation.lean`:
- `effectiveState D hb delivered` — reconstruct the replica state
  from a set of delivered messages + a causal order. Stubbed body
  (returns `D.init`); TODO is picking a deterministic causal linear
  extension or delegating to commutativity.
- `canonicalG D hb : CRDTSig` — the canonical state-based emulator:
  state is `Set D.Msg`, `update` runs `prepare` on the effective state
  and appends the message, `merge` is set union, `query` delegates to
  `D.query` on the effective state, `rc` is lifted.
- `emulation_G_weak_bisim` — placeholder for the simulation theorem
  (currently `True`, to be restated with a proper label morphism
  alongside step 10).

Builds cleanly. Uses `noncomputable` + classical decidability on
`Set D.Msg` — acceptable at this scaffolding level.

**Effort remaining:** meaningful mechanization of `effectiveState`
(linear-extension machinery) and the simulation relation — both
coupled to step 10.

### 10. Weak simulation proof for $\mathcal{G}$ — TODO

The technical core of Liittschwager et al. Shows
$\mathsf{init}_{\text{op}} \approx \mathsf{init}_{\mathcal{G}(\text{op})}$.
Two relations (host simulates guest and vice versa), both by execution
induction.

**Effort:** 2–4 weeks. Second hardest proof in Phase 1.

### 11. Transfer theorem — SCAFFOLDED

Landed in `Transfer.lean`:
- `OpIsRALinearizable D hb trace` — op-side RA-lin as a predicate on
  traces. Body stubbed as `True`; TODO is fleshing out to match
  Liittschwager's trace-property formulation.
- `op_RA_linearizable_of_vcs` — the end-to-end meta-theorem statement:
  if `canonicalG D hb` satisfies the 24 VCs, every reachable
  op-based trace is RA-linearizable. Proof is `trivial` pending the
  real `OpIsRALinearizable`.

With step 11 scaffolded, the full architecture is in Lean — each of
the 11 steps has a file / lemma that compiles, and downstream parts
call upstream parts through typed interfaces. Completing Phase 1
means filling in the three real sorries (Apply vis-invariant, Merge,
weakSim soundness) + the `canonicalG` simulation in step 10.

**Effort remaining:** coupled to steps 3/4/8/10.

## Total effort

Roughly **3–5 months** at full-time focused pace. Genuine risks: the
Merge case (step 4) and the emulation simulation proof (step 10).
Everything else is either trivial, mechanical, or a direct port of a
paper proof.

## References

- Ramesh, Soundarapandian, Sivaramakrishnan, *Automatically Verifying
  Replication-aware Linearizability* (arXiv:2502.19967v1): defines
  $\mathcal{S}_\mathcal{D}$ (lin.tex §3.1), RA-lin (Def. lin, §3.2),
  bottom-up linearization (§3.3 + appendix §A.2–A.4).
- Liittschwager, Castello, Tsampas, Kuper, *CRDT Emulation, Simulation,
  and Representation Independence* (arXiv:2504.05398v2, ICFP '25):
  op-based/state-based TS (§3), weak simulation (§2, §4.2), trace
  property transfer (§4.4, Corollary "Emulation Preserves Weak Trace
  Properties"). Agda mechanization at Zenodo 15866358.

## How to use this document

This plan is the single source of truth for the state of Phase 1. Edit
it as each step lands — flip status to IN PROGRESS when starting and
DONE when finished. Add risks/blockers inline. If the step ordering
changes (e.g. we decide to axiomatize the bridge and pivot to the
emulation layer first), update the table first, then the details.
