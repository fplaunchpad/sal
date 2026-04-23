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
| 3 | Bridge theorem: Apply case | **PARTIAL** |
| 4 | Bridge theorem: Merge case (hardest) | SCAFFOLDED |
| 5 | End-to-end smoke test on Grow-Only Set | TODO |
| 6 | Instantiate bridge for remaining CRDTs | TODO |
| 7 | Op-based TS (Liittschwager §3.3) | **SCAFFOLDED** |
| 8 | Weak simulation + weak trace machinery | **SCAFFOLDED** |
| 9 | Canonical op→state emulation $\mathcal{G}$ | TODO |
| 10 | Weak simulation proof for $\mathcal{G}$ | TODO |
| 11 | Transfer theorem | TODO |

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

### 3. Bridge theorem — Apply case — PARTIAL

Given `π` witnessing RA-lin at `C`, with `C --apply t r o--> C'`, show
`π ++ [e]` witnesses RA-lin at `C'`. Needs:

- `applySeq s (π ++ [e]) = D.update (applySeq s π) e` — easy.
- `lo_{C'}` respects the new extension.
- Permutation of `ev ∪ {e}`.

The non-trivial part is the `lo_{C'}` extension lemma — the new vis
has `L r × {e}` added, which changes `lo` around the frontier.

Landed:
- `applySeq_append_single` — trivial, closed.
- `lo_shrink_under_apply` — the key monotonicity lemma. Closed.
  States: `lo C' p q → lo C p q` when the new vis is `C.vis ∪ (ev × {e})`
  and neither `p` nor `q` equals `e`.
- `RA_lin_preserved_apply` — signature and overall structure in
  place; `applySeq` equation closed. Three internal `sorry`s for the
  detailed `listPermOf` / `respects` assembly. Each is ~20 lines of
  mechanical Lean we know how to write on paper.

**Effort remaining:** 1–2 days.

### 4. Bridge theorem — Merge case — SCAFFOLDED

The load-bearing step. Given RA-lin witnesses for both merge inputs,
construct one for the merged state. Follows the paper's bottom-up
template:

- Decompose `L r₁` and `L r₂` into the six sub-event sets
  $L^a_1, L^b_1, L^a_2, L^b_2, L^a_\top, L^b_\top$.
- Push events through the merge using `base_2op`, `ind_*`, `inter_*`.
- Use `merge_comm`, `merge_idem` to normalize.
- Discharge `lo` constraints via `rcNonComm` and `condComm`.

**Effort:** 2–4 weeks. Single hardest proof in Phase 1.

### 5. Smoke test on Grow-Only Set — TODO

Build a `SatisfiesVCs (D_GSet)` instance from the existing theorems in
`Sal/CRDTs/Grow_Only_Set_CRDT.lean`, check `ra_linearizable_of_vcs`
fires end-to-end. Catches shape mismatches between my VC statements and
the existing Sal code.

**Effort:** 1 day once steps 1–4 land.

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

### 8. Weak simulation + weak trace machinery — SCAFFOLDED

Landed in `Weak_Simulation.lean`:
- `silentStep`, `silentClosure` — τ-step and τ*.
- `weakStep` — τ*-α-τ* step as an inductive.
- `isWeakExecution` — chain of observable weak steps.
- `weakTrace` — observable label lists.
- `WeakSim` — weak simulation structure with `rel` + `step` fields.
  Requires the two TSs to share a label type (Liittschwager setup).
- `weakSim_sound` — soundness theorem statement (trace inclusion);
  proof is `sorry`.

**Effort remaining:** close `weakSim_sound` (~1 week: induction on
`isWeakExecution`, glue `WeakSim.step`).

### 9. Canonical op→state emulation $\mathcal{G}$ — TODO

Liittschwager et al. §4.2: given an op-based CRDT, produce the
state-based emulator (essentially inlines causal broadcast into the
state).

**Effort:** 1–2 weeks.

### 10. Weak simulation proof for $\mathcal{G}$ — TODO

The technical core of Liittschwager et al. Shows
$\mathsf{init}_{\text{op}} \approx \mathsf{init}_{\mathcal{G}(\text{op})}$.
Two relations (host simulates guest and vice versa), both by execution
induction.

**Effort:** 2–4 weeks. Second hardest proof in Phase 1.

### 11. Transfer theorem — TODO

Composition of the pieces above:

> **Theorem.** If $\mathcal{D}$ satisfies the 24 VCs, then every
> reachable configuration in its op-based counterpart
> $\mathcal{G}^{-1}(\mathcal{D})$ is RA-linearizable.

Proof: RA-lin is a weak trace property; weak simulation (step 10)
preserves weak trace properties; bridge (step 4) gives state-based
RA-lin; done.

**Effort:** ~1 week.

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
