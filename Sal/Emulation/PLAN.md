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
| 0 | Scaffolding (signature, TS with 5 invariants, RA-lin skeleton) | **DONE** |
| 1 | Transcribe the 24 VCs + `cond_comm_lift` into `SatisfiesVCs` (25 fields) | **DONE** |
| 2 | Bridge theorem: base / CreateReplica / Query cases | **DONE** |
| 3 | Bridge theorem: Apply case | **DONE** |
| 4 | Bridge theorem: Merge case (hardest) | **PARTIAL** (existential form, convergence + 7 BottomUp rules + 3-of-4 sub-cases of `merge_linearization_exists` closed; closure-stable carving foundation in place; 4 sorries remain — see §4 details) |
| 5 | End-to-end smoke test on Grow-Only Set (25 VCs) | **DONE** |
| 6 | Instantiate bridge for remaining CRDTs | TODO |
| 7 | Op-based TS (Liittschwager §3.3) | **SCAFFOLDED** |
| 8 | Weak simulation + weak trace machinery | **DONE** |
| 9 | Canonical op→state emulation $\mathcal{G}$ | **SCAFFOLDED** |
| 10 | Weak simulation proof for $\mathcal{G}$ (incl. `effectiveState` linear extension) | TODO |
| 11 | Transfer theorem | **SCAFFOLDED** |

## Steps in detail

### 0. Scaffolding — DONE

Files landed in `Sal/Emulation/`:

- `Labeled_TS.lean` — generic LTS, executions, reachability.
- `CRDT_Signature.lean` — `CRDTSig` structure; `RcRes`; `Op`; `commutes`.
- `CRDT_TS.lean` — configuration with 5 invariants (`dom_eq`,
  `vis_src`, `vis_tgt`, `vis_causal`, `timestamps_distinct`,
  `vis_total_same_replica`), four rules (CreateReplica / Apply /
  Merge / Query), `initConfig`, `labeledTS`. Latter three
  invariants added to support the merge-case bottom-up induction
  (top-level `differentReplicas` derivation; `distinctOps`
  preconditions of BottomUp-2-OP).
- `RA_Linearizability.lean` — `lo_C`, `rc-non-comm`, `cond-comm`,
  `IsRALinearizable`, stubbed `ra_linearizable_of_vcs`.

### 1. Transcribe the 24 VCs + `cond_comm_lift` into `SatisfiesVCs` — DONE

All 25 fields of `SatisfiesVCs` now present in `RA_Linearizability.lean`:

`rc_non_comm`, `no_rc_chain`, `cond_comm_base`, `merge_comm`,
`merge_idem`, `base_2op`, `ind_lca_2op`, `inter_right_base_2op`,
`inter_left_base_2op`, `inter_right_2op`, `inter_left_2op`,
`inter_lca_2op`, `ind_right_2op`, `ind_left_2op`, `base_1op`,
`ind_lca_1op`, `inter_right_base_1op`, `inter_left_base_1op`,
`inter_right_1op`, `inter_left_1op`, `inter_lca_1op`, `ind_left_1op`,
`ind_right_1op`, `lem_0op`, `cond_comm_lift`.

The first 24 names match the per-CRDT theorem names in
`Sal/CRDTs/*.lean` exactly, so building a `SatisfiesVCs (D_CRDT)`
instance for any existing CRDT will be field-by-field plumbing for
those. `cond_comm_lift` (lin.tex §3.2 semantic extension of
`cond_comm_base` to arbitrary intervening sequences) is the one
field without a direct per-CRDT counterpart; vacuous for the 14
rc=Either CRDTs in the suite, and a one-time discharge obligation
per CRDT for the rest.

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

### 4. Bridge theorem — Merge case — PARTIAL (existential form; 4-of-5 sub-cases closed)

Strategy document: [`MERGE_PROOF.md`](MERGE_PROOF.md).

The original three-lemma decomposition (`merge_witness_{perm,
respects, state}`) was retired: the `_respects` cross case is
structurally coupled to the state equation and cannot be proved
independently of any closed-form witness. The current shape is a
single existential theorem `merge_linearization_exists` whose
internal induction co-constructs the witness with its lo-respect
property.

**Landed** in `Sal/Emulation/Merge_Linearization.lean`:
- `restrictTo` — sub-list of a list restricted to a `Set` (noncomputable via `Classical`).
- Event-set decomposition definitions: `L_top`, `L₁_local`,
  `L₂_local`, `L_a`, `L_b`, plus partition lemmas `L_a_union_L_b`,
  `L_a_inter_L_b`. (Definitions only — induction over them is the
  remaining work.)
- Convergence machinery (closed): `applySeq_swap_via_cond_comm_lift`,
  `applySeq_swap_commute`, `applySeq_swap_lo_incomparable`,
  `applySeq_bubble_lo_max`, `convergence`. Consume `cond_comm_lift`
  + Configuration invariants `timestamps_distinct`,
  `vis_total_same_replica`. Modulo the overwriter-witness sorry at
  the call site (see below).
- BottomUp rules (closed): `bottomUp_0op`, `bottomUp_1op_top_base`,
  `bottomUp_1op_bot_base`, `bottomUp_2op_base`,
  `bottomUp_2op_init_left`, `bottomUp_2op_reachable`,
  `bottomUp_1op_top_reachable`. The 2-OP reachable form is the
  load-bearing rule for the existential's distinct-last-event case.
- `merge_init_left_reachable_nil`, `merge_init_left_reachable_singleton` (closed).
- `merge_init_right_reachable` (closed via `merge_comm`).
- `merge_linearization_exists` — strong induction on
  `|π₁| + |π₂|`. Closed sub-cases:
  - both empty (uses `merge_idem`),
  - asymmetric one-empty (uses
    `merge_init_{left,right}_reachable`),
  - shared last event (uses `lem_0op` + IH on shrunken event sets).
- `RA_lin_preserved_merge_via_witness` — destructures the
  existential, closed unconditionally. Once
  `merge_linearization_exists` closes, swap the stub
  `RA_lin_preserved_merge` in `RA_Linearizability.lean` for a
  single-line call.

**Live sorries (4):**
1. `RA_Linearizability.lean:652` — `RA_lin_preserved_merge` shim;
   trivial once the existential closes.
2. `Merge_Linearization.lean:474` — overwriter-witness obligation
   inside `convergence`'s call to `applySeq_bubble_lo_max`.
   Resolved by tightening `convergence`'s signature to
   `ev = C.events` and propagating an overwriter-closure invariant.
3. `Merge_Linearization.lean:743` — `merge_init_left_reachable`
   for `|π| ≥ 2`. No standalone VC extends `merge X init` beyond
   the singleton case; expected to close as a byproduct of the
   `L^a / L^b` carving.
4. `Merge_Linearization.lean` (distinct-last-event branch of
   `merge_linearization_exists`). With the new closure-stable
   refactor (session 2026-04-25 below), `differentReplicas` is
   now uniformly derivable inside the recursion via
   `differentReplicas_of_closure`. The remaining work for this
   sorry is the L^a / L^b *peel discipline* (choose peel candidates
   from `L^a` so they are strictly local; case-split on commute;
   apply BottomUp-2-OP / commutation appropriately).

### Session 2026-04-25: closure-stable refactor

Threaded `vis ∧ ¬commute` causal closure through
`merge_linearization_exists` and its inner generalised statement.
Discharged at the top level from `Configuration.vis_causal`.
Proven preserved through shared-event tail peels via
`closure_preserved_by_tail_peel` (consequence of `respects π (lo C)`
plus `lo`'s first disjunct). The lemma
`differentReplicas_of_closure` makes the top-level `vis_causal +
vis_total_same_replica` argument uniform across recursive depth:
strictly local peel candidates from `ev_i \ ev_{3-i}` plus the
threaded closures yield `differentReplicas` without referring to
any specific replica's `C.L`.

**Discipline:** demand-driven only. Lemmas are landed when there is
a concrete consumer to check them against — not as speculative
infrastructure for an upcoming branch. (An earlier attempt to
pre-stage `last_is_lo_maximal` and `last_is_lo_maximal_in_ev` was
trimmed once it became clear they were sitting in scope without a
proved obligation that consumed them.)

**Top-down decomposition for the distinct-last-event branch.**
The branch is split into four named, sorry-bodied theorem stubs;
`merge_linearization_exists`'s body invokes them by application and
is itself sorry-free. The collective type-sufficiency of the four
stubs is verified by the dispatch type-checking. The stubs:

* **`distinct_last_strict_local_commute_case`** (sub-case A):
  `e₁ ∉ ev₂`, `e₂ ∉ ev₁`, `D.commutes e₁ e₂`. Strategy: commuting
  events swap freely; pick one to peel via `BottomUp-1-OP-bot` after
  re-permutation. `differentReplicas` is unneeded.
* **`distinct_last_strict_local_noncomm_case`** (sub-case B):
  `e₁ ∉ ev₂`, `e₂ ∉ ev₁`, `¬ D.commutes e₁ e₂`. Strategy: derive
  `differentReplicas` via `differentReplicas_of_closure` (the
  threaded closure is what unblocks this), extract `rc` direction
  from `hVC.rc_non_comm`, apply `bottomUp_2op_reachable`, recurse
  via `ih`. *Most likely first target* — both prerequisites already
  proved.
* **`distinct_last_e2_shared_case`** (sub-case C): `e₂ ∈ ev₁`.
  Strategy: `e₂` is the wrong peel candidate from the right side;
  re-permute `π₂` via `convergence` to bring an `L^a (ev₂ \ ev₁)`
  element to the tail. Coupled to the open `convergence`
  overwriter sorry — likely tackled together.
* **`distinct_last_e1_shared_case`** (sub-case D): `e₁ ∈ ev₂`.
  Mirror of C.

The `MergeWitness` and `MergeIH` abbreviations factor out the
existential conclusion and the strong-induction IH so the four
stubs share readable signatures.

Sorry count rises from 4 → 7 in this step, but each new leaf is a
tightly-scoped, well-shaped obligation in its own theorem.
`merge_linearization_exists` is now a thin dispatcher that routes
to the named stubs.

This refactor leaves the live-sorry count unchanged at 4 but
restructures the distinct-last-event obstruction: it is no longer
"how do we derive `differentReplicas` at recursive depth" — it is
"how do we choose peel candidates so the strict-local hypothesis
holds." That is the L^a / L^b carving question.

**Next-session checklist** (recorded inline at the
distinct-last-event sorry site):

1. Case-split on `(e₁ ∈ ev₂)` and `(e₂ ∈ ev₁)` to identify
   strictly-local vs shared peel candidates.
2. In the strictly-local sub-case, case-split on
   `D.commutes e₁ e₂`. Non-commute branch: derive
   `differentReplicas` (via `differentReplicas_of_closure`)
   and apply `bottomUp_2op_reachable`. Commute branch: independent
   commutation argument; commuting events can swap freely.
3. In the shared sub-cases, fall back to L^a candidates from
   `ev₁ \ ev₂` (or `ev₂ \ ev₁`), re-permuting via convergence to
   bring the candidate to the tail. Note that
   convergence-based re-permutation surfaces the same overwriter
   obligation as `Merge_Linearization.lean:377`, so this and the
   convergence sorry should be tackled together.

**Effort remaining (rebased):**
- Sorry (2) — overwriter witness + signature tightening: ~1–2 days.
- Sorry (3) + (4) — `L^a / L^b` carving and propagating it through
  the existential's induction: ~1–2 weeks each, sharing
  infrastructure. Closing them together is realistic.

**Total remaining for step 4:** ~2–3 weeks of focused work.

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
- `D_satisfies_VCs : SatisfiesVCs D` — **all 25 fields closed**:
  - 14 vacuous VCs closed by `intros; simp_all`. Includes the
    `cond_comm_lift` field (`Fst_then_snd` premise unsatisfiable).
  - 11 real-content VCs (`rc_non_comm`, `merge_comm`, `merge_idem`,
    `base_2op`, `ind_lca_2op`, `ind_left_2op`, `base_1op`,
    `ind_lca_1op`, `ind_left_1op`, `ind_right_1op`, `lem_0op`)
    plumbed to the corresponding `_root_.*` Sal theorems via the
    Prop/Bool bridge lemmas.

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
