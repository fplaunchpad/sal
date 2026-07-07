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

**Fix analysis (superseded by the built fix below).** The merge half of
`hCanon_of_leaves` consumes only the three BRANCH CanonMatch facts; the union
CanonMatch exists solely for `merge ≈ fold-from-σ₀` — only the engine's
noopFeasible ROUTE to it was unachievable. Decisive discovery: the engine's own
per-op condition `ChainOK` (`RGA_CanonConvergence.lean:89`) is ALREADY
rehome-tolerant ("weaker than `accurate` … survives the deletion of the chain's
own head" — vacuous in the counterexample), and `canon_fold` is mid-fold capable.
`noopFeasible` was a sufficient-condition packaging wrongly enshrined as the
interface.

**✅ CORRECTED SKELETON BUILT (commit b4c68e6), kernel-clean, 0 sorry:**
* `RGA_Corrected_Residual.lean` — `RgaEqJoinResidualLit2`: the union residual is
  now "∃ ρᵤ: the merged state is reachable by an honest from-init delivery of
  the union"; ρᵤ itself is the `IsCanonicalStateEqNF` witness.
  `canonFoldOK_concat`: the per-event discipline composes across `++`.
* `RGA_Corrected_Assembly.lean` — merge=fold via `eq_of_canonMatch2` (unchanged);
  the NEW hop `fold(ρ₀++π₀) ≈ fold(ρᵤ)` is the proved
  `RGA_update_convergence_canon`. `rga_eqJoinNF_of_canon2` ⟹ `EqJoinLemma3C_NF`.
* `RGA_Skeleton2.lean` — capstone `rga_RA_linearizable_skeleton2` ⟹ unconditional
  `IsRALinearizable3 C`. `hEnum` = **K1** (`CanonFoldOK ρ₀ σ₀ π₀` — engine-native
  delta discipline, TRUE in the refutation scenario) + **K2** (from-init union
  re-enum `ρᵤ` with perm/respects/noopFeasible/`CanonFoldOK` — the merge induction
  invariant) + the LCA/branch disciplines. `hReady` = THREE `EngineReady` legs
  (union leg DERIVED via `canonFoldOK_concat` + `canon_fold` from init).

**✅ K1 DISCHARGED (commits a8d0c98 + f1443a5, kernel-clean).**
`RGA_K1_DeltaDiscipline.lean` + `RGA_K1_Wiring.lean`:
`K1_canonFoldOK : … → CanonFoldOK ρ₀ (fold ρ₀) π₀` from **GenDisc2C** (each
event accurate at its own dependency fold — the engine's own rehome-tolerant
generation condition; `canonStepOK_of_gen` was the blueprint), the LCA's own
discipline (`CanonFoldOK [] init ρ₀`, existing noopFeasible engine route),
`respects π₀ (loOnA …)` (any vis-sort works), and execution-model facts.
Key move: the engine's `GoodEnum` interface threads the prefix's loOnA-respect
which the NF-witness ρ₀ can't supply — so every order-sensitive ingredient was
re-based on a freely-chosen loOnA-respecting ambient enumeration `U` (dep-lists
carve from `U`; the prefix enters only via `CanonInv` + set-inclusions, exactly
what `anc_transport`/`chainOK_transport` consume). Plus: `loOnA ⊆ vis` (rc =
Either), `DepC` irreflexive, no-DepE-edge-into-the-LCA, delta chains point
backward via `pairwise_append` (no index arithmetic).

**Remaining research:**
* **✅ GenDisc2C DISCHARGED (task #32; commits ea898f1 + 5a0c123, kernel-clean).**
  `RGA_GenDisc_Peel.lean` (bricks) + `RGA_GenDisc_Assembly.lean` (the strong
  induction): **`genDisc2C_of_born`** — born accuracy (each event accurate at
  SOME causally-ordered enum of its full past — the honest generation content)
  + id-uniqueness + nonzero ids + strict vis ⟹ `GenDisc2C Cfg E`. Mechanism:
  a past-op with no `loOnA` edge into `o` is BY DEFINITION pointwise invisible
  to `o`'s applicability, so non-deps peel off the end of a deps-first past
  enum with no state reasoning (`applicable_peel_suffix`); the reorder is
  engine convergence at `past(o)` (free relativization: `loOnA` ev-free,
  past loOnA-closed, `isDepPreC_of_restrict`); induction measured by a
  filtered listing (`msr_lt_of_mem` via `subperm_of_subset`).
  **K1's chain is now fully closed down to `hborn`**: hEnumC-conj-4 ←
  `K1_canonFoldOK` ← `genDisc2C_of_born` ← born accuracy at past folds —
  which is the execution model's job (generation states ARE past folds;
  hReady-layer plumbing, not research).
* **⚠️ K2 REFUTED — and DISSOLVED (2026-07-08, pen-level, crisp).** The from-init
  `noopFeasible` union enum does NOT exist in general. Counterexample (7 ops,
  criss-cross rehoming): shared creators build the chain `3→2→1→0`
  (`iy₁=(1,Ins [] 0)`, `ia₂=(2,Ins [] 1)`, `ia₁=(3,Ins [1] 2)`); replica A runs
  `z₂=(4,Del [1] 2)` then `o₁=(6,Ins [1] 3)` (records `anc 3 = 1`: post-z₂,
  1 live); replica B runs `z₁=(5,Del [] 1)` then `o₂=(7,Ins [] 2)` (records
  `anc 2 = 0`: post-z₁, 2 live). `o₁`'s accuracy forces z₂ effective while 1
  live (so z₂ before z₁) and 1 still live; `o₂`'s forces z₁ effective while 2
  live (so z₁ before z₂) and 2 still live — whichever delete goes first dooms
  the other branch's insert; spending a delete early as a noop forfeits the
  rehoming its branch's recorded chain requires. **Deep reason: tombstone-free
  rehoming makes delete-ORDER observable in survivors' stored parents; the two
  branches observed incompatible orders; no single guarded sequence replays
  both.** A merged version is NOT re-presentable as an honest delivery — the
  `IsCanonicalStateEqNF` union clause is unsatisfiable for the RGA, so
  `EqJoinLemma3C_NF` as stated cannot be discharged (third displaced-difficulty
  refutation: noopFeasible failed at the LCA-first delta, then at the from-init
  union; the honest discipline is `CanonFoldOK` everywhere).

  **The dissolution: swap the NF witness clause from `noopFeasible` to the
  engine-native discipline** (`IsCanonicalStateEqH` with `H ρ :=
  CanonFoldOK [] init_st ρ` for the RGA; generically a parameterized `H`).
  Then: (a) **the union witness is `ρ₀ ++ π₀` itself** — `CanonFoldOK` by
  `canonFoldOK_concat` (K1's output!), `respects loOnEq` by the existing union
  assembly in `RGA_EqJoin_NF`, fold ≈ merge by the corrected chain — **K2
  disappears entirely** (hEnumC conjuncts 5–8 deleted); (b) branch witnesses
  hand K1 `CanonFoldOK [] init ρ₀` directly as a premise (no engine
  re-derivation); (c) `GoodConfig3NF`'s apply-extension re-proves via
  `canonFoldOK_append` (snoc) from `qapplicable` (born-accurate ⟹
  `chainOK_of_accurate`); (d) the final RA-lin conclusion only ever uses the
  plain `IsCanonicalStateEq` part (`isCanonicalStateEq_of_NF` drops the
  clause), so the swap is interface-local. Re-thread scope: GenericEqQuotient_NF
  (witness def) + GoodConfig3NF (invariant + extension) + the corrected
  residual/assembly/skeleton files (drop ρᵤ, carry `CanonFoldOK`).

* **⚠️ FINDING #4 (2026-07-08): the CAPSTONE TARGET itself is unsatisfiable as
  stated.** `IsRALinearizable3` (`Adequacy.lean:35`) demands, per version, an
  enum whose fold **at the version's own signature** equals the state — at
  `D := QSig … WfOpA …` that is the **guarded** fold (`qdo`/`applySeqW`) with
  strict `=` on classes. The K2 counterexample shows every `WfOpA`-guarded
  replay of the criss-cross union skips `o₁` or `o₂` (the accuracy cycle), and
  a state missing the skipped node is observationally ≉ the merge — so NO
  witness exists: **`IsRALinearizable3 C` at the WfOpA-quotient is FALSE for
  the tombstone-free RGA at that reachable config.** The skeleton chain is
  sound as an implication but its conclusion is undischargeable. (This is the
  same noopFeasible/accuracy displaced-difficulty, surfacing at the very top:
  `isCanonicalState_of_NF` is exactly the guard-transparency step that consumed
  the witness's noopFeasibility.)

  **Fix options:**
  * **(R — recommended, cheap, research-correct):** re-state the capstone at
    the raw/≈ level — per version `v` with class `s` and events `E`:
    `∃ σ hσ, s = qmk σ hσ ∧ ∃ π, listPermOf π E ∧ respects π (lo core) ∧
    rgaEqEquiv'.eqv (applySeqR init_st π) σ`. This is the paper's
    RA-linearizability applied to the DATATYPE (raw `do_` folds, state up to
    observational eq); the guarded-quotient replay was mechanization packaging,
    never the paper's notion. The (H-swapped) GoodConfig3 invariant carries
    exactly this clause per version — the final extraction needs NO guard
    transparency (drop `isCanonicalState_of_NF`), only the order inclusion
    (`loOnEq_antimono`-style, as the current chain already does). The quotient
    remains as internal reachability machinery.
  * **(W — expensive):** re-base the quotient guard from `WfOpA` (accuracy) to
    a Faithful/rehome-correct guard so guarded = raw on disciplined enums; the
    plan doc's Gate (a) verdict ("the invariant is Faithful, not accurate")
    pointed here, and `general_swap_bothFaithful` covers the commutation VC —
    but all four instance VC bundles re-prove. Only worth it if a
    guarded-adequacy statement is independently wanted.

  **✅ THE RAW-≈ CAPSTONE IS BUILT (commits 26d5707 + fc41f73, kernel-clean).**
  * `GenericEqQuotient_H.lean` — `IsCanonicalStateEqH` (witness clause = abstract
    delivery discipline `H`; RGA: `CanonFoldOK [] init_st`), `EqJoinLemma3C_H`,
    congr + extend (`hHext` explicit).
  * `GoodConfig3H.lean` — `GoodConfig3S` (structural invariant, standalone step
    preservations; the unmaintainable guarded canonical clause is gone),
    `IsCanonicalStateH`, **`IsRALinearizable3Eq`** (the raw-≈ target: every
    version's class is `qmk` of a representative = raw `do_`-fold of a
    `lo`-respecting linearization, up to `≈`), the reachability induction, and
    `RA_linearizable_up_to_eq_H`.
  * `RGA_Skeleton3.lean` — `rgaJoinH_of_canon` (the H-join with **union witness
    `ρ₀ ++ π₀` itself**: discipline = `canonFoldOK_concat`, respects = the
    LCA-first assembly, fold = merge by `eq_of_canonMatch2`) and the capstone
    **`rga_RA_linearizable_skeleton3` ⟹ `IsRALinearizable3Eq C`**, residual:
    `hEnum` (K1-shaped; core discharged via `K1_canonFoldOK` ←
    `genDisc2C_of_born`), `hCanon` (fold half derivable as in Skeleton2's
    bridge; merge half = hMergeInputs), `hHext` (discipline snoc at applies —
    engineering), `hBA` (honest premise). Note: `hgenW` is GONE (it only fed
    the now-deleted guard-transparency).

  **Remaining work (all engineering, zero open research):**
  1. `hCanon` reduction re-wire (mirror `hCanon_of_leaves2` + Skeleton2's
     bridge at the Skeleton3 premise chain) + `hMergeInputs` discharge
     (BranchInv-I4 etc.).
  2. `hEnum` final wiring: `K1_canonFoldOK` needs `GenDisc2C` + `hids0` +
     `respects π₀ loOnA` (vis-sort) — thread the honest facts (born accuracy =
     `hborn`, from `hBA`-level reachability; enrich the invariant or the join
     premises to carry them to the merge site).
  3. `hHext` discharge: `canonFoldOK_append` (snoc) + `chainOK_of_accurate` +
     honest id-bookkeeping (WfOpGenQ + ts-freshness).
  4. `hBA`/`hborn` from the execution model; hReady-style plumbing.
  5. README/AgentNotes final update + promote Development→mainline.

  The criss-cross example is the RGA's last word: raw rehoming semantics is
  the ONLY sequentially-replayable semantics for merge unions, and the theorem
  statement now says exactly that.

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
