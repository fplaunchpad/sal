# Agent notes: RGA MRDT attempts

Read this before touching anything under `Sal/MRDTs/RGA*`. It indexes the
several RGA designs in this repo, records which one is proved, and points at the
per-directory `PLAN.md` files for detail.

For the **end-to-end RA-linearizability proof of the tombstone-free RGA in the
generic conditioned metatheory framework** (the active research arc — the
`Sal/ConditionedMRDTs/Development/` files), jump to the task list at the bottom:
[End-to-end RA-linearizability in the generic framework](#end-to-end-ra-linearizability-in-the-generic-framework--task-list).

## The rehoming design (convergence proved; DEMOTED 2026-07-16)

`Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_MRDT.lean` — tombstone-free RGA with
path-carrying operations, flat-set state `map ℕ (ℕ × ℕ)` (id ↦ element, anchor).
Formerly held the plain name `Sal/MRDTs/RGA/` and the canonical seat.
**Demotion (KC decision)**: the convergence capstone is sound, but the design
is sequential-spec-refuted at the `do` level (`tombstone_free_violates_delete_order`;
campaign form `rehoming_seq_refuted` in
`Sal/ConditionedMRDTs/MRDT_Instances/RGA_Rehoming/RGA_SeqSpec_Refuted.lean`):
a single-replica delete reorders survivors. Retained as the framework's
generality stress test and the delete-order countermodel; fused Peritext
still instantiates it (migration to the embed kernel owed, task #85).
**The canonical sequence datatype is the embedded-chain family**
(`Sal/MRDTs/RGA_Embed/` + `MRDT_Instances/EmbedRGA/`, `MRDT_Instances/SidedRGA/`).

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
- Build check: `timeout 300 lake env lean Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_MRDT.lean`

## The sided embed (two-sidedness as a parameter) — LANDED 2026-07-15

`whiteboard/sided-embed-design-note.md` executed in full (tasks #82/#83):
Python sided model battery-clean with L19 flipping clean under the Fugue
policy (`whiteboard/litmus/embed_sided.py`); sided chain-lex kernel
(`Sal/MRDTs/RGA_Embed/Sided_ChainLex.lean`: marker theorem, axiom-free
totality, unique decodability, all-R fragment theorem, in-order-interval
convexity) and the conditioned instance with capstone
`sided_embed_ra_linearizable3` (`MRDT_Instances/SidedRGA/`), all
kernel-clean. Sides are payload to convergence; side *selection* is a
generation policy (RGA and Fugue = two policies over one kernel). Owed:
per-policy intent theorems + the one-sided-from-sided re-derivation
decision (task #84). Design doc §5 of `whiteboard/embed-code-design.pdf`
has the worked L19 example and the encoding.

## The other RGA designs

| Variant | Where it lives | State | Status |
|---|---|---|---|
| **RGA_Embed (embedded-chain RGA)** | `Sal/MRDTs/RGA_Embed/` (kernel + read side) + `Sal/ConditionedMRDTs/MRDT_Instances/EmbedRGA/` (conditioned instance) | absolute immutable birth-chain coordinates (List Bool); Del = pure removal, merge = OR-set + value copy (no climb); instance state = canonical sorted list | **CAPSTONE PROVED** (`embed_ra_linearizable3`, kernel-clean, c812342): RA-lin per version at every honestly reachable configuration, parametric in the code (binary entropy-optimal + unary instances both proved), via the mergeable-queue route — join discharged by canonicity (`e_fold_canon`). Layers 0–3 + §§1–7 all 0-sorry. Remaining per `Sal/MRDTs/RGA_Embed/PLAN.md`: §8 applicable⟹honesty, intent transport, RGA† read-equivalence. Design `whiteboard/embed-code-design.pdf`, Python twin `whiteboard/litmus/embed_tree.py` (lockstep ≡ RGA† 120/120) |
| RGA (original) | `Sal/MRDTs/RGA_with_tombstones/` (main) | tombstone + read-side projection | committed, 0 sorry; different design, kept |
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
- `Sal/MRDTs/RGA_with_tombstones/` (original tombstone-based MRDT, already committed).
- `Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_MRDT.lean` (proved tombstone-free path-carrying
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
metatheory framework. Working files live in `Sal/ConditionedMRDTs/Development/`.

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

  **✅ FURTHER REDUCED (commits 58f7067 + c8e1cbe, kernel-clean):**
  * `RGA_Skeleton3_Leaves.lean` — `canonMatch_of_canonFoldOK` +
    **`hFoldCanon3`** (ALL FOUR CanonMatches from the carried disciplines —
    **no `EngineReady`, no `RefEdge`, no `hReady` leg anywhere**; the entire
    GoodEnumR/reachability-plumbing layer drops out of the main chain) +
    **`hCanon_of_leaves3`** (Skeleton3's `hCanon` ⟸ `hMergeInputs` alone).
  * **HonJ join-context threaded** (`EqJoinLemma3C_H … HonJ`): honest ambient
    facts (same-replica `vis`-totality, `hids0`, generation-discipline content)
    flow from reachable configs (`hHon`) through `GoodConfig3H`'s merge to the
    join, and `hEnum`'s premise chain now carries `HonJ vis events` — closing
    the dischargeability gap (K1's `GenDisc2C`/honest inputs now reachable).

  **✅ hMergeInputs GROUND DOWN (commits 4cfad0d + cde7f42, kernel-clean):**
  * `RGA_MergeCanon_Fix.lean` — **another over-strong premise found and fixed**:
    `canonMatch_merge_of_inputs`' per-survivor `hbwsurv` (birthAnc = 0 ∨
    survives) is FALSE in general (criss-cross node 7's birth anchor = LCA node
    2, dead in the merge). It fires only off the LCA forest, where it IS
    derivable (`bwsurv_of_wf`, propext only: branch-read anchors are
    branch-live by `wf` ⟹ branch-born survivors). Corrected glue
    `canonMatch_merge_of_inputs'`: per-survivor leaf = `CanonBirthBridge` ONLY.
  * `RGA_Skeleton3_Leaves.lean` (rewritten) — `CanonInv` free at every fold ⟹
    σ-forest facts (`Hstay`/`h0`/branch `wf`) and the WHOLE `hins_branch`
    bundle DERIVED (same-id ops identical via `hdts`; a union survivor lives in
    its inserting branch via CanonInv domain-iffs + the causal algebra).
    **Skeleton3's `hCanon` ⟸ THREE leaves: `Hdec` + `hcaus` + `hbridge`.**

  **✅✅ FOCUSED SESSION COMPLETE (commits 1dc59db → 53b1a86: THE DATATYPE
  SIDE IS CLOSED).** `rga_RA_linearizable_final` (`RGA_Final_Assembly.lean`,
  kernel-clean, 0 sorry): RGA RA-linearizability up to ≈ at every reachable
  configuration, residual = `hHon` + `hBA` ONLY (execution-model
  honest-delivery facts). The leaf ledger:
  * **hbridge DISCHARGED** (9cfaf39, `RGA_Hbridge_Discharge.lean`): takes the
    sibling `hcaus` bundle as premise (its `hD` runs through
    `merge_domain_clause` — decouples D from C); home determination via
    `birthAnc`'s if-chain (a survivor is never union-deleted ⟹ home-live;
    home `CanonInv` LiveChain); `home_dead_F_dead` (chain entries are deps ⟹
    in the home enum by closure ⟹ home-dead = home-deleted = union-deleted);
    `first_live_split` at the home-live head `bw`; `bw = 0` ⟹
    `canonAnc_dead_eq_zero` directly, else `canonBirthBridge_via_branchCanon`
    with `hin := hin_of_genDisc`. NO synthetic config (existential `Cfg` as
    in hEnum). NO carrier-3, NO BranchInv.
  * **hcaus + Hdec DISCHARGED** (9b5946a, `RGA_HcausHdec_Discharge.lean`):
    hcaus = 5 membership clauses + 2 provenance clauses via
    `del_target_inserted` (del accurate at its dep fold, target nonzero by
    rgaHonJ's no-root-deletes ⟹ target LIVE there ⟹ inserted). Hdec WITHOUT
    fold induction: anchor = `canonAnc` of the record (`CanonMatch`),
    `canonAnc_mem` picks a chain entry or 0, chain entries are deps
    (`chain_entries_mem`), deps are vis-past, vis is Lamport-monotone
    (rgaHonJ's clock clause). The old item-1 plan (id_mono_doIns'/doDel'
    payload-bound fold variants) was never needed.
    `rga_hMergeInputs_discharged` assembles {Hdec, hcaus, hbridge} = the FULL
    `hCanon_of_leaves3` premise. (Old item-7 concern resolved: rgaHonJ carries
    the no-root-deletes + Lamport clauses since 1dc59db.)
  * **hHext DISCHARGED** (bef33c0, `RGA_HHext_Discharge.lean`) — with the
    SEVENTH interface gap found and fixed: `CanonFoldOK` alone cannot extend
    at a fresh apply (DelOK/ChainOK constrain only LIVE data — a CanonFoldOK
    witness admits dead-target dels / junk chain entries, and a later insert
    reusing such a dead id breaks the no-id-reuse clauses; counterexample
    `ρ = [(5,r,Del [] 7)]` then `Ins` at `t = 7`). Fix: `rgaH` strengthened
    with `HonestPayloads` (SET-level ⟹ perm-invariant: del targets and chain
    entries are root-or-inserted); the union witness lifts it branchwise
    (tiny re-thread, leaf interfaces unchanged). Freshness of `t` against
    `evh` comes from INVERTING `Step3.apply` (`h_fresh_store` covers every
    stored version); fold obligations = `chainOK_of_accurate` /
    `delOK_of_accurate` + `canonFoldOK_append`.
  * **FINAL ASSEMBLY** (53b1a86, `RGA_Final_Assembly.lean`):
    `rga_RA_linearizable_final` = skeleton3 @ rgaHonJ with hEnum :=
    `rga_hEnum_discharged`, hCanon := `hCanon_of_leaves3 rgaHonJ
    rga_hMergeInputs_discharged`, hHext := `rga_hHext_discharged`.
  * **✅ hHon + hBA residual DISCHARGED (a3f4a26, `RGA_Honest_Residual.lean`,
    kernel-clean) — THE HONEST CAPSTONE `rga_RA_linearizable_honest`:** RGA
    RA-lin up to ≈ at every reachable configuration, from a SINGLE per-step
    assumption `HonestDelivery` = (1) *born accuracy* — the delivered op was
    generated accurately against a causal fold of the head version's events
    (the generation discipline forced by tombstone-freedom; the acknowledged
    irreducible assumption) + (2) *born-applicable delivery* (hBA's clauses
    verbatim). Everything else DERIVED:
    - Lamport clocks / timestamp uniqueness / vis-support are STRUCTURAL
      fields of the metatheory `Configuration` (`causal_mono`,
      `timestamps_distinct`, `vis_src`/`vis_tgt`) — dishonest-clock
      configurations are unrepresentable; no induction needed.
    - Nonzero ins-times and nonzero del-TARGETS from the delivered op's own
      `WfOpQ`, extracted from hBA at a representative of the head class
      (`wfOpQ_of_hBA`; the Del clause is ℕ-unsatisfiable at target 0) —
      task #36's content absorbed, no separate WfOpGenQ premise.
    - Nonzero del-TIMES Lamport-derived: an accurate non-root del saw its
      target's insert, so `t > insert-time ≥ 0` forces `t ≥ 1`.
    - `GenDisc2C` at every reachable core = `genDisc2C_of_born` over the
      `HonCore` reachability invariant (finite events + nonzero ids + no
      root dels + born accuracy) maintained through all four Step3 cases;
      the rgaHonJ witness is the re-typed core `coreR` (only `N`'s state
      type differs from `Configuration.core`; nothing reads `N`).
    **Remaining: README + Development→mainline promotion (+ #28 PDF, #29).**

  **Superseded plan (historical; kept for the refutation ledger):**
  1. `Hdec` (σ₀' id-monotonicity): fold invariant along ρ₀ from honest payload
     bounds — needs `id_mono_doIns'`/`id_mono_doDel'` variants (the packaged
     `mono_alloc`/`accurate` premises are from-init-replica-shaped, over-strong
     at δ/union folds — same pattern as everything else; payload-bound-only
     versions suffice: resolve lands in the recorded chain ∪ {0}).
  2. `hcaus`: pure membership transfer (perms + `hdts`) for 5 clauses; the two
     `deletedIn → insertedIn` provenance clauses from HonJ (del-target's
     creator is causally prior ⟹ in the branch by closure).
  3. `hbridge` — per-survivor `CanonBirthBridge`: THE remaining deep item.
     **⚠️ SIXTH over-strong premise found (2026-07-08, pen-level):** the
     four-carrier reduction's carrier 3 (`canonBirthBridge_per_survivor`'s
     `hlive : IsAncPath σ₀' bw (liveSub σ₀' rcSuf)`) is FALSE for an ordinary
     branch-delete + insert-below execution: LCA chain `3→2→1`, branch deletes
     2, then inserts `t` anchored at 3 — the recorded suffix `[1]` skips the
     branch-dead-but-LCA-LIVE node 2, so it is NOT the σ₀' chain (`anc σ₀' 3 =
     2 ≠ 1`); the recorded suffix and the LCA chain agree only AFTER
     `survP F`-filtering (2 is union-deleted). **Do NOT use
     `canonBirthBridge_per_survivor`; use `canonBirthBridge_via_branchCanon`**
     (`RGA_BranchCanon:110`), whose `hin` is the honest filtered form, pinned by
     `hin_of_survFilterEq` to the crisp
     `hFiltEq : rcSuf.filter (survB F) = cw.filter (survB F)`.
     **✅ hFiltEq's KERNEL DISCHARGED (commit baa3272, `RGA_FiltEq.lean`,
     kernel-clean).** The decisive discovery: the coherence statement is
     **F-static** (mentions no fold state), so it needs NO new engine
     invariant — it is established at the survivor's DEPENDENCY fold, where
     `GenDisc2C` (discharged from born accuracy) makes the entire recorded
     chain live. `canonAnc_record_coherence`: the recorded suffix after `bw`
     = the dep-fold-live filter of `bw`'s own record (`isAncPath_suffix` +
     `LiveChain` + `isAncPath_unique`), and the filter's drops are dep-deleted
     ⟹ F-dead (`canonAnc_liveSub_of_deadF`, `depList_trans_mem`).
     `hin_of_genDisc`: the full `hin` of `canonBirthBridge_via_branchCanon` —
     `cw` := σ₀'-live filter of `bw`'s record (LCA `LiveChain`), Step-1 drops
     LCA-deleted (an LCA op's deps live in BOTH branches by closure) ⟹ F-dead.
     **No BranchInv threading needed — the old I4 route is superseded.**
     Remaining hbridge assembly (engineering): `hsplit`/`hpreDead` from the
     home branch's LiveChain + Cfg-level wiring into the hMergeInputs
     discharge (same synthetic-config wiring as hEnum; one wiring serves both).
     **Original discharge plan (now partially superseded) below for reference:**
     (a) `hsplit`/`hpreDead`: from the home branch's `CanonInv` LiveChain
     (free!): `bw = anc σ_home t` is the FIRST home-final-live entry of the
     recorded chain; the prefix is home-dead ⟹ (with the HonJ
     reference-causality clause: chain entries' creators are causally prior,
     hence in the home branch by closure) inserted-and-deleted in the home
     branch ⟹ union-deleted ⟹ `¬ survP F` ✓;
     (b) `hlwf/hawf/hbwf` from `CanonInv` `wf`s ✓; `hD` from the two domain
     clauses (merge_domain_clause + fold CanonMatch, Bool-ext) ✓; `hcm` = hfold ✓;
     (c) **`hFiltEq` — the sole remaining deep leaf**: the recorded suffix is a
     SUBSEQUENCE of the σ₀' chain `cw` (rehome targets stay on the original
     chain: a delete's recorded path lists its target's ancestors, so climbing
     never leaves `cw` — induction over the branch fold), whose omissions are
     branch-deleted ⟹ union-deleted ⟹ `¬ survP F`; conversely `cw`-entries
     missing from the suffix are branch-dead ⟹ `¬ survP F` — so the
     `survB F`-filters coincide. This is BranchInv-I4's content restated
     directly on `CanonInv`'s LiveChain — likely SIMPLER than the old
     `branchInv_of_enum` threading (both routes recorded; pick at build time).
  4. **✅ hEnum DISCHARGED (commit 5cf1f37, `RGA_HEnum_Discharge.lean`,
     kernel-clean, first-try).** `rgaHonJ vis events := ∃ Cfg,
     (Cfg.vis ↔ vis restricted-to-events) ∧ GenDisc2C Cfg events ∧ hids0` —
     the configuration is EXISTENTIAL, and at a real reachable config the
     witness is `C.core` ITSELF (`vis_src`/`vis_tgt` give the restriction) —
     **no synthetic configuration is ever built**. Discharge: branchwise delta
     listing (disjoint filters) + restricted-vis topological sort +
     `K1_canonFoldOK` with `GenDisc2C` restricted events→union via
     `isDepPreC_of_restrict`.
  5. `hHext`: `canonFoldOK_append` snoc + `chainOK_of_accurate` + honest ids.
  6. `hHon`/`hBA` from the execution model (`hHon` = `genDisc2C_of_born` at
     the real core + the Cfg-iff, which is `vis_src`/`vis_tgt`).
  7. `hcaus` note: the provenance clauses (`deletedIn → insertedIn`) derive
     from GenDisc2C at the del's dep-fold (accuracy ⟹ target live ⟹ creator
     among deps ⟹ in-branch by closure) — EXCEPT the degenerate del-of-root
     (`Del _ 0` is born-accurate vacuously); honest events exclude it via
     WfOpQ (`resolve pre ≠ x` fails at x=0), so **rgaHonJ needs a WfOpQ-ish
     clause** (dels have nonzero, provenanced targets) — task #36's content
     surfaces here. Then Hdec (payload-bound id_mono fold) + the hbridge
     assembly (hsplit/hpreDead from home LiveChain + `hin_of_genDisc` +
     `canonBirthBridge_via_branchCanon`) complete hMergeInputs.
  8. README final update + promote Development→mainline.

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
