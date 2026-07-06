# Discharging `RgaEqJoinResidualLit` — the RGA merge=fold identity (WALL 1, final)

*The sole remaining obligation for end-to-end RGA `≈`-linearizability. Pen-and-paper FIRST
(this doc), then mechanization against it. Companion to `WALL1_ANALYSIS.md`, which resolved the
`≈`-vs-literal obstruction (GAP-1) via `mergeFold_transport`; this doc discharges what remains.*

## 0. Where we stand

`RGA_EqJoin_NF_Residual.rga_eqJoin_of_residualLit_NF` (kernel-clean) reduces `EqJoinLemma3C_NF` for
the RGA to `RgaEqJoinResidualLit W`:

> from three born-applicable deliveries `ρ₀` (enumerates `ev₁∩ev₂`), `ρ₁` (enumerates `ev₁`),
> `ρ₂` (enumerates `ev₂`) — all `loOnEq W vis`-respecting and `noopFeasible` from `init_st` —
> produce a delta enum `π₀` with
>
> - `listPermOf π₀ δ`, `respects π₀ (loOnEq W vis δ)`, `noopFeasible π₀ σ₀'`   **(δ-enum)**
> - `eq (merge σ₀' σ₁' σ₂') (applySeqR σ₀' π₀)`                                **(‡, merge=fold)**
>
> where `δ := (ev₁∪ev₂)\(ev₁∩ev₂)`, `σ₀' := applySeqR init_st ρ₀` (LCA fold), `σ₁' := applySeqR
> init_st ρ₁`, `σ₂' := applySeqR init_st ρ₂` (literal branch folds). `W := WfOpA` at instantiation.

Everything downstream (`mergeFold_transport`, `isCanonicalStateEqNF_union_of_fold`,
`RA_linearizable_up_to_eq_NF`, `rga_RA_linearizable_NF`) is discharged and kernel-clean. This is the
last piece.

The `merge` characterizations are **definitional** (`RGA_Reachability_Invariant`, all `rfl`):

    contains (merge l a b) t = survivors l a b t
    survivors l a b = (dom l ∩ dom a ∩ dom b) ∪ (dom a \ dom l) ∪ (dom b \ dom l)     -- OR-set
    anc (merge l a b) t = climb (anc l) (survivors l a b) (birthAnc l a b t)
    birthAnc l a b t = if contains l t then anc l t else if contains a t then anc a t else anc b t

So (‡) is precisely: **the δ-fold `applySeqR σ₀' π₀` has the OR-set as its domain and the climbed
birth-anchor as each survivor's anchor** — per id.

## 1. The engine: `eq_merge_two_sided_final` (order-agnostic, already proved)

`RGA_MergeFoldChain.eq_merge_two_sided_final` proves (‡) from SIX pieces, for ARBITRARY `l a b`, an
abstract order `lo`, event set `ev`, reference enum `π₀`, target enum `π`, and applied set `F`. Its
`lo` is abstract throughout, so we instantiate `lo := loOnEq rgaEqEquiv' WfOpA vis δ`, `ev := δ`,
`l := σ₀'`, `a := σ₁'`, `b := σ₂'`, `π := π₀ := π` (reference = target, so the conclusion is exactly
(‡)), and `F := ρ₀ ++ π₀` (the total applied set from `init_st`, since `applySeqR σ₀' π₀ =
applySeqR init_st (ρ₀ ++ π₀)` by `applySeqR_append`).

Side conditions (all from `Inv` of the folds, via `rga_invCong` / reachable invariants): `wf σ₀'`,
`id_mono σ₀'`, `wf σ₁'`, `wf σ₂'`, `contains σ₀' 0 = false`. These hold because `σᵢ'` are reachable
(born-applicable folds preserve `Inv`), and `Inv ⟹ wf ∧ id_mono ∧ ¬contains·0` (RGA reachability
invariant). **Tractable — no research risk.**

The six pieces (`l=σ₀'`, `a=σ₁'`, `b=σ₂'`, `p := applySeqR σ₀' π₀`, `F := ρ₀++π₀`):

| # | piece | statement | discharge route | risk |
|---|-------|-----------|-----------------|------|
| hcm | CanonMatch | `CanonMatch F p` | `canon_fold` + `canonFoldOK_of_noopFeasible` on `ρ₀++π₀` | LOW |
| hMSR | swap facts | distinct/wf/id_mono/fresh/`Faithful`/`NoFreshClash` for `loOnEq`-pending pairs at every prefix `applySeqR σ₀' pre` | `conditioned_premises` (all but `Faithful`) + `Faithful`-from-accuracy | MED |
| hD | OR-set = live-set | `survivors σ₀' σ₁' σ₂' k = contains p k` | §3 below | MED |
| hB | single-branch inv | `BranchInv σ₀' p` | thread `branchInv_doIns` / `branchInv_doDel_crossBranch_sub` over `π₀` | MED |
| hBE | branch-new element | `el p k = birthEl σ₀' σ₁' σ₂' k` (branch-new survivors) | §4 below | MED |
| hbridge | birth-anchor bridge | `CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' k) (a_k::p_k)` (branch-new survivors) | `canonBirthBridge_via_branchCanon`→`hin_of_survFilterEq`→`hFiltEq` (accuracy) | MED-HIGH |

## 2. The δ-enum (obligation, two genuine sub-questions)

`RgaEqJoinResidualLit` must PRODUCE `π₀` with `listPermOf π₀ δ`, `respects π₀ (loOnEq WfOpA vis δ)`,
`noopFeasible π₀ σ₀'`. There is **no existing loOnEq-enum-existence lemma** (only
`exists_loOnA_noopFeasible_enum`, which is loOnA-respecting and `noopFeasible` from `init`, both
wrong here). Two sub-obligations:

- **(δ-A) loOnEq acyclicity on δ.** `loOnEq` (GenericEqQuotient:428) is
  `(vis ∧ ¬eqCommute) ∨ (vis-incomparable ∧ rc=Fst_then_snd ∧ ¬∃ later-non-commuting)`. Disjunct-1
  is a sub-relation of the strict order `vis` (acyclic). Disjunct-2 is an `rc`-tiebreak among
  vis-incomparable pairs, guarded by "the source has no non-`≈`-commuting `vis`-future in `ev`".
  Acyclicity is *plausible by design* (the guard makes disjunct-2 sources near-sinks) but **is not
  proved anywhere**. Needed: `∀ l' ⊆ δ, l' ≠ [] → ∃ m ∈ l', ∀ y ∈ l', ¬ loOnEq … y m` (a loOnEq-minimal
  element of every sublist), then `exists_respecting` gives the enum. — **OPEN sub-question 1.**

  *Escape hatch:* we already HAVE `loOnEq`-respecting enums `ρ₁` (of `ev₁`) and `ρ₂` (of `ev₂`).
  A δ-enum might be BUILT by interleaving the `ev₁\ev₂`-subsequence of `ρ₁` with the `ev₂\ev₁`-sub of
  `ρ₂`, rather than a fresh topological sort — but merging two respecting subsequences into one
  respecting enum of the union is itself a lemma (needs: no `loOnEq` edge crosses between the two
  δ-halves backwards, i.e. concurrent branch-new events don't `loOnEq`-order across branches, which
  holds iff they `≈`-commute — the merge's whole premise). This is the cleaner route; still an
  obligation.

- **(δ-B) `noopFeasible π₀ σ₀'`.** Each δ event must be `applicable`-or-no-op at `applySeqR σ₀' pre`.
  The branch deliveries give applicability at `applySeqR init_st (ρᵢ-prefix)`. Transporting to
  `σ₀'`-prefixes needs: (i) `σ₀' ≈` the `ev₁∩ev₂`-fold inside `ρ₁`/`ρ₂` (canon convergence,
  `RGA_update_convergence_eq`), and (ii) `applicable` is `≈`-invariant. **(ii) is ALREADY PROVED** —
  `RGA_EqQuotient.accurate_eq_iff` (`eq s s' → (accurate o s ↔ accurate o s')`) + `fresh_ts_eq_iff`
  (both already load-bearing for the `QSig` congruence VC `applicable_congr`). So `applicable o` is
  `≈`-invariant, and δ-B is NOT research-open — it reduces to the mechanical "branch events stay
  applicable-or-noop across the canon-convergence transport", using the interleave construction
  (§8.2) where the events ARE ρ₁/ρ₂'s own branch events (already applicable at their branch
  prefixes). **RESOLVED (down to mechanization).**

So of the two flagged sub-questions, **δ-B dissolves into existing infrastructure**; only **δ-A
(loOnEq-δ acyclicity / interleave-respecting) is genuinely open**, and it hinges on `loOnEq`'s
`ev`-antimonotonicity (`loOnEq_antimono`, already built: a SMALLER `ev` weakens the disjunct-2 guard
`¬∃e₃∈ev`, so `loOnEq …δ` has ⊇ the disjunct-2 edges of `loOnEq …ev₁` on δ-events) plus the
cross-branch `rc`-tiebreak among concurrent branch-new pairs. The interleave (§8.2) must be chosen to
respect that cross-branch `rc`-order; a consistent choice exists because `rc` is a decidable
tiebreaker and cross-branch disjunct-1 edges vanish (concurrent branch-new events `≈`-commute — the
merge's own convergence premise). Mechanizing δ-A = proving the chosen interleave `respects
(loOnEq …δ)`; this is the sole new research obligation of the δ-enum.

## 3. hD — OR-set = δ-fold live-set

Goal: `survivors σ₀' σ₁' σ₂' k = contains (applySeqR σ₀' π₀) k`, i.e. `dom(merge) = dom(δ-fold)`.

`contains` is event-determined and `≈`-invariant (it reads only `domain`, closed under `do_`
insert/delete regardless of anchor state). So this piece does NOT need the anchor machinery.

Argument (per id `k`):
- **k ∈ dom σ₀' (LCA node).** In `survivors` iff `k ∈ dom σ₁' ∧ k ∈ dom σ₂'` (delete-wins: survives
  iff not deleted in either branch). In the δ-fold: `k` starts live (in `σ₀'`), and `π₀` applies the
  branch-new events = (branch-a `Del`s) ⊎ (branch-b `Del`s) ⊎ (branch inserts). `k` is removed iff a
  branch-a `Del k` OR branch-b `Del k` is in `π₀`. A branch-a `Del k` is in `π₀` iff `k ∉ dom σ₁'`
  (`σ₁'`=fold ρ₁ deleted it) — matching "not in dom σ₁'". Symmetric for b. So `contains(δ-fold) k =
  (k∈dom σ₁' ∧ k∈dom σ₂')` = survivors. ✓
- **k ∉ dom σ₀', k ∈ dom σ₁' (branch-a-new, live).** In `survivors` via `dom σ₁' \ dom σ₀'`. In the
  δ-fold: `k`'s branch-a `Ins` is in `π₀` and no later `Del k`, so live. ✓ (symmetric for b-new.)
- **k in neither / deleted-new.** Not in survivors; not in δ-fold. ✓

Mechanization: induction on `π₀` tracking `contains (applySeqR σ₀' pre) k` against the branch-event
membership, using that `π₀`'s events are exactly `(ρ₁-branch-a events) ⊎ (ρ₂-branch-b events)` and
`contains σ₁' k` is determined by ρ₁'s events on `k`. The **branch-decomposition lemma** below is the
crux support. Depends on the δ-enum being pinned to the branch events (so we know `π₀`'s event
multiset). **MED.**

### The branch-decomposition support lemma (shared by hD/hB/hBE)

`dom σ₁'`, `el σ₁'`, `anc σ₁'` on branch-a-new nodes are determined by ρ₁'s branch-a events (those in
`ev₁\ev₂`), because the LCA-events of ρ₁ fold to `≈ σ₀'` and the branch-a events extend it. Formally:
`σ₁' ≈ applySeqR σ₀' Ea` where `Ea` = the `ev₁\ev₂`-subsequence of `ρ₁` (canon convergence,
`RGA_update_convergence_eq` at `ev₁`, splitting `ρ₁` vs `ρ₀++Ea`). Since `contains`/`el`/`anc`-on-
survivors are the observable equalities of `≈` (`eq` = per-id el+anc on the shared domain), the
branch-fold observables equal those of `applySeqR σ₀' Ea`. **This is where "literal branch fold"
earns its keep: `applySeqR σ₀' Ea` is `σ₀'` genuinely extended by branch-a events, so `branchInv_*`
and `birthEl`/`birthAnc` apply.** π₀ interleaves `Ea` and `Eb`.

## 4. hBE — branch-new element

Goal (branch-new survivor `k`, `¬contains σ₀' k`): `el (δ-fold) k = birthEl σ₀' σ₁' σ₂' k` where
`birthEl = el σ₁' k` if `k∈dom σ₁'` else `el σ₂' k`.

A branch-a-new `k`'s element is the `e_k` recorded by its `Ins` event, unchanged by any later op
(elements are write-once in the RGA). Both `σ₁'` (via ρ₁) and the δ-fold (via π₀) apply the SAME
`Ins e_k p_k a_k` event for `k`, so `el (δ-fold) k = e_k = el σ₁' k = birthEl`. Uses the
branch-decomposition lemma to identify the events. **MED.**

## 4bis. PROBE VERDICT (2026-07-06): the anchor residual is bounded assembly, NOT a research wall

Timeboxed probe of "does `accurate` collapse the anchor coincidence?" — verdict recorded here.

* **`hFiltEq` (the cross-forest filter coincidence) is CLOSED**, kernel-clean, in
  `RGA_HinFilterEq.hin_via_liveSub` (`IsAncPath_unique` + `liveFilter_surv`). Route A
  (`foldChain_of_goodFold`, RGA_MergeBranchNew) is **superseded**, not the live residual.
* **`accurate` unblocks the per-event step**: `recPathFaithful_of_accurate` (`accurate ⇒
  RecPathFaithful`) is exactly what powers `branchInv_doDel_crossBranch_sub` (cross-branch `Del`
  preservation) — which had NO valid supplier on the old `GenDisc2CEq` path. The re-base does its job.
* **Remaining = bounded assembly (~3–4 lemmas), not stuck.** `canonBirthBridge_of_branchChain` closes
  the anchor bridge given carriers `hlive : IsAncPath l birthAnc (liveSub l rcSuf)` + `hsurv`. Those
  need `BranchInv l (applySeqR l Ea)` THREADED over the branch event list (`branchInv_doIns` +
  `branchInv_doDel_crossBranch_sub`, both proved; the latter now fed by `accurate`) + the
  branch-decomposition `σ₁' ≈ applySeqR l Ea` (from GenDisc-free `RGA_update_convergence_noop`). The
  one risk is the l-extension representation (the ρ₀-prefix/`loOnEq` subtlety) — but `BranchInv`
  threading needs only the EVENT structure, not `loOnEq`-respecting, so it is cleaner there.
* This maps into the canonical route (`RGA_EndToEnd.lean`): `hCanon`'s merge-half `CanonMatch F
  (merge …)` anchor clause = this bridge; its domain clause = `survivors = survP` set-algebra.

## 5. hbridge — birth-anchor coincidence (the sharp piece)

Goal (branch-new survivor `k` with recorded insert `(k,r,.Ins e_k p_k a_k) ∈ F`):
`CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' k) (a_k :: p_k)` — the birth-anchor
`bw := birthAnc = anc σ₁' k` (branch-a's stored anchor for `k`) and its LCA-forest ancestor chain
resolve, against `F`, to the same survivor as `k`'s RECORDED chain `a_k::p_k`.

Reduction (already mechanized): `canonBirthBridge_via_branchCanon` → `hin_of_survFilterEq` reduces
this to **`hFiltEq`: `rcSuf.filter (survB F) = cw.filter (survB F)`** — the surviving recorded
ancestors of `bw` equal its surviving LCA-forest ancestors. This is a pure event-set/forest identity,
discharged by **path accuracy**: because ρ₁ is born-applicable (`WfOpA ⊇ accurate`), every recorded
insert in `σ₁'` has its recorded path = the genuine live ancestor chain at capture
(`RecPathFaithful` / `subchain_resolve`), so the recorded chain and the forest chain have the same
surviving subsequence. **This is the piece the whole re-base was FOR** — `accurate` from `WfOpA`
discharges it; on the old `GenDisc2CEq` path it was the un-dischargeable wall. **MED-HIGH** (the
accuracy→`hFiltEq` lemma must be assembled from `RGARecPathFaithful` + `RGA_HinFilterEq`).

## 6. hB — single-branch invariant on the δ-fold

Goal: `BranchInv σ₀' (applySeqR σ₀' π₀)`. `BranchInv l p` = on the shared live domain, `p`'s element
and anchor agree with `l`-forest expectations (I2/I4) + anchor stays in `{0}∪dom l`.

Thread over `π₀`'s events from `BranchInv σ₀' σ₀'` (trivial base): each `Ins` preserves it by
`branchInv_doIns` (fresh id, seats under a live-or-0 anchor); each `Del pre x` preserves it by
`branchInv_doDel_crossBranch_sub`, which needs `RecPathFaithful (Del pre x) (applySeqR σ₀' pre)` —
supplied by accuracy of ρ (born-applicable), the SAME accuracy hook as hbridge. **MED.**

## 7. hcm / hMSR — the reachability pieces

- **hcm** `CanonMatch (ρ₀++π₀) (applySeqR σ₀' π₀)`: `canon_fold` gives `CanonMatch F (disciplined
  fold of F)`; discipline (`CanonFoldOK (ρ₀++π₀)`) from `canonFoldOK_of_noopFeasible` (already built,
  order-agnostic) applied to the combined delivery `ρ₀++π₀` as an enum of `ev₁∪ev₂` — needs `ρ₀++π₀`
  `noopFeasible` from `init` (✓: ρ₀ noopFeasible from init, π₀ noopFeasible from σ₀'=fold ρ₀,
  compose via `noopFeasible_append`) + `RefEdge`/`GoodEnumR`/id-uniqueness (from the union closure).
  **LOW-MED.**
- **hMSR**: for every `loOnEq`-pending pair `(x,y)` at prefix `pre`, the swap facts. `distinct_ts`,
  `¬contains·0`, `wf`, `id_mono`, `fresh_ts x/y`, `NoFreshClash x/y y/x` all come from
  `conditioned_premises` (the born-applicable reachability oracle) — but that oracle is stated for
  folds from `D.init`, and here the fold is from `σ₀'` (=`applySeqR init ρ₀`), so we compose
  `pre' := ρ₀ ++ pre` and read the premises at `applySeqR init pre'`. The two `Faithful x/y` facts
  are NOT emitted by `conditioned_premises` (it gives `NoFreshClash`, not `Faithful`) — they need the
  accuracy-at-prefix argument (`faithful_of_recPathFaithful` on the born-applicable prefix). **MED.**

## 8. Mechanization order (dependency-sorted) and honest risk

1. **Branch-decomposition lemma** (`σ₁' ≈ applySeqR σ₀' Ea`, `σ₂' ≈ applySeqR σ₀' Eb`; π₀ = interleave
   of `Ea`,`Eb`). Gates hD/hB/hBE. Uses `RGA_update_convergence_eq`. — do first.
2. **δ-enum** (δ-A acyclicity, δ-B noopFeasible-from-σ₀'). The two open sub-questions. Can proceed
   with (1)'s `Ea`/`Eb` interleave as the *construction* (sidesteps δ-A's fresh topo-sort) — then
   δ-A becomes "the interleave respects loOnEq" and δ-B becomes "the interleave is noopFeasible from
   σ₀'", both provable from ρ₁/ρ₂'s respecting+feasible + cross-branch `≈`-commutation.
3. **hcm, hMSR** (reachability, from `conditioned_premises` + accuracy).
4. **hD, hBE** (containment/element, from branch-decomposition).
5. **hB** (branch-inv threading, `branchInv_doDel_crossBranch_sub` + accuracy).
6. **hbridge** (accuracy → `hFiltEq`, the sharp one).
7. **Assembly**: `eq_merge_two_sided_final` + side-conditions → (‡) → `RgaEqJoinResidualLit`.

**Risk assessment.** No piece is believed FALSE — the design is sound (born-applicable `accurate`
discharges every anchor obligation; the old wall was `GenDisc2CEq`, now bypassed). The two genuine
research unknowns are the δ-enum sub-questions (§2), and both have a plausible construction-based
route (interleave ρ₁/ρ₂'s branch subsequences, §8.2) that reduces them to cross-branch
`≈`-commutation — the merge's own premise. This is a multi-part mechanization (≈8 lemmas over the
existing machinery), NOT a single grind; each piece is independently verifiable and the assembly
(§1) is a fixed order-agnostic engine.
