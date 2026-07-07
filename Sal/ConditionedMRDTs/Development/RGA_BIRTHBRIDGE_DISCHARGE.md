# Discharging #39 — `CanonBirthBridge` per survivor (pen-and-paper first)

*The one genuine remaining depth for end-to-end RGA. Pen-and-paper (this doc) before Lean; then
skeleton-first with the sub-residual admitted.*

## Target

For every survivor `k` of `merge σ₀' σ₁' σ₂'` with recorded insert `(k,r,.Ins e p a) ∈ F` (`F =
ρ₀++π₀`) and `survP F k`:

    CanonBirthBridge σ₀' F (birthAnc σ₀' σ₁' σ₂' k) (a :: p)

via `RGAHinFilterEq.canonBirthBridge_of_branchChain` (built; `hFiltEq` closed). Its real residual is
four carriers: `hsplit`, `hpreDead`, `hlive`, `hsurv`.

## Key structural fact

`a :: p` is a **genuine ancestor chain**: at `k`'s insert, `a` = the anchor and `p` = `a`'s recorded
ancestor path, so `a::p = [a, anc a, anc² a, …]`. `birthAnc = anc(branch) k` sits INSIDE `a::p`
(rehoming climbs up the recorded chain to the first LIVE ancestor). So `rc = rcPre ++ birthAnc :: rcSuf`
with `rcPre` the climbed-past dead prefix, `rcSuf` = `birthAnc`'s recorded rootward tail.

## Case split on where `k` lives

**(i) `k` an LCA node** (`contains σ₀' k`): `birthAnc = anc σ₀' k`. `CanonInv ρ₀ σ₀'` (branch canon,
#37) gives `LiveChain σ₀' k (a::p)` = `IsAncPath σ₀' k (liveSub σ₀' (a::p))`. So `liveSub σ₀' (a::p) =
[birthAnc, anc σ₀' birthAnc, …]`; `birthAnc` = its head, `rcSuf` its tail, `hlive`/`hsplit`/`hpreDead`
fall straight out. **NO BranchInv.**

**(ii) `k` branch-a-new** (`¬contains σ₀' k`, `contains σ₁' k`), `birthAnc` an LCA node
(`contains σ₀' birthAnc`): `CanonInv ρ₁ σ₁'` gives `LiveChain σ₁' k (a::p)` — `k`'s σ₁'-chain. `rcSuf`
= `birthAnc`'s recorded ancestors. `hlive` needs their live-in-**σ₀'** to be `birthAnc`'s **σ₀'**-chain
— the σ₀'↔σ₁' forest bridge = **`BranchInv σ₀' σ₁'` I4** (branch a's anchors agree with σ₀' on shared
live nodes; branch a EXTENDS σ₀', anchors write-once). ← THE SUB-CRUX.

**(iii) `k` branch-a-new, `birthAnc` branch-a-new** (`¬contains σ₀' birthAnc`): `CanonBirthBridge`'s
OFF-FOREST branch (`hbout : ¬contains σ₀' bw → canonAnc F rc = bw`); `hlive` VACUOUS. Need only
`canonAnc F (a::p) = birthAnc`, from the branch `LiveChain` (`resolve σ₁'` = `anc σ₁'` = `birthAnc`)
transported to `canonAnc F` via `resolve_eq_canonAnc` + the survivor-domain agreement.

(Symmetric for branch-b-new via `σ₂'`/`ρ₂`.)

## The two set-algebra carriers (all cases)

* **`hpreDead`** (`∀ c ∈ rcPre, ¬ survP F c`): `rcPre` = entries climbed past = DEAD in the branch
  (`¬contains σᵢ' c`). A recorded ancestor `c` of `k` is inserted before `k` (reference-causality /
  `WfOpGenQ`), so `¬contains σᵢ' c ⟹ deletedIn ρᵢ c ⟹ deletedIn F c ⟹ ¬survP F c`.
* **`hsurv`** (`∀ c ∈ rcSuf, survP F c → contains σ₀' c`): a recorded ancestor that SURVIVES the union
  is an LCA node. `survP F c` ⟹ `¬deletedIn F c` ⟹ `¬deletedIn ρᵢ c`; `c` referenced ⟹ `insertedIn`;
  a live branch node that is a recorded ancestor and survives both branches is in `σ₀'` (OR-set: a
  node live in the merge and referenced by an LCA-or-cross path is LCA). [set-algebra + reference.]

## Verdict — what to admit skeleton-first

The four carriers reduce to:
1. **branch `LiveChain`** (`LiveChain σᵢ' k (a::p)`) — HAVE it from `CanonInv ρᵢ σᵢ'` (#37);
2. **`BranchInv σ₀' σ₁'` / `σ₀' σ₂'` (I4)** — the ONE genuine sub-residual, needed only in case (ii);
3. `survP`/`deletedIn` set-algebra + reference-causality (`WfOpGenQ`).

So `BranchInv` I4 is the true depth. It comes from the branch-decomposition `σ₁' ≈ applySeqR σ₀' Ea`
(GenDisc-free `RGA_update_convergence_noop`, R:=refRel) + threading `branchInv_doIns` /
`branchInv_doDel_crossBranch_sub` (fed by `accurate` = `recPathFaithful_of_accurate`) over `Ea`, then
`≈`-transport to the actual `σ₁'`.

**Skeleton-first plan:** state `canonBirthBridge_per_survivor` taking the branch `LiveChain` +
`BranchInv`-I4 (σ₀'↔σ₁'/σ₂') + the reference/set-algebra facts as ADMITTED hypotheses, DERIVE the four
carriers per case, and feed `canonBirthBridge_of_branchChain`. That precisely types the sub-residual
(`BranchInv` I4) before the branch-decomposition/threading work.

---

## RESOLVED STRUCTURE (2026-07-06) — the carrier construction, mechanization-ready

Read of the actual machinery (`RGA_BranchCanon`, `RGA_HinFilterEq`, `RGA_MergeFoldChain`,
`RGA_SubchainResolve`, `RGA_CanonConvergence`, `RGA_MergeLinearization`) settles every open point. The
mechanization is now a locked plan, not exploration.

### Confirmed facts that reshape the split

1. **The carriers feed ONLY the in-forest branch.**  `canonBirthBridge_of_branchChain` builds
   `CanonBirthBridge l F bw rc = ⟨hbin, hbout⟩` where `hbin` (the `contains l bw = true` case) is the
   ONLY consumer of the carriers — via `hin_via_liveSub l F bw rcSuf hlive hsurv`, itself guarded by
   `contains l bw = true`. `hbout` (`¬contains l bw → canonAnc F rc = bw`) is discharged INTERNALLY by
   `branchCanon_hout` from `hcm : CanonMatch F fold` + `hD` + `betaf_start` — NOT from the carriers.
   ⟹ hlive/hsurv only need to be *honest* when `contains σ₀' bw = true`; when `¬contains σ₀' bw` they
   are provided but never used, so any well-typed filler suffices.

2. **`bw` = first branch-live entry of `a::p`.**  `bw = birthAnc σ₀' σ₁' σ₂' k = anc(birth branch) k`
   (`birthAnc` = `if contains σ₀' k then anc σ₀' k else if contains σ₁' k then anc σ₁' k else anc σ₂' k`),
   and `resolve s = ` "first live candidate, else 0" with `liveChain_resolve : resolve s pre = anc s x`
   under `LiveChain s x pre`. So `bw = resolve(birth branch)(a::p)` = the first birth-branch-live entry
   of `a::p`; `bw ≠ 0` (`hbwne`) ⟹ `bw ∈ a::p`. This gives `hsplit` (`a::p = rcPre ++ bw :: rcSuf`)
   with `rcPre` = the birth-branch-DEAD prefix before `bw`, `rcSuf` = the tail after `bw`.

3. **`CanonInv` (not `CanonMatch`) carries the `LiveChain`.**  `CanonInv F s`'s per-survivor clause is
   `el s t = e ∧ LiveChain s t (a::p)`. Exposed now as `RGACanonMatchReachable.canonInv_reachable_of_facts`
   (kernel-clean, added 2026-07-06) — same hypotheses as `canonMatch_reachable_of_facts`, conclusion
   `CanonInv ρ (applySeqR init_st ρ)`. So each branch `LiveChain σᵢ' k (a::p)` is HAD from the branch's
   `canonInv_reachable_of_facts` (same `hReady`-style facts as `hFoldCanon`).

### The clean 2×-way split — crux isolated to ONE case

Split on `contains σ₀' bw` FIRST (that is what gates the carriers), then on the birth branch of `k`:

* **(A) `¬contains σ₀' bw`** (off-forest `bw`).  `hbin` vacuous; the bridge is `hbout` = internal
  (`branchCanon_hout`). **CORRECTION (2026-07-06):** the earlier "filler via `hlive : IsAncPath σ₀' bw []`
  = `anc σ₀' bw = 0`" is WRONG — it presumes `liveSub σ₀' rcSuf = []`, but a branch-new `bw` whose
  recorded anchor is an LCA node `c ∈ σ₀'` has `rcSuf = c :: …`, `liveSub σ₀' rcSuf = c :: …`, and
  `IsAncPath σ₀' bw (c :: …)` demands `anc σ₀' bw = c` while `bw ∉ σ₀' ⟹ anc σ₀' bw = 0` — FALSE. So one
  must NOT route case A through `canonBirthBridge_of_branchChain` (which forces `hlive` unconditionally;
  this retires my old `RGA_BirthBridge.canonBirthBridge_per_survivor`). Route through
  `RGABranchCanon.canonBirthBridge_via_branchCanon`, whose in-forest obligation
  `hin : contains σ₀' bw = true → ∃cw …` is CONDITIONAL — case A supplies it VACUOUSLY. Done in
  `RGA_BirthBridge_Bundle.canonBirthBridge_bundle` (built, kernel-clean). **NO BranchInv.**  [old case iii]

* **(B) `contains σ₀' bw`** (in-forest `bw`; `bw` is an LCA node).  Need honest `hlive`/`hsurv`.
  Sub-split on `k`:
  - **(B-i) `contains σ₀' k`** (`k` an LCA node): `bw = anc σ₀' k`. `LiveChain σ₀' k (a::p)` (branch
    `CanonInv ρ₀`) gives `IsAncPath σ₀' k (liveSub σ₀' (a::p))`; peeling the head `bw` yields
    `hlive : IsAncPath σ₀' bw (liveSub σ₀' rcSuf)` and `hsurv` (survivors of `rcSuf` live in σ₀' = the
    `liveSub` membership). **NO BranchInv.**  [old case (i)]
  - **(B-ii) `¬contains σ₀' k`, `k` branch-new** (say branch a, `contains σ₁' k`): `bw = anc σ₁' k`,
    and `bw ∈ σ₀'`. `LiveChain σ₁' k (a::p)` gives `k`'s **σ₁'**-chain; `hlive` needs `bw`'s **σ₀'**-chain
    and `hsurv` needs `rcSuf`-survivors live in **σ₀'**. The σ₁'→σ₀' transport IS **`BranchInv σ₀' σ₁'`**:
    I4 (`climb (anc σ₀') (dom σ₁') (anc σ₀' bw) = anc σ₁' bw`) reproduces `bw`'s σ₀'-anchor from its
    σ₁'-anchor on shared live nodes, and I3 (`anc σ₁' bw = 0 ∨ contains σ₀' (anc σ₁' bw)`) keeps the
    climb inside the σ₀' forest. **← THE SOLE CRUX.**  (Symmetric branch b via `BranchInv σ₀' σ₂'`.)  [old case (ii)]

`hpreDead` (`∀ c ∈ rcPre, ¬survP F c`) in ALL cases: `rcPre` = birth-branch-dead entries; dead-in-branch
+ recorded-ancestor ⟹ `deletedIn ρᵢ c` ⟹ (`ρᵢ ⊆ F` for the branch's own dels) `deletedIn F c` ⟹
`¬survP F c` (`notSurv_of_branchDeleted`, RGA_BranchCanon §1). Pure set-algebra + reference-causality.

### The bundle lemma (DONE) + the `hRc` producer to write next

**DONE — `RGA_BirthBridge_Bundle.canonBirthBridge_bundle` (built, kernel-clean).** Produces the FULL
per-survivor `hbridge` shape that `RGA_MergeCanon.canonMatch_merge_of_inputs` consumes, from: forest
invariants + `hD` + `hcm` (union canon) + `h0`, and the per-survivor residuals `hSurv` (survivor
domain), `hRoot` (`bw=0 ⟹ canonAnc F rc = 0`), `hBwSurv` (0-or-survivor), and `hRc` — the
recorded-chain reconstruction `∃ rcPre rcSuf, split ∧ dead-prefix ∧ (contains σ₀' bw ⟹ chain
reconciliation)`. The `bw=0`/case-A subtleties are handled here; `BranchInv` content lands ONLY in
`hRc`'s guarded reconciliation.

**NEXT — `hRc` producer** (case-B, `contains σ₀' bw`): produce
`∃ cw, IsAncPath σ₀' bw cw ∧ canonAnc F cw = canonAnc F rcSuf` (= `hin_via_liveSub` with
`cw := liveSub σ₀' rcSuf`, needing `hlive`/`hsurv`), plus the `split`/`dead-prefix`, from ADMITTED:
  - `hCIᵢ : CanonInv ρᵢ σᵢ'`  (HAVE via `canonInv_reachable_of_facts` → per-survivor `LiveChain σᵢ' k (a::p)`);
  - `hBI1 : BranchInv σ₀' σ₁'`, `hBI2 : BranchInv σ₀' σ₂'`  (THE crux, admit → discharge via BD);
  - list surgery `bw = first branch-live entry of a::p ⟹ split` (`resolve`/`liveSub`/`takeWhile`);
  - set-algebra: `deletedIn ρᵢ`→`¬survP F` for the dead prefix.
This is where `BranchInv σ₀'σ₁'/σ₀'σ₂'` gets consumed (case B-ii); writing it PINS the exact `BranchInv`
facts (I4 climb + I3 stay) needed, before the branch-decomposition discharge.

### BranchInv discharge (the last research step, after the skeleton)

`BranchInv σ₀' σ₁'` from **branch-decomposition** `σ₁' ≈ applySeqR σ₀' Ea` (`Ea` = branch-a's δ-events,
via GenDisc-free `RGA_update_convergence_noop`, `R := refRel`) + threading `branchInv_refl` (base
`BranchInv σ₀' σ₀'`) through `branchInv_doIns` / `branchInv_doDel_crossBranch_sub` over `Ea` (accuracy
fed by `recPathFaithful_of_accurate`), then `≈`-transport (`BranchInv` reads `el`/`anc`/`contains`, all
`≈`-invariant) to the actual `σ₁'`. This is the genuine remaining depth; born-applicability of `Ea` is
now FREE from the causal merge.
