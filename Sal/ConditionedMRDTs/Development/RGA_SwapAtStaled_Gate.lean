import Sal.ConditionedMRDTs.Refutations.RGA_Rehoming_Gate

/-!
# Task #11 · Milestone 1 — the STALED-SWAP gate

Bubble re-architecture, SCOPE / Route B, Milestone 1
(`CONDITIONED_METATHEORY_PLAN.md`, "Bubble re-architecture — SCOPE").

The generic convergence bubble swaps an adjacent `loOnA`-incomparable pair
`(a,b)` **at the fold state `σ` they sit at**, and the RGA's `commutes_with'`
(`RGA_Tombstone_Free_MRDT.lean:331`) can discharge that swap ONLY when BOTH `a`
and `b` are `accurate` at `σ`.  The decisive sub-question this file decides on the
real RGA `do_`:

> Does the swap `do_ (do_ σ a) b = do_ (do_ σ b) a` (its `eq`-version) hold at a
> **staled** `σ` — a `σ` where one of `a,b` is NOT `accurate` because a prior
> event deleted its anchor — or only at both-`accurate` `σ`?

## Construction (reuses `RGA_Rehoming_Gate`)

* `σ_staled := do_ baseAB delA` — the base chain `root → node1 → node2` after
  `delA` deletes `node1` (id `1`), **rehoming** `node2` (id `2`) up to the root.
* `a := insC = (3,1,Ins 30 [] 1)` — the concurrent insert anchored at `node1`.
  At `σ_staled` its anchor `node1` is gone, so it is **INACCURATE**
  (`not_accurate_insC_sigmaStaled`, reusing the gate's `accurate_insC_after_delA`).
  Because its carried path is `[]`, its `resolve` collapses to the root `0`
  *unconditionally* — the staled insert becomes a **constant** insert `3 ↦ (30,0)`.
* `b` — an event that IS `accurate` at `σ_staled` and `loOnA`-incomparable with
  `insC` (different replica, no vis edge).  Two concrete choices, both tested:
  * `insD = (5,2,Ins 40 [] 2)` — a fresh insert anchored at the rehomed `node2`
    (live, now a child of the root);
  * `delD = (5,2,Del [] 2)` — a delete of the rehomed `node2`.
  (Note: `node2`'s anchor is `1` at `baseAB` but `0` at `σ_staled`, so any such
  `b` is `accurate` at `σ_staled` but NOT at `baseAB`; and `insC` is `accurate`
  at `baseAB` but not at `σ_staled`.  So `insC` and `b` are **never jointly
  `accurate`** at any reachable state — the pair the bubble may never discharge
  through `commutes_with'`, yet whose swap we test directly.)

## VERDICT — ∀-STATE (the staled swap HOLDS), leaning; evidence, not proof

Every staled swap constructible under the gate's constraint ("`b` `accurate` at
`σ_staled`, concurrent with `insC`") HOLDS on the real `do_`:

* `staled_swap_holds`      — `insC` vs `insD` (Ins): `eq`, in fact literal `Eq`
  after `upd_comm`.
* `staled_swap_holds_del`  — `insC` vs `delD` (Del): `eq`.

The mechanism is structural, not accidental:
1. `insC` carries path `[]`, so once `node1` is dead (permanently — no fresh `b`
   can revive id `1`) its `resolve (1 :: [])` collapses to `resolve [] = 0`
   *independently of the state*.  The staled `insC` is the **constant** update
   `3 ↦ (30,0)`.
2. `b` `accurate` at `σ_staled` references only nodes live in `σ_staled`
   (`node2` or the root) — never `insC`'s fresh id `3`.  So the classic
   non-commutation ("an insert anchored at the OTHER op's freshly created id",
   `RGA_Tombstone_Free_MRDT.lean:306`) is **structurally excluded** by requiring
   `b` `accurate`: to anchor at id `3`, `b` would have to be inaccurate at
   `σ_staled` (id `3 ∉ σ_staled`).
3. The one interaction channel for a `Del` — reparenting `insC`'s node `3` — can
   fire only when `b` deletes the root, and `accurate` forces such a `Del`'s
   reparent target to the root `0`, which is exactly where `insC` already anchors
   node `3`.  So even that case commutes.

This selects **Route A (easy)**: the RGA supports a *stronger, unconditioned*
swap VC on the constrained pair (drop the "`a` accurate" premise; keep only the
"`b` accurate" premise), so `applySeq_swap_loOnA_incomparable_C`'s applicability
side condition on the staled event can be dropped.

**Honesty caveat.** This is EVIDENCE for the specific staled shape the gate
fixes (`a = insC`, path `[]`, `b` `accurate`), not a universal proof.  The
failure mode the gate's `b`-`accurate` requirement excludes is real
(`RGA_Rehoming_Gate.staled_ins_not_applicable`; `G2_Transport_Probe.folds_differ`):
a *both-staled* swap, or a swap whose staled op carries a non-empty path that
re-anchors state-dependently, is outside this gate's constraint and may still
fail.  See `staled_swap_would_fail_if_b_inaccurate` for the witnessed boundary.

## Cross-check — global convergence holds (it must; the RGA is a real CRDT)

`full_enum_with_b_converges` exhibits two full `loOnA`-respecting enumerations of
`{insA,insB,delA,insC,insD}` — sharing the prefix `[insA,insB,delA]` that folds
to `σ_staled`, then transposing `insC`/`insD` — that converge.  Here the pointwise
swap and the global convergence *coincide* (the pointwise swap holds), so this
distinguishes the benign "∀-STATE / Route A" world from the catastrophic
"global convergence fails" world: global convergence HOLDS.

## Axiom status
Every headline decl is kernel-clean (`propext, Classical.choice, Quot.sound`
only — no `sorryAx`, no `native_decide`/`ofReduceBool`).  The imported
`Merge_Linearization_Set` sorries are not transitively touched.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGASwapAtStaled

open Sal.Emulation
open Sal.ConditionedMRDTs.RGARehomingGate
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.G2Probe (folds_differ insOpE delOpE)

/-! ## §1  The staled state and the two concurrent, `accurate` events -/

/-- The staled fold state: `root → node1 → node2` after `delA` removes `node1`,
rehoming `node2` up to the root.  Concretely `{ 2 ↦ (20, 0) }`. -/
def sigmaStaled : concrete_st := do_ baseAB delA

/-- `b` (choice 1): a fresh insert (id `5`) anchored at the rehomed `node2`. -/
def insD : Op app_op_t := (5, 2, .Ins 40 [] 2)
/-- `b` (choice 2): a delete of the rehomed `node2`. -/
def delD : Op app_op_t := (5, 2, .Del [] 2)

/-! ## §2  State facts about `σ_staled` -/

theorem contains_baseAB_2 : contains baseAB 2 = true := by
  rw [baseAB_eq, lemma_InDomUpd1]; simp

/-- `node1` (id `1`) is gone at `σ_staled` (reuse the gate). -/
theorem contains_sigmaStaled_1 : contains sigmaStaled 1 = false :=
  contains_node1_after_delA

/-- `node2` (id `2`) survives at `σ_staled`. -/
theorem contains_sigmaStaled_2 : contains sigmaStaled 2 = true := by
  show contains (do_ baseAB (4, 0, app_op_t.Del [] 1)) 2 = true
  rw [contains_doDel, contains_baseAB_2]; simp

/-- `node3` (id `3`, `insC`'s creation) is absent at `σ_staled`. -/
theorem contains_sigmaStaled_3 : contains sigmaStaled 3 = false := by
  show contains (do_ baseAB (4, 0, app_op_t.Del [] 1)) 3 = false
  rw [contains_doDel, contains_baseAB_3]; simp

/-- `node5` (id `5`, `b`'s creation) is absent at `σ_staled`. -/
theorem contains_sigmaStaled_5 : contains sigmaStaled 5 = false := by
  show contains (do_ baseAB (4, 0, app_op_t.Del [] 1)) 5 = false
  rw [contains_doDel]
  have : contains baseAB 5 = false := by rw [baseAB_eq, lemma_InDomUpd1, lemma_InDomUpd1]; simp [init_st]
  rw [this]; simp

/-- The root sentinel is never stored at `σ_staled`. -/
theorem contains_sigmaStaled_0 : contains sigmaStaled 0 = false := by
  show contains (do_ baseAB (4, 0, app_op_t.Del [] 1)) 0 = false
  rw [contains_doDel, contains_baseAB_0]; simp

/-- `node2` was rehomed to the root: `anc σ_staled 2 = 0`. -/
theorem anc_sigmaStaled_2 : anc sigmaStaled 2 = 0 := by
  show anc (do_ baseAB (4, 0, app_op_t.Del [] 1)) 2 = 0
  rw [anc_doDel]
  have hanc : anc baseAB 2 = 1 := by
    rw [baseAB_eq]
    show (sel (upd (upd init_st 1 (10, 0)) 2 (20, 1)) 2).2 = 1
    rw [lemma_SelUpd1]
  rw [hanc]; simp

/-! ## §3  `insC` is staled; `insD`/`delD` are `accurate` at `σ_staled` -/

/-- `insC`'s anchor `node1` is gone, so it is NOT `accurate` at `σ_staled`
(reuse the gate). -/
theorem not_accurate_insC_sigmaStaled : ¬ accurate insC sigmaStaled :=
  accurate_insC_after_delA

/-- `insD` (Ins anchored at the rehomed `node2`) IS `accurate` at `σ_staled`. -/
theorem accurate_insD_sigmaStaled : accurate insD sigmaStaled := by
  show accurate (5, 2, app_op_t.Ins 40 [] 2) sigmaStaled
  refine Or.inr ⟨contains_sigmaStaled_2, ?_⟩
  show anc sigmaStaled 2 = 0
  exact anc_sigmaStaled_2

/-- `delD` (Del of the rehomed `node2`) IS `accurate` at `σ_staled`. -/
theorem accurate_delD_sigmaStaled : accurate delD sigmaStaled := by
  show accurate (5, 2, app_op_t.Del [] 2) sigmaStaled
  refine Or.inr ⟨contains_sigmaStaled_2, ?_⟩
  show anc sigmaStaled 2 = 0
  exact anc_sigmaStaled_2

/-! ## §4  `do_`-reductions used by the swaps

`insC` carries path `[]`, so on any state where its anchor `node1` is dead it
reduces to the **constant** update `3 ↦ (30,0)` (`reduce_insC`).  `insD` anchors
at the live `node2` and reduces to `5 ↦ (40,2)` (`reduce_insD`).  These mirror
`RGA_Rehoming_Gate.baseAB_eq`'s `resolve` algebra. -/

/-- Staled `insC` collapses to a constant insert at the root — on ANY state where
`node1` is absent (which no fresh event can undo). -/
theorem reduce_insC (s : concrete_st) (h1 : contains s 1 = false) :
    do_ s insC = upd s 3 (30, 0) := by
  show do_ s (3, 1, app_op_t.Ins 30 [] 1) = upd s 3 (30, 0)
  simp only [do_]
  rw [resolve_dead_head s 1 [] h1]
  simp only [resolve]

/-- `insD` anchors at the live `node2`. -/
theorem reduce_insD (s : concrete_st) (h2 : contains s 2 = true) :
    do_ s insD = upd s 5 (40, 2) := by
  show do_ s (5, 2, app_op_t.Ins 40 [] 2) = upd s 5 (40, 2)
  simp only [do_]
  rw [resolve_live_head s 2 [] h2]

/-- `delD` containment (delete of `node2`, path `[]`). -/
theorem contains_doDelD (s : concrete_st) (k : ℕ) :
    contains (do_ s delD) k = (contains s k && k != 2) := by
  show contains (do_ s (5, 2, app_op_t.Del [] 2)) k = (contains s k && k != 2)
  rw [contains_doDel]

/-- `delD` selection: reparent the (nonexistent) children of `node2` to the root
`resolve s [] = 0`, then remove `node2`. -/
theorem sel_doDelD (s : concrete_st) (k : ℕ) :
    sel (do_ s delD) k = (if anc s k = 2 then (el s k, 0) else sel s k) := by
  show sel (do_ s (5, 2, app_op_t.Del [] 2)) k = _
  rw [sel_doDel]; simp only [resolve]

/-! ## §5  THE TEST — the staled swap HOLDS

`a = insC` is INACCURATE at `σ_staled` (`not_accurate_insC_sigmaStaled`); `b`
(`insD` or `delD`) is `accurate`.  We evaluate the swap on the real `do_`. -/

/-- **VERDICT (representative, Ins).**  The staled swap `insC` ⇄ `insD` HOLDS —
in fact as literal `Eq` (two independent `upd`s that `upd_comm`), a fortiori as
`eq`.  `insC` is not `accurate` at `σ_staled`, so `commutes_with'` cannot be
invoked; yet the equation holds anyway, because the staled `insC` is the constant
`3 ↦ (30,0)` and `insD` (accurate) touches only `node2`/id `5`. -/
theorem staled_swap_holds :
    eq (do_ (do_ sigmaStaled insC) insD) (do_ (do_ sigmaStaled insD) insC) := by
  have hc2' : contains (upd sigmaStaled 3 (30, 0)) 2 = true := by
    rw [lemma_InDomUpd2 sigmaStaled 2 3 (30, 0) (by decide), contains_sigmaStaled_2]
  have hc1' : contains (upd sigmaStaled 5 (40, 2)) 1 = false := by
    rw [lemma_InDomUpd2 sigmaStaled 1 5 (40, 2) (by decide), contains_sigmaStaled_1]
  have hL : do_ (do_ sigmaStaled insC) insD
          = upd (upd sigmaStaled 3 (30, 0)) 5 (40, 2) := by
    rw [reduce_insC sigmaStaled contains_sigmaStaled_1,
        reduce_insD (upd sigmaStaled 3 (30, 0)) hc2']
  have hR : do_ (do_ sigmaStaled insD) insC
          = upd (upd sigmaStaled 5 (40, 2)) 3 (30, 0) := by
    rw [reduce_insD sigmaStaled contains_sigmaStaled_2,
        reduce_insC (upd sigmaStaled 5 (40, 2)) hc1']
  have hEq : do_ (do_ sigmaStaled insC) insD = do_ (do_ sigmaStaled insD) insC := by
    rw [hL, hR]; exact upd_comm sigmaStaled 3 5 (30, 0) (40, 2) (by decide)
  rw [hEq]; intro k; exact ⟨rfl, fun _ => rfl⟩

/-- **VERDICT (second witness, Del).**  The staled swap `insC` ⇄ `delD` HOLDS
(observational `eq`).  The delete of `node2` reparents nothing (`insC`'s node `3`
is anchored at the root, not at `node2`) and its own reparent target is the root
`resolve σ [] = 0`, so the two orders agree pointwise. -/
theorem staled_swap_holds_del :
    eq (do_ (do_ sigmaStaled insC) delD) (do_ (do_ sigmaStaled delD) insC) := by
  have hc1_DS : contains (do_ sigmaStaled delD) 1 = false := by
    rw [contains_doDelD, contains_sigmaStaled_1]; simp
  rw [reduce_insC sigmaStaled contains_sigmaStaled_1,
      reduce_insC (do_ sigmaStaled delD) hc1_DS]
  intro k
  refine ⟨?_, ?_⟩
  · -- containment: (3=k ∨ σk) ∧ k≠2  =  3=k ∨ (σk ∧ k≠2)  (agree because 3=k → k≠2)
    rw [contains_doDelD, lemma_InDomUpd1, lemma_InDomUpd1, contains_doDelD]
    by_cases hk2 : k = 2
    · subst hk2; simp
    · have hb : (k != 2) = true := by simp [hk2]
      simp only [hb, Bool.and_true]
  · -- value
    intro _
    by_cases hk3 : k = 3
    · subst hk3
      rw [sel_doDelD]
      have hanc3 : anc (upd sigmaStaled 3 (30, 0)) 3 = 0 := by
        show (sel (upd sigmaStaled 3 (30, 0)) 3).2 = 0
        rw [lemma_SelUpd1]
      rw [if_neg (by rw [hanc3]; decide), lemma_SelUpd1, lemma_SelUpd1]
    · rw [sel_doDelD,
          lemma_SelUpd2 (do_ sigmaStaled delD) k 3 (30, 0)
            (by simp only [bne_iff_ne, ne_eq]; exact fun e => hk3 e.symm),
          sel_doDelD]
      have hselk : sel (upd sigmaStaled 3 (30, 0)) k = sel sigmaStaled k :=
        lemma_SelUpd2 sigmaStaled k 3 (30, 0)
          (by simp only [bne_iff_ne, ne_eq]; exact fun e => hk3 e.symm)
      simp only [anc, el, hselk]

/-! ## §6  Cross-check — global convergence HOLDS

The two full `loOnA`-respecting enumerations of `{insA,insB,delA,insC,insD}` that
share the prefix `[insA,insB,delA]` (folding to `σ_staled`) and then transpose
`insC`/`insD` converge.  Here the pointwise swap and global convergence coincide;
this rules out the catastrophic "global convergence fails" world. -/

theorem full_enum_with_b_converges :
    eq (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA, insC, insD])
       (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA, insD, insC]) := by
  have h1 : applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA, insC, insD]
          = do_ (do_ sigmaStaled insC) insD := rfl
  have h2 : applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA, insD, insC]
          = do_ (do_ sigmaStaled insD) insC := rfl
  rw [h1, h2]; exact staled_swap_holds

/-! ## §7  The boundary the gate's constraint excludes (honesty)

The staled swap holds because `b` is required `accurate`.  Drop that and the swap
CAN fail: at `init_st`, `delOpE` (delete of the absent node `1`) is NOT
`accurate`, and its swap with `insOpE` genuinely diverges — even as literal `≠`
(`G2Probe.folds_differ`).  This is why `staled_swap_holds` is EVIDENCE for the
constrained pair, not a universal unconditioned-swap theorem. -/
theorem staled_swap_would_fail_if_b_inaccurate :
    do_ (do_ init_st insOpE) delOpE ≠ do_ (do_ init_st delOpE) insOpE :=
  folds_differ

/-! ## §8  The bundled verdict -/

/-- **THE VERDICT — ∀-STATE (leaning).**  At `σ_staled`, `insC` is NOT `accurate`
(`.1`) while `insD` IS (`.2`), so `commutes_with'` is inapplicable; nonetheless
the staled swap `insC` ⇄ `insD` HOLDS (`.2.2.1`), and so does `insC` ⇄ `delD`
(`.2.2.2`).  Every staled swap constructible under the gate's constraint ("`b`
`accurate`, concurrent with `insC`") holds on the real `do_`.  This selects
**Route A (easy)**: the RGA supports the stronger swap VC (staled event need not
be `accurate`, only the swapped-in `b` must be), so the applicability side
condition on the staled event drops from `applySeq_swap_loOnA_incomparable_C`.
Evidence, not proof (see `staled_swap_would_fail_if_b_inaccurate` for the
excluded failure mode). -/
theorem verdict_staled_swap_holds :
    (¬ accurate insC sigmaStaled)
    ∧ accurate insD sigmaStaled
    ∧ eq (do_ (do_ sigmaStaled insC) insD) (do_ (do_ sigmaStaled insD) insC)
    ∧ eq (do_ (do_ sigmaStaled insC) delD) (do_ (do_ sigmaStaled delD) insC) :=
  ⟨not_accurate_insC_sigmaStaled, accurate_insD_sigmaStaled,
   staled_swap_holds, staled_swap_holds_del⟩

/-! ## §9  Axiom audit — kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms staled_swap_holds
#print axioms staled_swap_holds_del
#print axioms full_enum_with_b_converges
#print axioms staled_swap_would_fail_if_b_inaccurate
#print axioms verdict_staled_swap_holds

end Sal.ConditionedMRDTs.RGASwapAtStaled
