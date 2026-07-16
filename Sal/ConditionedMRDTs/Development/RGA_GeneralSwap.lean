import Sal.MRDTs.RGA_Rehoming.RGA_Tombstone_Free_MRDT
import Sal.MRDTs.RGA_Rehoming.RGA_Reachability_Invariant

/-!
# Task #13 · Milestone 1b — the GENERAL update-side swap VC (or its located obstruction)

Bubble re-architecture, SCOPE / Route A (`CONDITIONED_METATHEORY_PLAN.md`,
"Bubble re-architecture — SCOPE", "MILESTONE 1 VERDICT").

The two prior gates (`RGA_SwapAtStaled_Gate.lean`,
`RGA_SwapAtStaled_NonEmptyPath_Gate.lean`, both VERIFIED) proved the staled swap
for concrete SINGLE-delete states.  This file attacks the GENERAL VC

  `id_mono s → wf s → accurate b s → eq (do_ (do_ s a) b) (do_ (do_ s b) a)`

for ALL ops `a` (including re-anchoring inserts staled at `s`) and ALL reachable
`s` — including `s` staled by MULTIPLE accumulated deletes.

## HEADLINE FINDING (kernel-checked)

**The general VC as literally stated above is FALSE** (`naive_general_swap_false`):
`id_mono s ∧ wf s ∧ accurate b s` is NOT sufficient, and the deficiency is NOT
what more state-invariant would supply.  The counterexample runs at
`s = init_st` (trivially `id_mono`, `wf`, `contains 0 = false`), with `b` a
perfectly `accurate` **and fresh** insert, and `a` a **fresh** insert whose
recorded path references `b`'s freshly created id.  So even
`id_mono ∧ wf ∧ accurate b ∧ fresh_ts a ∧ fresh_ts b ∧ distinct-ids` is
insufficient.

**The missing ingredient is a relation between `a` and `s`, not a state
invariant.**  `id_mono s` is a property of `s` alone; it cannot constrain the
*recorded path* `a` carries.  What the swap actually needs is that `a`'s recorded
path is *faithful* at `s` — that staleness came only from deletes rehoming along
`a`'s own chain, never from `a` naming a node that `b` (or anyone) later created.
This is captured here as two op↔state predicates, both **strictly weaker than
`accurate`** (both implied by it): `ClimbFaithful` (an `Ins`'s list, filtered at
its climb-target, resolves to that target's true parent) and `DelTargetFaithful`
(a `Del`'s recorded rehome target is its target's true parent).  Neither is
implied by `id_mono` (the counterexample is `id_mono` yet not `ClimbFaithful`).

## WHAT CLOSES (kernel-checked, `sorry`-free)

Replacing `accurate a` with the weaker `Faithful a` (plus `b accurate`, `wf`,
`contains 0 = false`, freshness, and `NoFreshClash`), the swap closes for ALL FOUR
op-kind combinations, for ARBITRARY reachable `s` (any number of accumulated
deletes) — bundled as `general_swap`:

* `swap_InsIns` — `a = Ins` (staled, any climb), `b = Ins` accurate/fresh.  Needs
  only `b`'s fresh id ∉ `a`'s list; NO faithfulness, NO `id_mono`.  The staled
  insert's climb-target is invariant under adding a fresh non-clashing node.
* `swap_InsDel` — `a = Ins` (staled, RE-ANCHORING via a non-empty path), `b = Del`
  accurate.  Needs `ClimbFaithful`.  This is the multi-delete generalisation of
  `RGA_SwapAtStaled_NonEmptyPath_Gate.swap_delN2_holds`: the eager child-rehoming
  of `b`'s delete lands `a`'s node exactly where the other order climbs it.
* `swap_DelIns` — `a = Del` (staled), `b = Ins` accurate/fresh.  Needs
  `DelTargetFaithful` and `b`'s fresh id ∉ `a`'s path.
* `swap_DelDel` — `a = Del` staled, `b = Del` accurate.  Needs a **one-sided
  `collapse`**: where `deldel_comm` uses the RGA's `collapse`
  (`RGA_Tombstone_Free_MRDT.lean:794`, needing BOTH targets `accurate`), here only
  `b` is accurate.  It closes from `ClimbFaithful s pa`, `DelTargetFaithful`, and
  `id_mono s` — the last used ONLY to rule out the 2-cycle `xa ↔ xb`.  `b`'s own
  `ClimbFaithful` is recovered from its accurate chain (`climbFaithful_of_isAncPath`).

The both-`accurate` reduction (`swap_bothAccurate`) dispatches to the RGA's proved
`insins_comm`/`insdel_comm`/`deldel_comm` and is the special case `a` accurate
(`faithful_of_accurate`: `accurate a s → Faithful a s`, so `general_swap` subsumes it).

## The LEVER — verdict on the plan's conjecture

The plan conjectured the update-side swap and the merge-side `wf`-preservation
"are plausibly the SAME structural fact" unified by `id_mono`.  **They are not the
same fact.**  The merge side's lever is genuinely `id_mono` used as a *fuel bound*:
it makes `climb`'s finite fuel (= the node id) sufficient by strict descent
(`RGA_Reachability_Invariant.climb_aux_walk`).  The update side's lever is *path
faithfulness* (an op↔state data relation, `Faithful`); `resolve` walks a finite
recorded LIST, so it terminates for free — there is no fuel to bound.  `id_mono`
IS used on the update side, but only in `swap_DelDel` and only for *acyclicity*
(ruling out `xa ↔ xb`), never for termination.  So the two obstructions are cousins
(both about ancestor chains surviving deletes) that both mention `id_mono`, but for
DIFFERENT reasons (fuel vs. acyclicity), and the update side crucially needs a
non-`id_mono` ingredient (`Faithful`) that the merge side does not.

## Axiom status
Every kept headline decl is kernel-clean (`propext, Classical.choice, Quot.sound`
only — no `sorryAx`, no `native_decide`/`ofReduceBool`).  The `Merge_Linearization`
sorries are not transitively touched.
-/

set_option maxHeartbeats 4000000

namespace Sal.ConditionedMRDTs.RGAGeneralSwap

/-! ## §1  `resolve`-monotonicity under a delete (task step 1)

Deleting a node moves `resolve` only UP the recorded list: either it is unchanged
(the delete target was not the climb-target) or it advances to the next live
candidate (the target was the climb-target).  The core equation
`resolve_doDel` — `resolve (do_ s (Del pre x)) L = resolve s (L.filter (≠x))` —
is proved *unconditionally* in the base MRDT; we package the "moves up or stays"
consequence and the faithfulness bridge here. -/

/-- **`resolve`-monotonicity under delete.**  After deleting `x`, resolving `L`
either equals the pre-delete resolve (when `x` was not what `L` resolved to) or
equals the post-filter resolve (when it was).  Immediate from `resolve_doDel` +
`resolve_filter_ne`; it says a delete never moves `resolve` to an *unrelated*
node, only forward along `L`. -/
theorem resolve_mono_under_delete (s : concrete_st) (t r x : ℕ) (pre L : List ℕ) :
    (resolve s L ≠ x ∧ resolve (do_ s (t, r, .Del pre x)) L = resolve s L)
    ∨ (resolve s L = x ∧
        resolve (do_ s (t, r, .Del pre x)) L = resolve s (L.filter (fun c => c != x))) := by
  rw [resolve_doDel]
  by_cases h : resolve s L = x
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl ⟨h, resolve_filter_ne s x L h⟩

/-! ## §2  Faithfulness predicates (strictly weaker than `accurate`)

The exact op↔state relations the swaps consume.  Both are implied by `accurate`
and both are what "staleness came only from deletes" supplies for a genuine
event — but neither is implied by `id_mono` alone (see `naive_general_swap_false`). -/

/-- **`ClimbFaithful s L`**: if `L`'s climb-target is live, then removing it from
`L` and re-resolving lands on that target's *true* parent.  For an accurate list
this is `isancpath_resolve_self_filter`; for a delete-staled list it is the fact
that deletes rehome children rootward along the very chain `L` records. -/
def ClimbFaithful (s : concrete_st) (L : List ℕ) : Prop :=
  contains s (resolve s L) = true →
    resolve s (L.filter (fun c => c != resolve s L)) = anc s (resolve s L)

/-- **`DelTargetFaithful s pa xa`**: a `Del`'s recorded rehome target
`resolve s pa` is its live target's true parent `anc s xa`. -/
def DelTargetFaithful (s : concrete_st) (pa : List ℕ) (xa : ℕ) : Prop :=
  contains s xa = true → resolve s pa = anc s xa

/-- `accurate` (an `Ins`) implies `ClimbFaithful` of its resolve-list. -/
theorem climbFaithful_of_accurate_ins (s : concrete_st) (e ka : ℕ) (pa : List ℕ)
    (h0 : contains s 0 = false) (t r : ℕ)
    (hacc : accurate (t, r, .Ins e pa ka) s) : ClimbFaithful s (ka :: pa) := by
  simp only [accurate, opLeaf, opPath] at hacc
  intro hlive
  rcases hacc with ⟨hk0, hpnil⟩ | ⟨hklive, hpath⟩
  · -- ka = 0, pa = [] : climb-target is 0, not live — premise false
    subst hk0; subst hpnil
    have : resolve s ([0] : List ℕ) = 0 := by simp only [resolve]; split <;> rfl
    rw [this] at hlive; rw [h0] at hlive; exact absurd hlive (by simp)
  · -- ka live : climb-target is ka, and (ka::pa).filter (≠ka) = pa.filter (≠ka)
    have hres : resolve s (ka :: pa) = ka := resolve_live_head s ka pa hklive
    rw [hres]
    have hfilter : (ka :: pa).filter (fun c => c != ka) = pa.filter (fun c => c != ka) := by
      rw [List.filter_cons]; simp
    rw [hfilter]
    exact isancpath_resolve_self_filter s ka pa hpath

/-- `accurate` (a `Del`) implies `DelTargetFaithful` (under `contains s 0 = false`,
which makes the degenerate `xa = 0` branch vacuous). -/
theorem delTargetFaithful_of_accurate_del (s : concrete_st) (xa : ℕ) (pa : List ℕ)
    (t r : ℕ) (h0 : contains s 0 = false)
    (hacc : accurate (t, r, .Del pa xa) s) : DelTargetFaithful s pa xa := by
  simp only [accurate, opLeaf, opPath] at hacc
  intro hlive
  rcases hacc with ⟨hx0, _⟩ | ⟨_, hpath⟩
  · subst hx0; rw [h0] at hlive; exact absurd hlive (by simp)
  · exact isAncPath_resolve s xa pa hpath

/-! ## §3  THE COUNTEREXAMPLE — the naive general VC is FALSE under `id_mono`

At `s = init_st` (trivially `id_mono`, `wf`, `contains 0 = false`):

* `sB = (7,2, Ins 50 [] 0)` — a **perfectly `accurate` and fresh** insert, creating
  node `7` as a child of the root;
* `sA = (5,1, Ins 40 [7] 3)` — a **fresh** insert whose recorded path `[7]`
  references `sB`'s freshly created id `7`.

The two orders DIVERGE: in `[sA,sB]` node `5` anchors at the root `0` (path `[7]`
is dead at `init`, climb falls to `0`); in `[sB,sA]` node `5` anchors at `7`
(now live).  This is a genuine `id_mono` state with `b` accurate — yet the swap
fails.  The deficiency is `sA`'s path naming a not-yet-created node, which no
STATE invariant on `s` can exclude: it is an op↔state faithfulness failure. -/

/-- The staled `a`: a fresh insert whose recorded path names `b`'s fresh id `7`. -/
def sA : op_t := (5, 1, .Ins 40 [7] 3)
/-- The accurate, fresh `b`: creates node `7` at the root. -/
def sB : op_t := (7, 2, .Ins 50 [] 0)

/-- `contains init_st k = false` for every key (`init_st` is empty). -/
theorem contains_init (k : ℕ) : contains init_st k = false := by
  simp [init_st, contains, mem]

/-- `sB` is `accurate` at `init_st` (root-anchored insert, left disjunct). -/
theorem accurate_sB_init : accurate sB init_st := by
  show accurate (7, 2, app_op_t.Ins 50 [] 0) init_st
  exact Or.inl ⟨rfl, rfl⟩

theorem fresh_sA_init : fresh_ts sA init_st := ⟨by decide, contains_init 5⟩
theorem fresh_sB_init : fresh_ts sB init_st := ⟨by decide, contains_init 7⟩

/-- The LHS anchors node `5` at the root `0`. -/
theorem sel_lhs_5 : sel (do_ (do_ init_st sA) sB) 5 = (40, 0) := by
  have hdoA : do_ init_st sA = upd init_st 5 (40, 0) := by
    show do_ init_st (5, 1, app_op_t.Ins 40 [7] 3) = upd init_st 5 (40, 0)
    simp only [do_]
    rw [resolve_dead_head init_st 3 [7] (contains_init 3),
        resolve_dead_head init_st 7 [] (contains_init 7)]
    rfl
  have hc0 : contains (upd init_st 5 (40, 0)) 0 = false := by
    rw [lemma_InDomUpd2 init_st 0 5 (40, 0) (by decide)]; exact contains_init 0
  rw [hdoA]
  show sel (do_ (upd init_st 5 (40, 0)) (7, 2, app_op_t.Ins 50 [] 0)) 5 = (40, 0)
  simp only [do_]
  rw [resolve_dead_head (upd init_st 5 (40, 0)) 0 [] hc0]
  show sel (upd (upd init_st 5 (40, 0)) 7 (50, resolve _ [])) 5 = (40, 0)
  rw [lemma_SelUpd2 (upd init_st 5 (40, 0)) 5 7 (50, resolve (upd init_st 5 (40, 0)) []) (by decide),
      lemma_SelUpd1]

/-- The RHS anchors node `5` at `7` (`sB`'s freshly created node). -/
theorem sel_rhs_5 : sel (do_ (do_ init_st sB) sA) 5 = (40, 7) := by
  have hdoB : do_ init_st sB = upd init_st 7 (50, 0) := by
    show do_ init_st (7, 2, app_op_t.Ins 50 [] 0) = upd init_st 7 (50, 0)
    simp only [do_]
    rw [resolve_dead_head init_st 0 [] (contains_init 0)]
    rfl
  have hc3 : contains (upd init_st 7 (50, 0)) 3 = false := by
    rw [lemma_InDomUpd2 init_st 3 7 (50, 0) (by decide)]; exact contains_init 3
  have hc7 : contains (upd init_st 7 (50, 0)) 7 = true := by
    rw [lemma_InDomUpd1]; simp
  show sel (do_ (do_ init_st sB) (5, 1, app_op_t.Ins 40 [7] 3)) 5 = (40, 7)
  rw [hdoB]
  simp only [do_]
  rw [resolve_dead_head (upd init_st 7 (50, 0)) 3 [7] hc3,
      resolve_live_head (upd init_st 7 (50, 0)) 7 [] hc7,
      lemma_SelUpd1]

theorem contains_lhs_5 : contains (do_ (do_ init_st sA) sB) 5 = true := by
  have hdoA : do_ init_st sA = upd init_st 5 (40, 0) := by
    show do_ init_st (5, 1, app_op_t.Ins 40 [7] 3) = upd init_st 5 (40, 0)
    simp only [do_]
    rw [resolve_dead_head init_st 3 [7] (contains_init 3),
        resolve_dead_head init_st 7 [] (contains_init 7)]; rfl
  show contains (do_ (do_ init_st sA) sB) 5 = true
  rw [hdoA]
  show contains (do_ (upd init_st 5 (40, 0)) (7, 2, app_op_t.Ins 50 [] 0)) 5 = true
  simp only [do_]
  rw [lemma_InDomUpd1, lemma_InDomUpd1]; simp

/-- **THE COUNTEREXAMPLE.**  The naive general swap VC — `id_mono s ∧ wf s ∧
`contains s 0 = false` ∧ `accurate b s` (even plus `fresh_ts a`, `fresh_ts b`,
and distinct ids) ⟹ swap — is FALSE.  Witnessed at `init_st` with `sA`/`sB`.
The obstruction is `sA`'s recorded path naming `sB`'s fresh id, an op↔state
faithfulness failure that `id_mono` (a property of `s` alone) cannot preclude. -/
theorem naive_general_swap_false :
    ¬ (∀ (s : concrete_st) (a b : op_t),
        id_mono s → wf s → contains s 0 = false → accurate b s →
        fresh_ts a s → fresh_ts b s → a.1 ≠ b.1 →
        eq (do_ (do_ s a) b) (do_ (do_ s b) a)) := by
  intro H
  have hswap := H init_st sA sB id_mono_init Inv_init.2 Inv_init.1
    accurate_sB_init fresh_sA_init fresh_sB_init (by decide)
  have hval := (hswap 5).2 contains_lhs_5
  rw [sel_lhs_5, sel_rhs_5] at hval
  exact absurd (congrArg Prod.snd hval) (by decide)

/-! ## §4  Both-accurate reduction (task step 2)

When `a` is ALSO `accurate` (and both fresh), the swap is exactly the RGA's proved
`insins_comm`/`insdel_comm`/`deldel_comm`, dispatched on the op kinds. -/

/-- **Step 2.**  If both `a` and `b` are `accurate` and fresh at `s`, the swap holds
by the RGA's proved commutations. -/
theorem swap_bothAccurate (s : concrete_st) (a b : op_t)
    (hdist : a.1 ≠ b.1) (h0 : contains s 0 = false)
    (ha : accurate a s) (hb : accurate b s)
    (hfa : fresh_ts a s) (hfb : fresh_ts b s) :
    eq (do_ (do_ s a) b) (do_ (do_ s b) a) := by
  obtain ⟨t1, r1, op1⟩ := a
  obtain ⟨t2, r2, op2⟩ := b
  simp only at hdist
  cases op1 with
  | Ins e1 p1 a1 =>
    cases op2 with
    | Ins e2 p2 a2 => exact insins_comm s t1 r1 e1 a1 t2 r2 e2 a2 p1 p2 hdist h0 ha hb hfa hfb
    | Del p2 x2    => exact insdel_comm s t1 r1 e1 a1 p1 t2 r2 p2 x2 hdist h0 ha hb hfa hfb
  | Del p1 x1 =>
    cases op2 with
    | Ins e2 p2 a2 =>
        exact eq_symm _ _ (insdel_comm s t2 r2 e2 a2 p2 t1 r1 p1 x1
          (Ne.symm hdist) h0 hb ha hfb hfa)
    | Del p2 x2    => exact deldel_comm s t1 r1 p1 x1 t2 r2 p2 x2 h0 ha hb

/-! ## §5  Ins/Ins — the staled-insert swap, NO faithfulness needed

`a = Ins` (staled, arbitrary climb-target) vs `b = Ins` accurate/fresh.  The ONLY
hypothesis beyond `b accurate` is that `b`'s fresh id does not occur in `a`'s
resolve-list (`hclash`).  `a`'s staled climb-target `va = resolve s (a1::p1)` is
literally unchanged by adding `b`'s fresh non-clashing node (`resolve_upd_notMem`),
so the two orders are the SAME state after `upd_comm`. -/
theorem swap_InsIns (s : concrete_st) (t1 r1 e1 a1 : ℕ) (p1 : List ℕ)
    (t2 r2 e2 a2 : ℕ) (p2 : List ℕ)
    (hdist : t1 ≠ t2) (h0 : contains s 0 = false)
    (hb : accurate (t2, r2, .Ins e2 p2 a2) s)
    (hfa : fresh_ts (t1, r1, .Ins e1 p1 a1) s)
    (hclash : t2 ∉ (a1 :: p1)) :
    eq (do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Ins e2 p2 a2))
       (do_ (do_ s (t2, r2, .Ins e2 p2 a2)) (t1, r1, .Ins e1 p1 a1)) := by
  simp only [fresh_ts] at hfa
  obtain ⟨ht1, _⟩ := hfa
  simp only [accurate, opLeaf, opPath] at hb
  set va := resolve s (a1 :: p1) with hva
  -- b's climb-target resolves to a2 (b accurate)
  have r2eq : resolve s (a2 :: p2) = a2 := by
    apply resolve_cons_eq
    rcases hb with ⟨h, hp⟩ | h
    · exact Or.inl ⟨h, hp, h0⟩
    · exact Or.inr h.1
  -- reduce both effects
  have hL : do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Ins e2 p2 a2)
          = upd (upd s t1 (e1, va)) t2 (e2, a2) := by
    simp only [do_]
    rw [← hva]
    have hc0_1 : contains (upd s t1 (e1, va)) 0 = false := by
      simp only [contains, upd, mem, union, _root_.singleton]
      have : (0 = t1) = False := by simp [Ne.symm ht1]
      grind
    have r2eq' : resolve (upd s t1 (e1, va)) (a2 :: p2) = a2 := by
      apply resolve_cons_eq
      rcases hb with ⟨h, hp⟩ | h
      · exact Or.inl ⟨h, hp, hc0_1⟩
      · refine Or.inr ?_
        rw [lemma_InDomUpd1, h.1]; simp
    rw [r2eq']
  have hR : do_ (do_ s (t2, r2, .Ins e2 p2 a2)) (t1, r1, .Ins e1 p1 a1)
          = upd (upd s t2 (e2, a2)) t1 (e1, va) := by
    simp only [do_]
    rw [r2eq]
    have r1eq' : resolve (upd s t2 (e2, a2)) (a1 :: p1) = va := by
      rw [hva]; exact resolve_upd_notMem s t2 (e2, a2) (a1 :: p1) hclash
    rw [r1eq']
  rw [hL, hR, upd_comm s t1 t2 (e1, va) (e2, a2) hdist]
  intro k; exact ⟨rfl, fun _ => rfl⟩

/-! ## §6  Ins/Del — the RE-ANCHORING staled insert swap, needs `ClimbFaithful`

`a = Ins` (staled, non-empty path, genuinely re-anchoring) vs `b = Del` accurate.
This is the ∀-state generalisation of
`RGA_SwapAtStaled_NonEmptyPath_Gate.swap_delN2_holds` (which was one concrete
state).  The `ClimbFaithful` hypothesis is exactly what the gate's single delete
supplied for free and what MULTIPLE accumulated deletes still supply for a genuine
event: `a`'s recorded path below its climb-target is that target's true chain, so
when `b` deletes the climb-target, `a`'s eager-rehomed node lands where the other
order re-climbs it. -/

/-- If a list resolves to `0` (no live candidate) then so does any filtering of it
(filtering can only drop candidates, never revive one).  Needs `contains s 0 =
false` to rule out a live root as spurious climb-target. -/
theorem resolve_zero_filter (s : concrete_st) (h0 : contains s 0 = false)
    (p : ℕ → Bool) : ∀ L, resolve s L = 0 → resolve s (L.filter p) = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro hres
    have hcf : contains s c = false := by
      cases hcc : contains s c with
      | false => rfl
      | true =>
        rw [resolve_live_head s c rest hcc] at hres
        rw [hres] at hcc; rw [h0] at hcc; exact absurd hcc (by simp)
    rw [resolve_dead_head s c rest hcf] at hres
    rw [List.filter_cons]
    by_cases hpc : p c = true
    · rw [if_pos hpc, resolve_dead_head s c (rest.filter p) hcf]; exact ih hres
    · rw [if_neg hpc]; exact ih hres

theorem swap_InsDel (s : concrete_st) (t1 r1 e1 a1 : ℕ) (p1 : List ℕ)
    (t2 r2 x2 : ℕ) (p2 : List ℕ)
    (h0 : contains s 0 = false)
    (hb : accurate (t2, r2, .Del p2 x2) s)
    (hfa : fresh_ts (t1, r1, .Ins e1 p1 a1) s)
    (hcf : ClimbFaithful s (a1 :: p1)) :
    eq (do_ (do_ s (t1, r1, .Ins e1 p1 a1)) (t2, r2, .Del p2 x2))
       (do_ (do_ s (t2, r2, .Del p2 x2)) (t1, r1, .Ins e1 p1 a1)) := by
  simp only [fresh_ts] at hfa
  obtain ⟨ht1_0, ht1_dom⟩ := hfa
  simp only [accurate, opLeaf, opPath] at hb
  unfold ClimbFaithful at hcf
  -- t1 ∉ p2 (p2 members are live, t1 is fresh)
  have ht1p2 : t1 ∉ p2 := by
    intro hmem
    have hc : contains s t1 = true := by
      rcases hb with ⟨_, hp⟩ | h
      · rw [hp] at hmem; simp at hmem
      · exact isAncPath_mem s x2 p2 h.2 t1 hmem
    rw [ht1_dom] at hc; exact absurd hc (by simp)
  -- t1 ≠ x2
  have ht1x2 : t1 ≠ x2 := by
    rcases hb with ⟨hx, _⟩ | h
    · rw [hx]; exact ht1_0
    · intro e; rw [e, h.1] at ht1_dom; exact absurd ht1_dom (by simp)
  -- a's effect is a path-free upd to the climb-target
  have hInsL : do_ s (t1, r1, .Ins e1 p1 a1) = upd s t1 (e1, resolve s (a1 :: p1)) := by
    simp only [do_]
  set US : concrete_st := upd s t1 (e1, resolve s (a1 :: p1)) with hUS
  set DS : concrete_st := do_ s (t2, r2, .Del p2 x2) with hDS
  have rUSp2 : resolve US p2 = resolve s p2 := by
    rw [hUS]; exact resolve_upd_notMem s t1 (e1, resolve s (a1 :: p1)) p2 ht1p2
  -- THE KEY equation: a's final anchor agrees on both orders
  have key : (if resolve s (a1 :: p1) = x2 then resolve s p2 else resolve s (a1 :: p1))
           = resolve s ((a1 :: p1).filter (fun c => c != x2)) := by
    by_cases hvx : resolve s (a1 :: p1) = x2
    · rw [if_pos hvx]
      by_cases hx2live : contains s x2 = true
      · -- x2 live: both sides equal anc s x2
        have hRp2 : resolve s p2 = anc s x2 := by
          rcases hb with ⟨hx0, _⟩ | h
          · rw [hx0] at hx2live; rw [h0] at hx2live; exact absurd hx2live (by simp)
          · exact isAncPath_resolve s x2 p2 h.2
        have hlive : contains s (resolve s (a1 :: p1)) = true := by rw [hvx]; exact hx2live
        have hcfr := hcf hlive
        rw [hvx] at hcfr
        rw [hRp2]; exact hcfr.symm
      · -- x2 not live → climb-target is 0, and x2 = 0, p2 = []
        simp only [Bool.not_eq_true] at hx2live
        have hres0 : resolve s (a1 :: p1) = 0 := by
          rcases resolve_zero_or_live s (a1 :: p1) with h | h
          · exact h
          · rw [hvx] at h; rw [hx2live] at h; exact absurd h (by simp)
        have hx2_0 : x2 = 0 := hvx.symm.trans hres0
        rcases hb with ⟨_, hpnil⟩ | ⟨hxl, _⟩
        · rw [hpnil, hx2_0]
          exact (resolve_zero_filter s h0 (fun c => c != 0) (a1 :: p1) hres0).symm
        · rw [hx2live] at hxl; exact absurd hxl (by simp)
    · rw [if_neg hvx]
      exact (resolve_filter_ne s x2 (a1 :: p1) hvx).symm
  have hRHS : do_ DS (t1, r1, .Ins e1 p1 a1)
            = upd DS t1 (e1, resolve s ((a1 :: p1).filter (fun c => c != x2))) := by
    have hresDS : resolve DS (a1 :: p1)
                = resolve s ((a1 :: p1).filter (fun c => c != x2)) := by
      rw [hDS]; exact resolve_doDel s t2 r2 x2 p2 (a1 :: p1)
    simp only [do_]; rw [hresDS]
  rw [hInsL, hRHS]
  intro k
  refine ⟨?_, ?_⟩
  · -- containment: (t1=k ∨ σk) ∧ k≠x2  =  t1=k ∨ (σk ∧ k≠x2)
    rw [contains_doDel US t2 r2 x2 p2 k,
        lemma_InDomUpd1 DS t1 k (e1, resolve s ((a1 :: p1).filter (fun c => c != x2))),
        hDS, contains_doDel s t2 r2 x2 p2 k, hUS, lemma_InDomUpd1]
    by_cases hk : k = t1
    · subst hk; simpa using ht1x2
    · have htk : ¬ (t1 = k) := fun e => hk e.symm
      simp [htk]
  · intro _
    rw [sel_doDel US t2 r2 x2 p2 k, rUSp2]
    by_cases hk : k = t1
    · subst hk
      have hanc : anc US k = resolve s (a1 :: p1) := by
        rw [hUS]; simp only [anc]; rw [lemma_SelUpd1]
      have hel : el US k = e1 := by
        rw [hUS]; simp only [el]; rw [lemma_SelUpd1]
      have hsel : sel US k = (e1, resolve s (a1 :: p1)) := by rw [hUS, lemma_SelUpd1]
      rw [hanc, hel, hsel, lemma_SelUpd1]
      by_cases hvx : resolve s (a1 :: p1) = x2
      · rw [if_pos hvx]
        have := key; rw [if_pos hvx] at this; rw [this]
      · rw [if_neg hvx]
        have := key; rw [if_neg hvx] at this; rw [this]
    · have hne : (t1 : ℕ) != k := by simp [Ne.symm hk]
      have hanck : anc US k = anc s k := by
        rw [hUS]; simp only [anc]
        rw [lemma_SelUpd2 s k t1 (e1, resolve s (a1 :: p1)) hne]
      have helk : el US k = el s k := by
        rw [hUS]; simp only [el]
        rw [lemma_SelUpd2 s k t1 (e1, resolve s (a1 :: p1)) hne]
      have hselk : sel US k = sel s k :=
        lemma_SelUpd2 s k t1 (e1, resolve s (a1 :: p1)) hne
      rw [hanck, helk, hselk,
          lemma_SelUpd2 DS k t1 (e1, resolve s ((a1 :: p1).filter (fun c => c != x2))) hne,
          hDS, sel_doDel s t2 r2 x2 p2 k]

/-! ## §7  Del/Ins — the staled-delete swap, needs `DelTargetFaithful`

`a = Del` (staled recorded rehome target) vs `b = Ins` accurate/fresh.  The
`DelTargetFaithful` hypothesis (`a`'s recorded rehome target is its live target's
true parent) is needed exactly when `b` anchors its new node at `a`'s delete
target: then `a` rehomes `b`'s node, and the two orders agree only if `a`'s target
is the true parent.  `hxa0` (a genuine `Del` never targets the root sentinel) and
the fresh/distinctness of `b`'s created id complete the hypotheses. -/
theorem swap_DelIns (s : concrete_st) (t1 r1 xa : ℕ) (pa : List ℕ)
    (t2 r2 e2 kb : ℕ) (pb : List ℕ)
    (h0 : contains s 0 = false)
    (hb : accurate (t2, r2, .Ins e2 pb kb) s)
    (hfb : fresh_ts (t2, r2, .Ins e2 pb kb) s)
    (hxa0 : xa ≠ 0)
    (hclash : t2 ∉ (xa :: pa))
    (hdtf : DelTargetFaithful s pa xa) :
    eq (do_ (do_ s (t1, r1, .Del pa xa)) (t2, r2, .Ins e2 pb kb))
       (do_ (do_ s (t2, r2, .Ins e2 pb kb)) (t1, r1, .Del pa xa)) := by
  simp only [fresh_ts] at hfb
  obtain ⟨ht2_0, ht2_dom⟩ := hfb
  simp only [accurate, opLeaf, opPath] at hb
  unfold DelTargetFaithful at hdtf
  have ht2xa : t2 ≠ xa := by intro e; apply hclash; rw [e]; simp
  have ht2pa : t2 ∉ pa := fun hm => hclash (List.mem_cons_of_mem xa hm)
  have rkb : resolve s (kb :: pb) = kb := by
    apply resolve_cons_eq
    rcases hb with ⟨h, hp⟩ | h
    · exact Or.inl ⟨h, hp, h0⟩
    · exact Or.inr h.1
  have hInsR : do_ s (t2, r2, .Ins e2 pb kb) = upd s t2 (e2, kb) := by
    simp only [do_]; rw [rkb]
  set DA : concrete_st := do_ s (t1, r1, .Del pa xa) with hDA
  set UB : concrete_st := upd s t2 (e2, kb) with hUB
  have rUBpa : resolve UB pa = resolve s pa := by
    rw [hUB]; exact resolve_upd_notMem s t2 (e2, kb) pa ht2pa
  -- a's target after applying b, resolved on the deleted state
  have keyb : resolve DA (kb :: pb) = (if kb = xa then anc s xa else kb) := by
    rw [hDA, resolve_doDel]
    by_cases hkx : kb = xa
    · rw [if_pos hkx, hkx]
      have hpath : IsAncPath s xa pb := by
        rcases hb with ⟨hkb0, _⟩ | h
        · rw [hkb0] at hkx; exact absurd hkx.symm hxa0
        · rw [← hkx]; exact h.2
      rw [List.filter_cons]
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      exact isancpath_resolve_self_filter s xa pb hpath
    · rw [if_neg hkx]
      have hne : resolve s (kb :: pb) ≠ xa := by rw [rkb]; exact hkx
      rw [resolve_filter_ne s xa (kb :: pb) hne, rkb]
  have hLHS : do_ DA (t2, r2, .Ins e2 pb kb)
            = upd DA t2 (e2, if kb = xa then anc s xa else kb) := by
    simp only [do_]; rw [keyb]
  rw [hInsR, hLHS]
  intro k
  refine ⟨?_, ?_⟩
  · -- containment
    rw [lemma_InDomUpd1 DA t2 k (e2, if kb = xa then anc s xa else kb),
        hDA, contains_doDel s t1 r1 xa pa k,
        contains_doDel UB t1 r1 xa pa k, hUB, lemma_InDomUpd1]
    by_cases hk : k = t2
    · subst hk; simpa using ht2xa
    · have htk : ¬ (t2 = k) := fun e => hk e.symm
      simp [htk]
  · intro _
    rw [sel_doDel UB t1 r1 xa pa k, rUBpa]
    by_cases hk : k = t2
    · subst hk
      rw [lemma_SelUpd1]
      have hancUB : anc UB k = kb := by rw [hUB]; simp only [anc]; rw [lemma_SelUpd1]
      have helUB : el UB k = e2 := by rw [hUB]; simp only [el]; rw [lemma_SelUpd1]
      have hselUB : sel UB k = (e2, kb) := by rw [hUB, lemma_SelUpd1]
      rw [hancUB, helUB, hselUB]
      by_cases hkx : kb = xa
      · have hxlive : contains s xa = true := by
          rcases hb with ⟨hkb0, _⟩ | h
          · rw [hkb0] at hkx; exact absurd hkx.symm hxa0
          · rw [← hkx]; exact h.1
        rw [if_pos hkx, if_pos hkx, hdtf hxlive]
      · rw [if_neg hkx, if_neg hkx]
    · have hne : (t2 : ℕ) != k := by simp [Ne.symm hk]
      rw [lemma_SelUpd2 DA k t2 (e2, if kb = xa then anc s xa else kb) hne,
          hDA, sel_doDel s t1 r1 xa pa k]
      have hancUBk : anc UB k = anc s k := by
        rw [hUB]; simp only [anc]; rw [lemma_SelUpd2 s k t2 (e2, kb) hne]
      have helUBk : el UB k = el s k := by
        rw [hUB]; simp only [el]; rw [lemma_SelUpd2 s k t2 (e2, kb) hne]
      have hselUBk : sel UB k = sel s k := lemma_SelUpd2 s k t2 (e2, kb) hne
      rw [hancUBk, helUBk, hselUBk]

/-! ## §8  Del/Del — the staled-delete vs accurate-delete swap

`a = Del` (staled) vs `b = Del` accurate.  This is where the RGA's `collapse`
(`RGA_Tombstone_Free_MRDT.lean:794`, which needs BOTH targets `accurate`) would be
applied in `deldel_comm`; here only `b` is accurate.  It closes with a ONE-SIDED
collapse assembled from: `ClimbFaithful s pa` (`a`'s path faithful at its
climb-target), `DelTargetFaithful s pa xa` (`a`'s rehome target correct), and
`id_mono s` — the last used ONLY to rule out the 2-cycle `xa ↔ xb`.  `b`'s own
`ClimbFaithful` is derived from its `accurate` chain (`climbFaithful_of_isAncPath`). -/

/-- An accurate chain of `leaf` is `ClimbFaithful` (its climb-target is the chain's
head, whose true parent is recovered by filtering the head out). -/
theorem climbFaithful_of_isAncPath (s : concrete_st) (h0 : contains s 0 = false)
    (leaf : ℕ) (p : List ℕ) (hp : IsAncPath s leaf p) : ClimbFaithful s p := by
  intro hlive
  cases p with
  | nil =>
    simp only [resolve] at hlive; rw [h0] at hlive; exact absurd hlive (by simp)
  | cons c cs =>
    simp only [IsAncPath] at hp
    obtain ⟨_, hcc, hrest⟩ := hp
    have hres : resolve s (c :: cs) = c := resolve_live_head s c cs hcc
    rw [hres]
    have hfilter : (c :: cs).filter (fun x => x != c) = cs.filter (fun x => x != c) := by
      rw [List.filter_cons]; simp
    rw [hfilter]
    exact isancpath_resolve_self_filter s c cs hrest

theorem swap_DelDel (s : concrete_st) (t1 r1 xa : ℕ) (pa : List ℕ)
    (t2 r2 xb : ℕ) (pb : List ℕ)
    (h0 : contains s 0 = false) (hwf : wf s) (hmono : id_mono s)
    (hb : accurate (t2, r2, .Del pb xb) s)
    (hxa0 : xa ≠ 0) (hxb0 : xb ≠ 0)
    (hcf : ClimbFaithful s pa) (hdtf : DelTargetFaithful s pa xa) :
    eq (do_ (do_ s (t1, r1, .Del pa xa)) (t2, r2, .Del pb xb))
       (do_ (do_ s (t2, r2, .Del pb xb)) (t1, r1, .Del pa xa)) := by
  simp only [accurate, opLeaf, opPath] at hb
  unfold ClimbFaithful at hcf
  unfold DelTargetFaithful at hdtf
  have hxblive : contains s xb = true := by
    rcases hb with ⟨hx0, _⟩ | h
    · exact absurd hx0 hxb0
    · exact h.1
  have hbpath : IsAncPath s xb pb := by
    rcases hb with ⟨hx0, _⟩ | h
    · exact absurd hx0 hxb0
    · exact h.2
  have hResPb : resolve s pb = anc s xb := isAncPath_resolve s xb pb hbpath
  have hcfb := climbFaithful_of_isAncPath s h0 xb pb hbpath
  unfold ClimbFaithful at hcfb
  intro k
  refine ⟨?_, ?_⟩
  · simp only [contains_doDel]; rw [Bool.and_right_comm]
  · intro _
    have hel : el (do_ (do_ s (t1, r1, .Del pa xa)) (t2, r2, .Del pb xb)) k
             = el (do_ (do_ s (t2, r2, .Del pb xb)) (t1, r1, .Del pa xa)) k := by
      simp only [el_doDel]
    have han : anc (do_ (do_ s (t1, r1, .Del pa xa)) (t2, r2, .Del pb xb)) k
             = anc (do_ (do_ s (t2, r2, .Del pb xb)) (t1, r1, .Del pa xa)) k := by
      simp only [anc_doDel, resolve_doDel]
      by_cases h1 : anc s k = xa
      · by_cases h2 : anc s k = xb
        · -- (d)  xa = xb
          have hxab : xa = xb := h1.symm.trans h2
          have hxalive : contains s xa = true := by rw [hxab]; exact hxblive
          have hRa : resolve s pa = anc s xa := hdtf hxalive
          have hne1 : ¬ (anc s xa = xb) := by
            rw [← hxab]; rcases hmono xa hxalive with h | h
            · rw [h]; exact fun e => hxa0 e.symm
            · omega
          have hne2 : ¬ (anc s xb = xa) := by
            rw [hxab]; rcases hmono xb hxblive with h | h
            · rw [h]; exact fun e => hxb0 e.symm
            · omega
          simp only [if_pos h1, if_pos h2]
          rw [hRa, hResPb, if_neg hne1, if_neg hne2, hxab]
        · -- (b)  anc s k = xa, ≠ xb
          simp only [if_pos h1, if_neg h2]
          by_cases hA : resolve s pa = xb
          · rw [if_pos hA]
            have hancxb_ne : anc s xb ≠ xa := by
              intro he
              have hxal : contains s xa = true := by
                rcases hwf xb hxblive with h | h
                · rw [he] at h; exact absurd h hxa0
                · rw [he] at h; exact h
              have hRaval : resolve s pa = anc s xa := hdtf hxal
              rw [hA] at hRaval
              have h_axa := hmono xa hxal
              have h_axb := hmono xb hxblive
              rcases h_axa with e1 | e1
              · rw [← hRaval] at e1; exact hxb0 e1
              rcases h_axb with e2 | e2
              · rw [he] at e2; exact hxa0 e2
              rw [← hRaval] at e1; rw [he] at e2; omega
            have hRHS : resolve s (pa.filter (fun c => c != xb)) = anc s xb := by
              have hcfr := hcf (by rw [hA]; exact hxblive)
              rw [hA] at hcfr; exact hcfr
            have hLHS : resolve s (pb.filter (fun c => c != xa)) = anc s xb := by
              rw [resolve_filter_ne s xa pb (by rw [hResPb]; exact hancxb_ne)]; exact hResPb
            rw [hLHS, hRHS]
          · rw [if_neg hA]; exact (resolve_filter_ne s xb pa hA).symm
      · by_cases h2 : anc s k = xb
        · -- (c)  anc s k = xb, ≠ xa
          simp only [if_neg h1, if_pos h2]
          by_cases hB : resolve s pb = xa
          · rw [if_pos hB]
            have hxal : contains s xa = true := by
              rw [hResPb] at hB
              rcases hwf xb hxblive with h | h
              · rw [hB] at h; exact absurd h hxa0
              · rw [hB] at h; exact h
            have hLHS : resolve s (pb.filter (fun c => c != xa)) = anc s xa := by
              have hcfr := hcfb (by rw [hB]; exact hxal)
              rw [hB] at hcfr; exact hcfr
            have hancxa_ne : anc s xa ≠ xb := by
              intro he
              rw [hResPb] at hB
              have h_axa := hmono xa hxal
              have h_axb := hmono xb hxblive
              rcases h_axa with e1 | e1
              · rw [e1] at he; exact hxb0 he.symm
              rcases h_axb with e2 | e2
              · rw [hB] at e2; exact hxa0 e2
              rw [he] at e1; rw [hB] at e2; omega
            have hRHS : resolve s (pa.filter (fun c => c != xb)) = anc s xa := by
              rw [resolve_filter_ne s xb pa (by rw [hdtf hxal]; exact hancxa_ne)]; exact hdtf hxal
            rw [hLHS, hRHS]
          · rw [if_neg hB]; exact resolve_filter_ne s xa pb hB
        · -- (a)  neither
          simp only [if_neg h1, if_neg h2]
    exact Prod.ext_iff.mpr ⟨hel, han⟩

/-! ## §9  The bundled general swap VC — Route A's enabling lemma

All four op-kind cases assemble into ONE theorem, under a per-op faithfulness
predicate (`Faithful`, strictly weaker than `accurate`) and a no-fresh-clash
predicate (`NoFreshClash`, the causal-freshness condition a real execution
supplies).  This is the general update-side swap the bubble needs: the staled
event `a` need NOT be `accurate` — only `Faithful` — and only the swapped-in `b`
must be `accurate`. -/

/-- Per-op faithfulness (both parts strictly weaker than `accurate`).  For an `Ins`
it is `ClimbFaithful` of the resolve-list; for a `Del` it is `ClimbFaithful` of the
path, its rehome target being correct (`DelTargetFaithful`), and genuineness
(`x ≠ 0`, the root sentinel is never a real target). -/
def Faithful (o : op_t) (s : concrete_st) : Prop :=
  match o with
  | (_, _, .Ins _ pre a) => ClimbFaithful s (a :: pre)
  | (_, _, .Del pre x)   => ClimbFaithful s pre ∧ DelTargetFaithful s pre x ∧ x ≠ 0

/-- No-fresh-clash: `b`'s freshly created id (if `b` is an `Ins`) does not occur in
`a`'s recorded list, and if BOTH are `Del`s then `b`'s target is genuine.  A real
execution supplies this: a concurrent `b`'s new node is not in `a`'s causal past,
so `a`'s path cannot name it (`naive_general_swap_false` is exactly the violation). -/
def NoFreshClash (a b : op_t) : Prop :=
  match b with
  | (t2, _, .Ins _ _ _) =>
      match a with
      | (_, _, .Ins _ pre anch) => t2 ∉ (anch :: pre)
      | (_, _, .Del pre x)      => t2 ∉ (x :: pre)
  | (_, _, .Del _ xb) =>
      match a with
      | (_, _, .Ins _ _ _) => True
      | (_, _, .Del _ _)   => xb ≠ 0

/-- **THE GENERAL SWAP VC (Route A's enabling lemma).**  For a reachable `s`
(`contains 0 = false`, `wf`, `id_mono`), a staled-but-`Faithful` op `a`, and an
`accurate` op `b` with no fresh clash, the update-side swap holds — for ALL op
kinds, for `a` staled by ANY number of accumulated deletes.  Dispatches on op kinds
to §5–§8.  Drop `accurate a` (replace by the weaker `Faithful a`) and the applicability
side-condition on the staled event drops from `applySeq_swap_loOnA_incomparable_C`. -/
theorem general_swap (s : concrete_st) (a b : op_t)
    (hdist : a.1 ≠ b.1) (h0 : contains s 0 = false) (hwf : wf s) (hmono : id_mono s)
    (hb : accurate b s) (hfa : fresh_ts a s) (hfb : fresh_ts b s)
    (hfaith : Faithful a s) (hclash : NoFreshClash a b) :
    eq (do_ (do_ s a) b) (do_ (do_ s b) a) := by
  obtain ⟨t1, r1, op1⟩ := a
  obtain ⟨t2, r2, op2⟩ := b
  simp only at hdist
  cases op1 with
  | Ins e1 p1 a1 =>
    simp only [Faithful] at hfaith
    cases op2 with
    | Ins e2 p2 a2 =>
        simp only [NoFreshClash] at hclash
        exact swap_InsIns s t1 r1 e1 a1 p1 t2 r2 e2 a2 p2 hdist h0 hb hfa hclash
    | Del p2 x2 =>
        exact swap_InsDel s t1 r1 e1 a1 p1 t2 r2 x2 p2 h0 hb hfa hfaith
  | Del p1 x1 =>
    simp only [Faithful] at hfaith
    cases op2 with
    | Ins e2 p2 a2 =>
        simp only [NoFreshClash] at hclash
        exact swap_DelIns s t1 r1 x1 p1 t2 r2 e2 a2 p2 h0 hb hfb
          hfaith.2.2 hclash hfaith.2.1
    | Del p2 x2 =>
        simp only [NoFreshClash] at hclash
        exact swap_DelDel s t1 r1 x1 p1 t2 r2 x2 p2 h0 hwf hmono hb
          hfaith.2.2 hclash hfaith.1 hfaith.2.1

/-! ## §10  `accurate ⟹ Faithful` — the both-accurate case is subsumed

`swap_bothAccurate` (§4) is the special case `a` accurate; `general_swap` subsumes
it, since `accurate a s` implies `Faithful a s`. -/

theorem faithful_of_accurate (s : concrete_st) (a : op_t)
    (h0 : contains s 0 = false) (ha : accurate a s)
    (hx0 : ∀ pre x, a.2.2 = app_op_t.Del pre x → x ≠ 0) : Faithful a s := by
  obtain ⟨t, r, op⟩ := a
  cases op with
  | Ins e pre anch =>
      exact climbFaithful_of_accurate_ins s e anch pre h0 t r ha
  | Del pre x =>
      refine ⟨?_, ?_, hx0 pre x rfl⟩
      · -- ClimbFaithful of the Del's path, from its accurate chain
        rcases ha with ⟨hx, hp⟩ | ⟨_, hpath⟩
        · -- x = 0 excluded by hx0
          exact absurd hx (hx0 pre x rfl)
        · exact climbFaithful_of_isAncPath s h0 x pre hpath
      · exact delTargetFaithful_of_accurate_del s x pre t r h0 ha

/-! ## §11  Full-fold cross-check on a MULTI-delete state (the gates' residual)

A concrete witness that the swap holds on a state staled by TWO accumulated deletes
(the residual the single-delete gates left untested): the chain `root → 1 → 2 → 3`,
with BOTH `2` and `3` deleted, staling a pending insert `E` anchored at `3` (path
`[2,1]`) so its climb crosses TWO dead nodes to land at `1` (verified:
`anc (do_ chain3_2del insE_gs) 9 = 1`).  Checked by `native_decide` on the folds'
dumps — an analysis cross-check (uses `Lean.ofReduceBool`), NOT a headline; the
headline `general_swap` is native-free and covers this case abstractly. -/

/-- Deep chain `root → n1 → n2 → n3`, built by real `Ins`. -/
def chain3 : concrete_st :=
  do_ (do_ (do_ init_st (1, 0, .Ins 10 [] 0)) (2, 0, .Ins 20 [] 1)) (3, 0, .Ins 30 [1] 2)

/-- Delete `n2` (middle) then `n3` (anchor) — a genuine TWO-delete staling. -/
def chain3_2del : concrete_st := do_ (do_ chain3 (7, 0, .Del [1] 2)) (8, 0, .Del [2, 1] 3)

/-- The staled insert `E`, anchored at `n3`, carrying the true chain `[2,1]`. -/
def insE_gs : op_t := (9, 1, .Ins 40 [2, 1] 3)
/-- An accurate `b` at the doubly-deleted state: delete the sole survivor `n1`. -/
def bDel_gs : op_t := (10, 2, .Del [] 1)

/-- On a state staled by TWO accumulated deletes, `insE_gs` (inaccurate, its climb
crosses two dead nodes) still swaps with the accurate `bDel_gs`.  Kernel-clean via
`native_decide` on the two folds' dumps — an analysis cross-check, not a headline
(it uses `Lean.ofReduceBool`); the headline `general_swap` is native-free. -/
theorem multidelete_swap_crosscheck :
    dump (do_ (do_ chain3_2del insE_gs) bDel_gs) [1, 2, 3, 9]
      = dump (do_ (do_ chain3_2del bDel_gs) insE_gs) [1, 2, 3, 9] := by native_decide

/-! ## §12  Axiom audit — headlines kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms naive_general_swap_false
#print axioms swap_InsIns
#print axioms swap_InsDel
#print axioms swap_DelIns
#print axioms swap_DelDel
#print axioms swap_bothAccurate
#print axioms general_swap
#print axioms faithful_of_accurate
#print axioms resolve_mono_under_delete

end Sal.ConditionedMRDTs.RGAGeneralSwap
