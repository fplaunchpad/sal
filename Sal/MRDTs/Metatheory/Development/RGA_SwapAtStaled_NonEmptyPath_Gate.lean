import Sal.MRDTs.Metatheory.Development.RGA_Rehoming_Gate

/-!
# Task #12 · the REFINED staled-swap gate — a NON-EMPTY-path staled insert

The prior gate (`RGA_SwapAtStaled_Gate.lean`) tested only EMPTY-path staled ops
(`Ins _ [] _`), which collapse to the root the moment their anchor dies — the
degenerate case where the path-carrying mechanism is OFF.  This file runs the
DECISIVE case the fork turns on: a staled insert whose recorded NON-EMPTY path
must be climbed, re-anchoring it to a *different* node than it had at its base.

## The deep tree and the events (all built by real `Ins`/`Del` on the real `do_`)

Chain `root(0) → n1(1) → n2(2) → n3(3)`, built with genuine non-empty paths:

* `insA = (1,0, Ins 10 []  0)` — `n1` at the root                     (reused: `RGARehomingGate.insA`)
* `insB = (2,0, Ins 20 []  1)` — `n2` anchored at `n1`, path `[]`     (reused: `RGARehomingGate.insB`)
* `insC3 = (3,0, Ins 30 [1] 2)` — `n3` anchored at `n2`, path `[1]`   (n2's true ancestor chain)
* `base = do_ (do_ baseAB) insC3 = {1↦(10,0), 2↦(20,1), 3↦(30,2)}`

The pending staled insert carries a genuine **length-2** path:

* `insE = (5,1, Ins 40 [2,1] 3)` — anchored at the deepest node `n3`, path `[2,1]`
  (`n3`'s real ancestor chain `n2 :: n1`).  `accurate insE base` (`accurate_insE_base`).

The staling delete removes `insE`'s ANCHOR `n3` (this is what actually re-anchors an
`Ins` — see the finding below):

* `delN3 = (4,0, Del [2,1] 3)`,  `sigmaStaled = do_ base delN3 = {1↦(10,0), 2↦(20,1)}`.

At `sigmaStaled`, `insE` is INACCURATE (`not_accurate_insE_sigmaStaled`: its anchor
`n3` is gone) and its `do_` RE-ANCHORS by climbing the carried path `3 :: [2,1]`
past the dead `n3` to the live `n2` — a genuine climb-target MOVE from `n3` to
`n2` (`climb_target_moves`: `anc (do_ base insE) 5 = 3` but
`anc (do_ sigmaStaled insE) 5 = 2`).

## THE FINDING that shapes the construction (a `do_`-semantics fact)

For an `Ins`, deleting a **middle** ancestor does NOT move the climb: `resolve`
short-circuits at the anchor, which is the head of the resolve list, so as long as
the anchor survives the insert re-lands there.  `middle_delete_no_climb_move`
witnesses this on `sigmaMid = do_ base (Del [1] 2)` (delete the middle `n2`, which
rehomes `n3` up to `n1`): `insE` is INACCURATE there (`IsAncPath` breaks at the
`n3→n2` link) yet its climb-target is UNCHANGED (`anc (do_ sigmaMid insE) 5 = 3`).
Only deleting the anchor itself (`sigmaStaled`) re-anchors an `Ins`.  So the
decisive re-anchoring swap is tested at `sigmaStaled`, not at `sigmaMid`.

## THE TEST — maximal-stress swapped-in `b`, `accurate` at `sigmaStaled`

`b` is chosen to maximally stress the interaction: it targets `insE`'s climb-target
`n2` directly.

* `bDel = (6,2, Del [1] 2)` — DELETES `insE`'s climb-target `n2`.  `accurate` at
  `sigmaStaled` (`accurate_bDel_sigmaStaled`).  In order `[insE,bDel]` the insert
  lands node `5` at `n2`, then `bDel` rehomes it up to `n1`; in order `[bDel,insE]`
  the insert climbs `3(dead)→2(dead)→1` DIRECTLY through the now-doubly-deleted
  chain, landing node `5` at `n1`.  Two different climb routes, SAME result.
* `bIns = (6,2, Ins 50 [1] 2)` — inserts at `insE`'s climb-target `n2`.

## VERDICT — the NON-EMPTY-path staled swap HOLDS (with the swapped-in op accurate)

`swap_delN2_holds` (`eq`, decisive Del) and `swap_insN2_holds` (`eq`, Ins) both
converge on the real `do_`, even though `insE` is INACCURATE and genuinely
re-anchors state-dependently.  The mechanism is the RGA's eager child-reparenting:
whichever node the insert re-anchors to, a later `Del` of that node rehomes the
insert's node to exactly the ancestor the other order climbs to directly.  The
`accurate` requirement on `b` is load-bearing — it forces `b`'s reparent target to
be the true live ancestor, which is precisely the climb continuation.

This selects a **nuanced Route A**: the RGA supports a *stronger* swap VC on the
constrained pair — drop the "staled event `accurate`" premise, keep only "swapped-in
`b` `accurate`" — even for non-empty-path, genuinely-re-anchoring staled inserts.
Evidence (concrete deep witnesses), not a universal proof; the prior gate's
`staled_swap_would_fail_if_b_inaccurate` shows the `b`-`accurate` premise is
necessary.

## Global cross-check (the RGA is a real CRDT)

`full_enum_converges` exhibits two full linearizations of
`{insA,insB,insC3,delN3,insE,bDel}` sharing the prefix `[insA,insB,insC3,delN3]`
(folding to `sigmaStaled`) and transposing `insE`/`bDel` — they converge.  Pointwise
swap and global convergence COINCIDE here, ruling out the catastrophic
"global-diverges" world.

## Axiom status
Every headline decl is kernel-clean (`propext, Classical.choice, Quot.sound` only —
no `sorryAx`, no `native_decide`/`ofReduceBool`).  The `Merge_Linearization_Set`
sorries are not transitively touched.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGASwapNonEmpty

open Sal.Emulation
open Sal.Metatheory.RGARehomingGate (insA insB baseAB baseAB_eq
  contains_baseAB_1 contains_baseAB_0 contains_baseAB_3 anc_baseAB_1)
open Sal.Metatheory.RGASig (RGACondSig)

/-! ## §1  The deep tree, the staled insert, and the delete events -/

/-- Create `n3` (element 30) anchored at `n2`, carrying `n2`'s real chain `[1]`. -/
def insC3 : Op app_op_t := (3, 0, .Ins 30 [1] 2)
/-- The deep chain `root → n1 → n2 → n3`. -/
def base : concrete_st := do_ baseAB insC3

/-- The pending staled insert: anchored at `n3`, carrying its length-2 chain `[2,1]`. -/
def insE : Op app_op_t := (5, 1, .Ins 40 [2, 1] 3)

/-- Delete `insE`'s ANCHOR `n3` (a leaf).  This is what re-anchors `insE`. -/
def delN3 : Op app_op_t := (4, 0, .Del [2, 1] 3)
/-- The staled state: `n3` gone, `insE`'s anchor dead. -/
def sigmaStaled : concrete_st := do_ base delN3

/-- Delete the MIDDLE ancestor `n2` (rehomes `n3` up to `n1`). -/
def delN2mid : Op app_op_t := (4, 0, .Del [1] 2)
/-- The middle-deleted state (used only for the no-climb-move finding). -/
def sigmaMid : concrete_st := do_ base delN2mid

/-- Swapped-in `b`, choice 1 (maximal stress): DELETE `insE`'s climb-target `n2`. -/
def bDel : Op app_op_t := (6, 2, .Del [1] 2)
/-- Swapped-in `b`, choice 2: INSERT at `insE`'s climb-target `n2`. -/
def bIns : Op app_op_t := (6, 2, .Ins 50 [1] 2)

/-! ## §2  Base-state algebra (kernel-clean, via the RGA map lemmas) -/

theorem contains_baseAB_2 : contains baseAB 2 = true := by
  rw [baseAB_eq, lemma_InDomUpd1]; simp

theorem contains_baseAB_5 : contains baseAB 5 = false := by
  rw [baseAB_eq, lemma_InDomUpd1, lemma_InDomUpd1]; simp [init_st]

theorem anc_baseAB_2 : anc baseAB 2 = 1 := by
  rw [baseAB_eq]
  show (sel (upd (upd init_st 1 (10, 0)) 2 (20, 1)) 2).2 = 1
  rw [lemma_SelUpd1]

/-- `base = upd baseAB 3 (30, 2)`: `insC3`'s anchor `n2` is live, so `resolve`
short-circuits at it (the path `[1]` is never consulted). -/
theorem base_eq : base = upd baseAB 3 (30, 2) := by
  show do_ baseAB (3, 0, app_op_t.Ins 30 [1] 2) = upd baseAB 3 (30, 2)
  simp only [do_]
  rw [resolve_live_head baseAB 2 [1] contains_baseAB_2]

theorem contains_base_3 : contains base 3 = true := by
  rw [base_eq, lemma_InDomUpd1]; simp

theorem contains_base_2 : contains base 2 = true := by
  rw [base_eq, lemma_InDomUpd2 baseAB 2 3 (30, 2) (by decide)]; exact contains_baseAB_2

theorem contains_base_1 : contains base 1 = true := by
  rw [base_eq, lemma_InDomUpd2 baseAB 1 3 (30, 2) (by decide)]; exact contains_baseAB_1

theorem contains_base_0 : contains base 0 = false := by
  rw [base_eq, lemma_InDomUpd2 baseAB 0 3 (30, 2) (by decide)]; exact contains_baseAB_0

theorem contains_base_5 : contains base 5 = false := by
  rw [base_eq, lemma_InDomUpd2 baseAB 5 3 (30, 2) (by decide)]; exact contains_baseAB_5

theorem anc_base_3 : anc base 3 = 2 := by
  rw [base_eq]; show (sel (upd baseAB 3 (30, 2)) 3).2 = 2; rw [lemma_SelUpd1]

theorem anc_base_2 : anc base 2 = 1 := by
  rw [base_eq]
  show (sel (upd baseAB 3 (30, 2)) 2).2 = 1
  rw [lemma_SelUpd2 baseAB 2 3 (30, 2) (by decide)]; exact anc_baseAB_2

theorem anc_base_1 : anc base 1 = 0 := by
  rw [base_eq]
  show (sel (upd baseAB 3 (30, 2)) 1).2 = 0
  rw [lemma_SelUpd2 baseAB 1 3 (30, 2) (by decide)]; exact anc_baseAB_1

/-- `insE`'s length-2 path is the genuine ancestor chain of `n3` at the deep base. -/
theorem accurate_insE_base : accurate insE base := by
  show accurate (5, 1, app_op_t.Ins 40 [2, 1] 3) base
  exact Or.inr ⟨contains_base_3, anc_base_3, contains_base_2, anc_base_2,
                contains_base_1, anc_base_1⟩

/-! ## §3  The staled state `sigmaStaled` (anchor `n3` deleted) -/

theorem contains_sigmaStaled_3 : contains sigmaStaled 3 = false := by
  show contains (do_ base (4, 0, app_op_t.Del [2, 1] 3)) 3 = false
  rw [contains_doDel, contains_base_3]; simp

theorem contains_sigmaStaled_2 : contains sigmaStaled 2 = true := by
  show contains (do_ base (4, 0, app_op_t.Del [2, 1] 3)) 2 = true
  rw [contains_doDel, contains_base_2]; simp

theorem contains_sigmaStaled_1 : contains sigmaStaled 1 = true := by
  show contains (do_ base (4, 0, app_op_t.Del [2, 1] 3)) 1 = true
  rw [contains_doDel, contains_base_1]; simp

theorem contains_sigmaStaled_0 : contains sigmaStaled 0 = false := by
  show contains (do_ base (4, 0, app_op_t.Del [2, 1] 3)) 0 = false
  rw [contains_doDel, contains_base_0]; simp

theorem contains_sigmaStaled_5 : contains sigmaStaled 5 = false := by
  show contains (do_ base (4, 0, app_op_t.Del [2, 1] 3)) 5 = false
  rw [contains_doDel, contains_base_5]; simp

/-- `n2` keeps its parent `n1` (deleting the leaf `n3` rehomes nothing above). -/
theorem anc_sigmaStaled_2 : anc sigmaStaled 2 = 1 := by
  show anc (do_ base (4, 0, app_op_t.Del [2, 1] 3)) 2 = 1
  rw [anc_doDel, anc_base_2, if_neg (by decide)]

theorem anc_sigmaStaled_1 : anc sigmaStaled 1 = 0 := by
  show anc (do_ base (4, 0, app_op_t.Del [2, 1] 3)) 1 = 0
  rw [anc_doDel, anc_base_1, if_neg (by decide)]

/-- `insE` is INACCURATE at `sigmaStaled`: its anchor `n3` is gone. -/
theorem not_accurate_insE_sigmaStaled : ¬ accurate insE sigmaStaled := by
  show ¬ accurate (5, 1, app_op_t.Ins 40 [2, 1] 3) sigmaStaled
  intro h
  simp only [accurate, opLeaf, opPath] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact absurd h1 (by decide)
  · rw [contains_sigmaStaled_3] at h1; exact Bool.noConfusion h1

/-! ## §4  `do_`-reductions of `insE` and the two `b`s -/

/-- Live anchor: `insE` short-circuits at `n3` (path never read). -/
theorem reduce_insE (s : concrete_st) (h3 : contains s 3 = true) :
    do_ s (5, 1, app_op_t.Ins 40 [2, 1] 3) = upd s 5 (40, 3) := by
  simp only [do_]; rw [resolve_live_head s 3 [2, 1] h3]

/-- Dead anchor, live `n2`: `insE` climbs one hop to `n2`. -/
theorem reduce_insE_climb (s : concrete_st) (h3 : contains s 3 = false)
    (h2 : contains s 2 = true) :
    do_ s (5, 1, app_op_t.Ins 40 [2, 1] 3) = upd s 5 (40, 2) := by
  simp only [do_]
  rw [resolve_dead_head s 3 [2, 1] h3, resolve_live_head s 2 [1] h2]

/-- Dead `n3` AND dead `n2`, live `n1`: `insE` climbs TWO hops through the
partially-deleted chain to `n1`. -/
theorem reduce_insE_climb2 (s : concrete_st) (h3 : contains s 3 = false)
    (h2 : contains s 2 = false) (h1 : contains s 1 = true) :
    do_ s (5, 1, app_op_t.Ins 40 [2, 1] 3) = upd s 5 (40, 1) := by
  simp only [do_]
  rw [resolve_dead_head s 3 [2, 1] h3, resolve_dead_head s 2 [1] h2,
      resolve_live_head s 1 [] h1]

/-- `bIns` anchors at the live `n2`. -/
theorem reduce_bIns (s : concrete_st) (h2 : contains s 2 = true) :
    do_ s (6, 2, app_op_t.Ins 50 [1] 2) = upd s 6 (50, 2) := by
  simp only [do_]; rw [resolve_live_head s 2 [1] h2]

/-! ## §5  The climb-target genuinely MOVES; the middle-delete finding -/

/-- **The re-anchor is real.**  `insE` anchors node `5` at `n3` on `base` but at
`n2` on `sigmaStaled` — the carried path `[2,1]` is what carries the climb. -/
theorem climb_target_moves :
    anc (do_ base insE) 5 = 3 ∧ anc (do_ sigmaStaled insE) 5 = 2 := by
  refine ⟨?_, ?_⟩
  · show anc (do_ base (5, 1, app_op_t.Ins 40 [2, 1] 3)) 5 = 3
    rw [reduce_insE base contains_base_3]
    show (sel (upd base 5 (40, 3)) 5).2 = 3
    rw [lemma_SelUpd1]
  · show anc (do_ sigmaStaled (5, 1, app_op_t.Ins 40 [2, 1] 3)) 5 = 2
    rw [reduce_insE_climb sigmaStaled contains_sigmaStaled_3 contains_sigmaStaled_2]
    show (sel (upd sigmaStaled 5 (40, 2)) 5).2 = 2
    rw [lemma_SelUpd1]

theorem contains_sigmaMid_3 : contains sigmaMid 3 = true := by
  show contains (do_ base (4, 0, app_op_t.Del [1] 2)) 3 = true
  rw [contains_doDel, contains_base_3]; simp

/-- After deleting the MIDDLE `n2`, `n3` is rehomed up to `n1`. -/
theorem anc_sigmaMid_3 : anc sigmaMid 3 = 1 := by
  show anc (do_ base (4, 0, app_op_t.Del [1] 2)) 3 = 1
  rw [anc_doDel, anc_base_3, if_pos rfl]
  exact resolve_live_head base 1 [] contains_base_1

/-- **THE FINDING.**  Deleting a MIDDLE ancestor does NOT re-anchor an `Ins`: at
`sigmaMid`, `insE` is INACCURATE (its `IsAncPath` breaks at the `n3→n2` link) yet
its climb-target is UNCHANGED — `resolve` short-circuits at the surviving anchor
`n3`.  Only deleting the anchor itself (`sigmaStaled`) moves the climb. -/
theorem middle_delete_no_climb_move :
    (¬ accurate insE sigmaMid) ∧ anc (do_ sigmaMid insE) 5 = 3 := by
  refine ⟨?_, ?_⟩
  · show ¬ accurate (5, 1, app_op_t.Ins 40 [2, 1] 3) sigmaMid
    intro h
    simp only [accurate, opLeaf, opPath] at h
    rcases h with ⟨h1, _⟩ | ⟨_, hpath⟩
    · exact absurd h1 (by decide)
    · obtain ⟨hanc3, -, -⟩ := hpath
      rw [anc_sigmaMid_3] at hanc3; exact absurd hanc3 (by decide)
  · show anc (do_ sigmaMid (5, 1, app_op_t.Ins 40 [2, 1] 3)) 5 = 3
    rw [reduce_insE sigmaMid contains_sigmaMid_3]
    show (sel (upd sigmaMid 5 (40, 3)) 5).2 = 3
    rw [lemma_SelUpd1]

/-! ## §6  `bDel` / `bIns` are `accurate` at `sigmaStaled` -/

theorem accurate_bDel_sigmaStaled : accurate bDel sigmaStaled := by
  show accurate (6, 2, app_op_t.Del [1] 2) sigmaStaled
  exact Or.inr ⟨contains_sigmaStaled_2, anc_sigmaStaled_2, contains_sigmaStaled_1,
                anc_sigmaStaled_1⟩

theorem accurate_bIns_sigmaStaled : accurate bIns sigmaStaled := by
  show accurate (6, 2, app_op_t.Ins 50 [1] 2) sigmaStaled
  exact Or.inr ⟨contains_sigmaStaled_2, anc_sigmaStaled_2, contains_sigmaStaled_1,
                anc_sigmaStaled_1⟩

/-! ## §7  THE TEST — the non-empty-path staled swap HOLDS

`insE` is INACCURATE at `sigmaStaled` and genuinely re-anchors; `b` is `accurate`.
We evaluate the swap on the real `do_`. -/

/-- **VERDICT (decisive, Del at the climb-target).**  `insE ⇄ bDel` HOLDS (`eq`).
Order `[insE,bDel]`: node `5` lands at `n2`, then `bDel` rehomes it to `n1`.
Order `[bDel,insE]`: node `5` climbs `3→2→1` through the doubly-deleted chain
straight to `n1`.  Different routes, equal result — the eager rehoming exactly
compensates for the extra climb hop. -/
theorem swap_delN2_holds :
    eq (do_ (do_ sigmaStaled insE) bDel) (do_ (do_ sigmaStaled bDel) insE) := by
  show eq (do_ (do_ sigmaStaled (5, 1, app_op_t.Ins 40 [2, 1] 3))
              (6, 2, app_op_t.Del [1] 2))
          (do_ (do_ sigmaStaled (6, 2, app_op_t.Del [1] 2))
              (5, 1, app_op_t.Ins 40 [2, 1] 3))
  -- containments of `do_ sigmaStaled bDel` needed to reduce the RHS insert
  have hcD3 : contains (do_ sigmaStaled (6, 2, app_op_t.Del [1] 2)) 3 = false := by
    rw [contains_doDel, contains_sigmaStaled_3]; simp
  have hcD2 : contains (do_ sigmaStaled (6, 2, app_op_t.Del [1] 2)) 2 = false := by
    rw [contains_doDel, contains_sigmaStaled_2]; simp
  have hcD1 : contains (do_ sigmaStaled (6, 2, app_op_t.Del [1] 2)) 1 = true := by
    rw [contains_doDel, contains_sigmaStaled_1]; simp
  rw [reduce_insE_climb sigmaStaled contains_sigmaStaled_3 contains_sigmaStaled_2]
  rw [reduce_insE_climb2 (do_ sigmaStaled (6, 2, app_op_t.Del [1] 2)) hcD3 hcD2 hcD1]
  -- goal: eq (do_ (upd σ 5 (40,2)) (Del [1] 2)) (upd (do_ σ (Del [1] 2)) 5 (40,1))
  have hresU1 : resolve (upd sigmaStaled 5 (40, 2)) [1] = 1 :=
    resolve_live_head (upd sigmaStaled 5 (40, 2)) 1 [] (by
      rw [lemma_InDomUpd2 sigmaStaled 1 5 (40, 2) (by decide)]; exact contains_sigmaStaled_1)
  have hresS1 : resolve sigmaStaled [1] = 1 :=
    resolve_live_head sigmaStaled 1 [] contains_sigmaStaled_1
  intro k
  refine ⟨?_, ?_⟩
  · -- containment
    rw [contains_doDel (upd sigmaStaled 5 (40, 2)) 6 2 2 [1] k,
        lemma_InDomUpd1 sigmaStaled 5 k (40, 2),
        lemma_InDomUpd1 (do_ sigmaStaled (6, 2, app_op_t.Del [1] 2)) 5 k (40, 1),
        contains_doDel sigmaStaled 6 2 2 [1] k]
    by_cases hk2 : k = 2
    · subst hk2; simp
    · have hb : (k != 2) = true := by simp [hk2]
      rw [hb]; simp
  · -- value
    intro _
    rw [sel_doDel (upd sigmaStaled 5 (40, 2)) 6 2 2 [1] k, hresU1]
    by_cases hk5 : k = 5
    · subst hk5
      have hancU5 : anc (upd sigmaStaled 5 (40, 2)) 5 = 2 := by
        simp only [anc]; rw [lemma_SelUpd1]
      have helU5 : el (upd sigmaStaled 5 (40, 2)) 5 = 40 := by
        simp only [el]; rw [lemma_SelUpd1]
      rw [if_pos hancU5, helU5, lemma_SelUpd1]
    · have hne5 : (5 : ℕ) != k := by simp [Ne.symm hk5]
      have hancUk : anc (upd sigmaStaled 5 (40, 2)) k = anc sigmaStaled k := by
        simp only [anc]; rw [lemma_SelUpd2 sigmaStaled k 5 (40, 2) hne5]
      have helUk : el (upd sigmaStaled 5 (40, 2)) k = el sigmaStaled k := by
        simp only [el]; rw [lemma_SelUpd2 sigmaStaled k 5 (40, 2) hne5]
      have hselUk : sel (upd sigmaStaled 5 (40, 2)) k = sel sigmaStaled k :=
        lemma_SelUpd2 sigmaStaled k 5 (40, 2) hne5
      rw [hancUk, helUk, hselUk,
          lemma_SelUpd2 (do_ sigmaStaled (6, 2, app_op_t.Del [1] 2)) k 5 (40, 1) hne5,
          sel_doDel sigmaStaled 6 2 2 [1] k, hresS1]

/-- **VERDICT (second witness, Ins at the climb-target).**  `insE ⇄ bIns` HOLDS
(in fact literal `Eq` via `upd_comm`: two independent fresh inserts).  `insE`
re-anchors to `n2`; `bIns` also anchors at the live `n2`; neither references the
other's fresh id, so they commute. -/
theorem swap_insN2_holds :
    eq (do_ (do_ sigmaStaled insE) bIns) (do_ (do_ sigmaStaled bIns) insE) := by
  show eq (do_ (do_ sigmaStaled (5, 1, app_op_t.Ins 40 [2, 1] 3))
              (6, 2, app_op_t.Ins 50 [1] 2))
          (do_ (do_ sigmaStaled (6, 2, app_op_t.Ins 50 [1] 2))
              (5, 1, app_op_t.Ins 40 [2, 1] 3))
  have hU2 : contains (upd sigmaStaled 5 (40, 2)) 2 = true := by
    rw [lemma_InDomUpd2 sigmaStaled 2 5 (40, 2) (by decide)]; exact contains_sigmaStaled_2
  have hV3 : contains (upd sigmaStaled 6 (50, 2)) 3 = false := by
    rw [lemma_InDomUpd2 sigmaStaled 3 6 (50, 2) (by decide)]; exact contains_sigmaStaled_3
  have hV2 : contains (upd sigmaStaled 6 (50, 2)) 2 = true := by
    rw [lemma_InDomUpd2 sigmaStaled 2 6 (50, 2) (by decide)]; exact contains_sigmaStaled_2
  have hL : do_ (do_ sigmaStaled (5, 1, app_op_t.Ins 40 [2, 1] 3))
              (6, 2, app_op_t.Ins 50 [1] 2)
          = upd (upd sigmaStaled 5 (40, 2)) 6 (50, 2) := by
    rw [reduce_insE_climb sigmaStaled contains_sigmaStaled_3 contains_sigmaStaled_2,
        reduce_bIns _ hU2]
  have hR : do_ (do_ sigmaStaled (6, 2, app_op_t.Ins 50 [1] 2))
              (5, 1, app_op_t.Ins 40 [2, 1] 3)
          = upd (upd sigmaStaled 6 (50, 2)) 5 (40, 2) := by
    rw [reduce_bIns sigmaStaled contains_sigmaStaled_2, reduce_insE_climb _ hV3 hV2]
  have hEq : do_ (do_ sigmaStaled (5, 1, app_op_t.Ins 40 [2, 1] 3))
                (6, 2, app_op_t.Ins 50 [1] 2)
           = do_ (do_ sigmaStaled (6, 2, app_op_t.Ins 50 [1] 2))
                (5, 1, app_op_t.Ins 40 [2, 1] 3) := by
    rw [hL, hR]; exact upd_comm sigmaStaled 5 6 (40, 2) (50, 2) (by decide)
  rw [hEq]; intro k; exact ⟨rfl, fun _ => rfl⟩

/-! ## §8  Global cross-check — the two full enumerations converge -/

/-- Two full `loOnA`-respecting enumerations of `{insA,insB,insC3,delN3,insE,bDel}`
sharing the prefix `[insA,insB,insC3,delN3]` (folding to `sigmaStaled`) and
transposing the staled `insE` with `bDel` — they CONVERGE.  Here the pointwise
swap and global convergence coincide, ruling out a global divergence. -/
theorem full_enum_converges :
    eq (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, insC3, delN3, insE, bDel])
       (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, insC3, delN3, bDel, insE]) := by
  have h1 : applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, insC3, delN3, insE, bDel]
          = do_ (do_ sigmaStaled insE) bDel := rfl
  have h2 : applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, insC3, delN3, bDel, insE]
          = do_ (do_ sigmaStaled bDel) insE := rfl
  rw [h1, h2]; exact swap_delN2_holds

/-! ## §9  The bundled verdict -/

/-- **THE VERDICT — the NON-EMPTY-path staled swap HOLDS.**  At `sigmaStaled`:
`insE` is `accurate` at its deep base (`.1`) but INACCURATE at the staled state
(`.2.1`), and its climb-target genuinely MOVES from `n3` to `n2` (`.2.2.1`).  The
swapped-in `bDel` is `accurate` (`.2.2.2.1`).  Nonetheless the swap `insE ⇄ bDel`
HOLDS (`.2.2.2.2.1`), and so does `insE ⇄ bIns` (`.2.2.2.2.2`).  Selects the
nuanced **Route A**: a stronger swap VC conditioned only on the swapped-in op's
accuracy, valid even for non-empty-path, genuinely-re-anchoring staled inserts. -/
theorem verdict_nonempty_staled_swap_holds :
    accurate insE base
    ∧ (¬ accurate insE sigmaStaled)
    ∧ (anc (do_ base insE) 5 = 3 ∧ anc (do_ sigmaStaled insE) 5 = 2)
    ∧ accurate bDel sigmaStaled
    ∧ eq (do_ (do_ sigmaStaled insE) bDel) (do_ (do_ sigmaStaled bDel) insE)
    ∧ eq (do_ (do_ sigmaStaled insE) bIns) (do_ (do_ sigmaStaled bIns) insE) :=
  ⟨accurate_insE_base, not_accurate_insE_sigmaStaled, climb_target_moves,
   accurate_bDel_sigmaStaled, swap_delN2_holds, swap_insN2_holds⟩

/-! ## §10  Axiom audit — kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms swap_delN2_holds
#print axioms swap_insN2_holds
#print axioms climb_target_moves
#print axioms middle_delete_no_climb_move
#print axioms full_enum_converges
#print axioms verdict_nonempty_staled_swap_holds

end Sal.Metatheory.RGASwapNonEmpty
