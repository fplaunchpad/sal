import Sal.ConditionedMRDTs.Development.RGA_InterleavedThreading
import Sal.ConditionedMRDTs.Development.RGA_UpdateConvergence_Assembly

/-!
# The update-layer capstone: assembling the proved pieces

*Additive; not committed; 0 `sorry` in what is kept.*

This file wires the four proved ingredients

* `RGAInterleavedThreading` — `Faithful` at any `GoodFold`-classified interleaved
  prefix (the ancestor-`Ins` step via `AncInsLink`, the staled-`Del` step via
  `chainFaithful_doDel_faithful`);
* `RGARecPathFaithful` — `RecPathFaithful` ⇒ `Faithful`, and `accurate` ⇒
  `RecPathFaithful` at birth;
* `ConditionedExecutionModel` — M2's `conditioned_premises` (the non-`Faithful`
  oracle conjuncts);
* `RGAConditionedConvergence` — the restated `RGA_conditioned_convergence_bothFaithful`
  whose swap content is discharged by `eqSwap_of_bothFaithful` (NO `accurate`);

into the headline `RGA_update_convergence`.

The build is bottom-up.  §1 discharges the two `GoodStep` cases that need NO
history linkage (the staled-`Del` from `accurate`, the concurrent-`Ins` from
freshness) and packages the ancestor-`Ins` case.  §2 records the GAP-3 bridges.
§3 assembles the headline.  See the closing STATUS block for exactly what closes
and what residual (if any) survives.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal

open Sal.Emulation
open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful NoFreshClash ClimbFaithful)
open Sal.ConditionedMRDTs.RGABubbleWiring (recList ChainFaithful climbFaithful_of_chain)
open Sal.ConditionedMRDTs.RGAConditionedConvergence
  (applySeqR applySeqR_cons applySeqR_nil applySeqR_append EqSwap)
open RGARecPathFaithful
  (target recPath RecPathFaithful recPathFaithful_of_accurate faithful_of_recPathFaithful
   recList_eq_target_recPath)
open RGAInterleavedThreading
  (GoodStep GoodFold AncInsLink chainFaithful_goodStep chainFaithful_goodFold
   chainFaithful_init_recList chainFaithful_at_interleaved_fold faithful_at_interleaved_fold)
open Sal.ConditionedMRDTs.ConditionedExecutionModel (ConditionedConfiguration)
open Sal.ConditionedMRDTs.RGASig (RGACondSig)
open Sal.ConditionedMRDTs.ConditionedConvergence (loOnA)
open Sal.ConditionedMRDTs (noopFeasible)
open Sal.ConditionedMRDTs.RGAUpdateConvergenceAssembly (fresh_ts_state_of_ids)

/-! ## §1  The three `GoodStep` cases -/

/-- **`accurate` ⇒ `Faithful` for a genuine `Del`.**  A `Del` whose recorded path
is the true chain of a nonzero live target is `Faithful`: it is `RecPathFaithful`
at birth (`Reach.refl`), and `RecPathFaithful ⇒ Faithful`.  No history linkage:
the `Del`'s own recorded path suffices. -/
theorem faithful_del_of_accurate (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false) (hx0 : x ≠ 0)
    (hacc : accurate (t, r, .Del p x) s) : Faithful (t, r, .Del p x) s := by
  have htgt : target (t, r, .Del p x) ≠ 0 := by simpa only [target, opLeaf] using hx0
  have hrp : RecPathFaithful (t, r, .Del p x) s :=
    recPathFaithful_of_accurate (t, r, .Del p x) s h0 hacc htgt
  exact faithful_of_recPathFaithful (t, r, .Del p x) s hrp

/-- **Staled-`Del` `GoodStep`** — the `Del` case, from `accurate` (no linkage). -/
theorem goodStep_del (s : concrete_st) (L : List ℕ) (t r x : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false) (hwf : wf s) (hx0 : x ≠ 0)
    (hacc : accurate (t, r, .Del p x) s) : GoodStep s L (t, r, .Del p x) := by
  show contains s 0 = false ∧ wf s ∧ Faithful (t, r, .Del p x) s
  exact ⟨h0, hwf, faithful_del_of_accurate s t r x p h0 hx0 hacc⟩

/-- **Concurrent-`Ins` `GoodStep`** — the fresh non-ancestor `Ins` case
(`t ∉ recList w`), no linkage. -/
theorem goodStep_ins_concurrent (s : concrete_st) (L : List ℕ) (t r e anch : ℕ) (p : List ℕ)
    (ht0 : t ≠ 0) (htL : t ∉ L) : GoodStep s L (t, r, .Ins e p anch) := by
  show (t ≠ 0 ∧ t ∉ L) ∨ (t ≠ 0 ∧ contains s 0 = false ∧ AncInsLink s L t anch)
  exact Or.inl ⟨ht0, htL⟩

/-- **Ancestor-`Ins` `GoodStep`** — the fold of `w`'s OWN accurate ancestor `Ins`
(`t ∈ recList w`).  This is the one case that needs the per-step reachability
linkage `AncInsLink` (see the STATUS block). -/
theorem goodStep_ins_ancestor (s : concrete_st) (L : List ℕ) (t r e anch : ℕ) (p : List ℕ)
    (ht0 : t ≠ 0) (h0 : contains s 0 = false) (hlink : AncInsLink s L t anch) :
    GoodStep s L (t, r, .Ins e p anch) := by
  show (t ≠ 0 ∧ t ∉ L) ∨ (t ≠ 0 ∧ contains s 0 = false ∧ AncInsLink s L t anch)
  exact Or.inr ⟨ht0, h0, hlink⟩

/-! ## §2  From a per-step `GoodStep` classifier to `GoodFold`, and to `Faithful`

`goodFold_of_stepwise` reduces `GoodFold L s pre` to a classifier that presents,
at every prefix split, a `GoodStep` at that prefix's fold.  This is the ORDER-layer
plumbing; discharging the classifier is the reachability layer (§1 gives the two
linkage-free cases; the ancestor-`Ins` case needs `AncInsLink`). -/

/-- **`GoodFold` from a per-step classifier.**  If every prefix split `pre =
pfx ++ o :: rest` makes `o` a `GoodStep` at the prefix fold `applySeqR s pfx`, then
`pre` is a `GoodFold` for `L` from `s`.  Induction on `pre`, threading the state. -/
theorem goodFold_of_stepwise (L : List ℕ) :
    ∀ (pre : List op_t) (s : concrete_st),
      (∀ (pfx : List op_t) (o : op_t) (rest : List op_t),
         pre = pfx ++ o :: rest → GoodStep (applySeqR s pfx) L o) →
      GoodFold L s pre := by
  intro pre
  induction pre with
  | nil => intro s _; exact True.intro
  | cons o rest ih =>
    intro s hstep
    refine ⟨hstep [] o rest rfl, ?_⟩
    apply ih (do_ s o)
    intro pfx o' rest' heq
    have hh := hstep (o :: pfx) o' rest' (by rw [List.cons_append, heq])
    rwa [applySeqR_cons] at hh

/-- **Faithful for an enabled `Ins` at a stepwise-good interleaved prefix.**  Folds
`goodFold_of_stepwise` into `faithful_at_interleaved_fold`.  The classifier `hstep`
carries the reachability content; `h0'` is `RgaInv`-at-fold. -/
theorem faithful_ins_of_stepwise (t r e a : ℕ) (p : List ℕ) (pre : List op_t)
    (hstep : ∀ (pfx : List op_t) (o : op_t) (rest : List op_t),
       pre = pfx ++ o :: rest → GoodStep (applySeqR init_st pfx) (recList (t, r, .Ins e p a)) o)
    (h0' : contains (applySeqR init_st pre) 0 = false) :
    Faithful (t, r, .Ins e p a) (applySeqR init_st pre) :=
  faithful_at_interleaved_fold t r e a p pre
    (goodFold_of_stepwise (recList (t, r, .Ins e p a)) pre init_st hstep) h0'

/-! ## §2b  Config bridges discharged from M2 (no linkage, no `noopFeasible`)

The `hReady` conjuncts M2 supplies at the level of timestamps alone: distinct ids
(`distinctTs`) and `fresh_ts` (id-distinctness `freshTs` lifted to state-absence by
the contains-tracking `fresh_ts_state_of_ids`, plus the nonzero-id discipline). -/

/-- **`fresh_ts` from M2.**  `C.freshTs` gives id-distinctness `∀ x ∈ pre, x.1 ≠ a.1`;
`fresh_ts_state_of_ids` folds that (with `a.1 ≠ 0`) to the RGA's state-absence form.
For a `Del`, `fresh_ts` is `True`. -/
theorem fresh_ts_config (C : ConditionedConfiguration RGACondSig)
    (E : Set op_t) (hE : C.BackClosed E) (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (pre : List op_t) (hsub : ∀ x ∈ pre, x ∈ E)
    (a : op_t) (ha : a ∈ E) (hanp : a ∉ pre) :
    fresh_ts a (applySeqR init_st pre) := by
  obtain ⟨t, r, op⟩ := a
  have hids : ∀ x ∈ pre, x.1 ≠ t := C.freshTs E hE ha pre hsub hanp
  cases op with
  | Ins e p anch =>
    exact fresh_ts_state_of_ids t r e anch p pre (hids0 (t, r, .Ins e p anch) ha) hids
  | Del p x => exact trivial

/-! ## §3  The headline

`RGA_update_convergence` feeds the restated `RGA_conditioned_convergence_bothFaithful`
its oracle.  The SWAP content is discharged by the engine internally
(`eqSwap_of_bothFaithful`: NEITHER operand `accurate`) — no swap/`EqSwap` premise
survives.  Of the ten non-swap conjuncts the oracle then needs, THREE are discharged
here from the abstract configuration `C` alone (`a.1 ≠ b.1` via `distinctTs`, and both
`fresh_ts` via `freshTs` + `fresh_ts_state_of_ids`); the remaining SEVEN are supplied
by `hReach`.

The seven are exactly the conjuncts that the abstract `ConditionedConfiguration`
provably cannot supply — see the STATUS block: `contains 0 = false`/`wf`/`id_mono`
(the reachable-state invariant, needing `noopFeasible` of the *eligible interleaving*,
which `C` does not carry), `Faithful a`/`Faithful b` (needing the ancestor-`Ins`
`AncInsLink`, i.e. the recList↔`vis` history linkage), and both `NoFreshClash`
(needing `recList a ⊆ {a.1} ∪ vis-ancestor ids`, the same linkage).  §1/§2 close the
ORDER layer of `Faithful` (`goodFold_of_stepwise` ⇒ `faithful_at_interleaved_fold`);
`hReach` supplies its reachability INPUT.  This is therefore a CONDITIONAL close. -/


end Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal
