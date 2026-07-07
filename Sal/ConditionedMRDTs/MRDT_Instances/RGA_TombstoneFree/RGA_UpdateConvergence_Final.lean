import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_InterleavedThreading
import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_UpdateConvergence_Assembly

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
open Sal.ConditionedMRDTs.RGAConditionedConvergence (RGA_conditioned_convergence_bothFaithful)
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

/-- **Update-layer convergence (CONDITIONAL on `hReach`).**  Two `loOnA`-respecting
enumerations of a backward-closed `E` fold from `init_st` to observationally-`eq`
states.  No swap/`EqSwap`/`hReady` premise survives; the residual `hReach` supplies
exactly the seven reachability/linkage conjuncts `C` cannot (STATUS block). -/
theorem RGA_update_convergence
    (C : ConditionedConfiguration RGACondSig)
    (Cfg : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (E : Set op_t) (hE : C.BackClosed E)
    (hids0 : ∀ o ∈ E, o.1 ≠ 0)
    (π₁ π₂ : List op_t)
    (h₁p : listPermOf π₁ E) (h₂p : listPermOf π₂ E)
    (h₁r : respects π₁ (loOnA RGACondSig Cfg E))
    (h₂r : respects π₂ (loOnA RGACondSig Cfg E))
    (hReach : ∀ (pre : List op_t) (a b : op_t),
        (∀ x ∈ pre, x ∈ E) → pre.Nodup → respects pre (loOnA RGACondSig Cfg E) →
        a ∈ E → b ∈ E → a ∉ pre → b ∉ pre → a ≠ b →
        ¬ loOnA RGACondSig Cfg E a b → ¬ loOnA RGACondSig Cfg E b a →
        (∀ z ∈ E, z ≠ a → loOnA RGACondSig Cfg E z a → z ∈ pre) →
        (∀ z ∈ E, z ≠ b → loOnA RGACondSig Cfg E z b → z ∈ pre) →
        contains (applySeqR init_st pre) 0 = false ∧ wf (applySeqR init_st pre)
        ∧ id_mono (applySeqR init_st pre)
        ∧ Faithful a (applySeqR init_st pre) ∧ Faithful b (applySeqR init_st pre)
        ∧ NoFreshClash a b ∧ NoFreshClash b a) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  apply RGA_conditioned_convergence_bothFaithful
    (loOnA RGACondSig Cfg E) E π₁ π₂ h₁p h₂p h₁r h₂r
  intro pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  obtain ⟨h0, hwf, hmono, hFa, hFb, hcab, hcba⟩ :=
    hReach pre a b hsub hnd hresp ha hb hanp hbnp hab hnab hnba hena henb
  exact ⟨C.distinctTs E hE ha hb hab, h0, hwf, hmono,
    fresh_ts_config C E hE hids0 pre hsub a ha hanp,
    fresh_ts_config C E hE hids0 pre hsub b hb hbnp, hFa, hFb, hcab, hcba⟩

/- ═══════════════════════════════════════════════════════════════════════════
   STATUS — what closes, and the exact residual (`hReach`).

   CLOSED unconditionally from the abstract configuration `C`:
   • the SWAP: the engine discharges it via `eqSwap_of_bothFaithful` (NEITHER
     operand `accurate`).  No `EqSwap`/swap-oracle premise survives (grep-checked).
   • `a.1 ≠ b.1`            — `C.distinctTs`.
   • `fresh_ts a`,`fresh_ts b` — `C.freshTs` + `fresh_ts_state_of_ids` (§2b),
     modulo the mild nonzero-id discipline `hids0`.

   The ORDER layer of `Faithful` is also closed (§1/§2): `goodFold_of_stepwise`
   threads the three `GoodStep` cases, and the staled-`Del` (`faithful_del_of_accurate`,
   from `accurate` alone) and concurrent-`Ins` (`goodStep_ins_concurrent`, from
   freshness) cases need NO history linkage.

   NOT closed from `C` (bundled into `hReach`, hence NOT unconditional):

   (1) **Ancestor-`Ins` `AncInsLink` — the sharp stuck case.**  For a fold step
       `o = (t,·,.Ins e p anch)` with `t ∈ recList a`, `goodStep_ins_ancestor`
       demands `AncInsLink s (recList a) t anch`: `recList a = D ++ t :: R` with `D`
       all dead, `t` dead, `anch` live, `resolve s R = anch`.  The live/dead split
       and `resolve s R = anch` (i.e. `R`'s head = `anch` = `t`'s recorded parent)
       hold ONLY if `recList a` coincides with `a`'s genuine `vis`-ancestor chain,
       consecutive members are true parent-links, and `o`'s recorded anchor is the
       successor of `t` in `recList a` — the `RecListVisFaithful` linkage.
       `ConditionedConfiguration` relates events only through `vis`/`distinct_ts`/
       `causal_mono`/`Inv`; it never reaches the RGA-syntactic anchor lists, and it
       ADMITS events whose `recList` is inconsistent with `vis` (exactly the
       `RGA_StaledDel_Gate.chainFaithful_not_preserved_under_clash_ins`
       counterexample).  So the linkage is neither a field of `C` nor derivable from
       its fields — it is a MODEL gap, matching the three prior verdicts.  This is
       why `Faithful a`/`Faithful b` sit in `hReach`.

   (2) **`NoFreshClash a b` / `b a`** — RGA form `b.1 ∉ recList a`.  M2's
       `noFreshClash_concurrent` gives the `vis`-ancestor id form; bridging needs
       `recList a ⊆ {a.1} ∪ vis-ancestor ids of a` — the SAME linkage as (1).

   (3) **`contains 0 = false`/`wf`/`id_mono` at the fold** — the reachable-state
       invariant.  M2's `inv_fold` yields `contains 0`/`wf` but needs
       `noopFeasible pre`, which the eligible-prefix oracle does NOT carry (its
       prefixes are `loOnA`-respecting sub-lists, not certified applicable-per-step);
       and `id_mono` is not even part of `RgaInv`.

   Two plumbing findings (why the naive M2 route does not apply directly):
   • `¬ loOnA a b → C.Concurrent a b` is FALSE: `loOnA` keeps only `vis`-edges that
     ALSO carry `appliesDependsOn`, so `¬ loOnA a b` does not give `¬ C.vis a b`.
     We route AROUND it — `distinctTs`/`freshTs` need no concurrency, and
     `NoFreshClash` is in `hReach` — so `conditioned_premises`' concurrency gate is
     never invoked.
   • `conditioned_premises` also needs `noopFeasible pre`, absent from the oracle.

   VERDICT: `RGA_update_convergence` closes CONDITIONALLY on `hReach`.  The swap
   oracle is eliminated and 3/10 conjuncts (+ the `Faithful` order layer) are
   discharged from `C`; the residual `hReach` is exactly the recList↔`vis` history
   linkage (feeding ancestor-`Ins` `AncInsLink`, `NoFreshClash`) plus the
   `noopFeasible`-of-eligible-interleaving reachable invariant — the facts a real
   RGA execution supplies by construction but the abstract configuration cannot.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## §4  Axiom audit -/

#print axioms faithful_del_of_accurate
#print axioms goodFold_of_stepwise
#print axioms faithful_ins_of_stepwise
#print axioms fresh_ts_config
#print axioms RGA_update_convergence

end Sal.ConditionedMRDTs.RGAUpdateConvergenceFinal
