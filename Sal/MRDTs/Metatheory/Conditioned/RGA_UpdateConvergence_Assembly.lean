import Sal.MRDTs.Metatheory.Conditioned.RGA_EnablementBase
import Sal.MRDTs.Metatheory.Conditioned.ConditionedExecutionModel

/-!
# Stage-1 assembly, post-GAP-1: the RESTATED-engine discharge attempt

*Additive; modifies no existing file; introduces no `sorry`.*

`RGA_ConditionedConvergence.lean` has been RESTATED so its swap oracle ranges only
over ELIGIBLE prefixes (nodup, `respects`-ordered, `E`-drawn, disjoint from the
swapped pair, with BOTH events ENABLED).  GAP-1 (the over-quantified, unsatisfiable
oracle) is thereby fixed.  This file carries the assembly one step further and
records, kernel-clean, exactly which of the ten `hReady` conjuncts are MECHANICAL
and which are the located residual.

## What closes here (kernel-clean, 0-sorry)

* **§1  the `fresh_ts` state-form GAP-3 bridge** — `fresh_ts_state_of_ids`.
  M2's `freshTs` emits only the id-DISTINCTNESS form `∀ x ∈ pre, x.1 ≠ t`; the RGA's
  `fresh_ts` needs the STATE-ABSENCE form `contains (fold pre) t = false`.  The bridge
  is a contains-tracking induction: an `Ins` with id `≠ t` never stores `t`
  (`lemma_InDomUpd2`), a `Del` never stores anything (`contains_doDel`), and `t` is
  dead at `init`.  This is the ONE genuinely-mechanical member of the GAP-3 cluster.

## The located residual — why the headline does NOT close unconditionally

The verdict block of `RGA_ConditionedConvergence.lean` (§ ~664-724) routes the
unconditional close to "ONE open M1 fact plus mechanical GAP-3 bridges".  Carrying
the discharge out shows the residual is sharper and is NOT a single M1 lemma:
**three** of the ten conjuncts share ONE missing invariant, and it is genuinely
absent from the eligible-prefix data and from M2's `ConditionedConfiguration`.

**The missing invariant (call it `RecListVisFaithful a`).**  For a pending event
`a = (t,r,.Ins e p anch)`, its RGA-recorded anchor path `recList a = anch :: p`
coincides with — and is correctly parent-linked as — `a`'s `vis`-ancestor id-chain
in the execution model.  Concretely: each `c ∈ recList a` is the id of `a` or a
`vis`-ancestor of `a`, and consecutive members are the true `anc`-links.

This one invariant is what THREE conjuncts need — none of which M2 supplies:

* **`Faithful a (fold pre)`** (the M1 build-up).  `Faithful a` = `ChainFaithful
  (recList a) (fold pre)`.  Threading it over the interleaved `pre` classifies each
  step: concurrent fresh `Ins`/`Faithful` `Del` are `IncompStep`s
  (`chainFaithful_incompStep`), a causal-past non-ancestor `Ins` is a non-clash
  `Ins` (`chainFaithful_doIns`) — BUT an ANCESTOR `Ins` (id `t' ∈ recList a`) is the
  wall.  Folding `(t',r',.Ins e' p' anch')` with `t' ∈ recList a` at `s`, when `t'`
  becomes the leftmost-live member of `recList a`, leaves the ChainFaithfulAux
  top-level obligation

      resolve s ((recList a).filter (· ≠ t')) = anch'          -- (★)

  i.e. `t'`'s successor in `recList a`'s live chain must equal the insert's live
  anchor.  Nothing in `ChainFaithful s (recList a)` (`t'` was DEAD there),
  `accurate` of the insert, `id_mono`, or `wf` forces (★): it is exactly the
  `recList`-consistency the counterexample
  `RGA_StaledDel_Gate.chainFaithful_not_preserved_under_clash_ins` REFUTES for a
  genuine-looking but inconsistent `recList` (records `5` as `8`'s ancestor).  (★)
  holds only if `recList a` is `a`'s TRUE chain — i.e. `RecListVisFaithful a`.

* **`id_mono (fold pre)`** (GAP-3, NOT mechanical).  Threading `id_mono` over an
  `Ins` needs `mono_alloc` — the inserted anchor `< t'` (`id_mono_doIns`).  M2 gives
  only `causal_mono : vis c c' → c.1 < c'.1`; concluding `anch' < t'` from it needs
  `anch'`'s inserter to be a `vis`-ancestor of `t'`'s inserter — the SAME
  `recList`↔`vis` linkage.  An eligible (`loOnA`-respecting) prefix need not be
  timestamp-increasing, so the naive `mono_alloc`-per-step is false without the link.

* **`NoFreshClash a b`** (GAP-3, NOT mechanical).  RGA form `b.1 ∉ recList a`; M2's
  `noFreshClash_concurrent` gives `∀ c, (c = a ∨ vis c a) → c ∈ events → c.1 ≠ b.1`.
  Bridging needs `recList a ⊆ {a.1} ∪ {vis-ancestor ids of a}` — again the linkage.

Mechanical (and only these): `a.1 ≠ b.1` (M2 `distinctTs`), `contains (fold pre)
0 = false` and `wf (fold pre)` (M2 `inv_fold`, `RGAUpdateConvergence.hReady_clean_conjuncts`),
and `fresh_ts` (§1 below).

**Two further M2-plumbing mismatches** (independent of the linkage):

* the engine's incomparability is `¬ loOnA a b ∧ ¬ loOnA b a`, which is WEAKER than
  M2's `C.Concurrent a b = ¬ vis a b ∧ ¬ vis b a` that `conditioned_premises`
  consumes (a vis-edge without `appliesDependsOn` is not a `loOnA` edge), so
  `conditioned_premises` is not directly applicable at an eligible pair;
* `conditioned_premises` needs `noopFeasible pre`, which the eligible-prefix oracle
  does not carry (that is `interleavingFeasible`, itself an assumption).

VERDICT: `RGA_update_convergence` does NOT close unconditionally.  GAP-1 is fixed
and the oracle is now satisfiable in shape, but discharging it still requires the
`RecListVisFaithful` history-linkage invariant (feeding `Faithful` + `id_mono` +
`NoFreshClash`), which `ConditionedConfiguration` — relating events only through
`vis`/`distinct_ts`/`causal_mono`, never through the RGA-syntactic anchor lists —
does not carry.  This is a MODEL gap, not a fiddly proof tail.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAUpdateConvergenceAssembly

open Sal.Emulation
open Sal.Metatheory.RGAGeneralSwap (contains_init)
open Sal.Metatheory.RGAConditionedConvergence (applySeqR applySeqR_cons applySeqR_nil)

/-! ## §1  The `fresh_ts` state-form GAP-3 bridge (mechanical, kernel-clean) -/

/-- One fold step keeps a dead id dead, provided the step's id differs from it.
`Ins` (id `≠ k`) stores `k` nowhere (`lemma_InDomUpd2`); `Del` stores nothing
(`contains_doDel`). -/
theorem contains_do_false_of_ne (s : concrete_st) (o : op_t) (k : ℕ)
    (hne : o.1 ≠ k) (hf : contains s k = false) :
    contains (do_ s o) k = false := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
    have hstep : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
      simp only [do_]
    have hbne : (t : ℕ) != k := by
      simp only [bne_iff_ne, ne_eq]; exact hne
    rw [hstep, lemma_InDomUpd2 s k t (e, resolve s (a :: pre)) hbne]; exact hf
  | Del pre x =>
    rw [contains_doDel]; simp only [hf, Bool.false_and]

/-- **Contains-tracking over a fold.**  If every op in `pre` has id `≠ k` and `k`
is dead at `s`, then `k` stays dead across `applySeqR s pre`. -/
theorem contains_fold_false (k : ℕ) :
    ∀ (pre : List op_t) (s : concrete_st),
      (∀ o ∈ pre, o.1 ≠ k) → contains s k = false →
      contains (applySeqR s pre) k = false := by
  intro pre
  induction pre with
  | nil => intro s _ hf; simpa using hf
  | cons o rest ih =>
    intro s hne hf
    rw [applySeqR_cons]
    exact ih (do_ s o) (fun o' ho' => hne o' (List.mem_cons_of_mem _ ho'))
      (contains_do_false_of_ne s o k (hne o List.mem_cons_self) hf)

/-- **The `fresh_ts` state-form GAP-3 bridge.**  From M2's id-distinctness form
`∀ x ∈ pre, x.1 ≠ t` (its `freshTs`), and `t ≠ 0`, the RGA's state-absence form
`fresh_ts (t,r,.Ins e p a) (applySeqR init_st pre)` follows: `t` is dead at `init`
(`contains_init`) and no `pre`-step stores it. -/
theorem fresh_ts_state_of_ids (t r e a : ℕ) (p : List ℕ) (pre : List op_t)
    (ht0 : t ≠ 0) (hids : ∀ x ∈ pre, x.1 ≠ t) :
    fresh_ts (t, r, .Ins e p a) (applySeqR init_st pre) := by
  refine ⟨ht0, ?_⟩
  exact contains_fold_false t pre init_st hids (contains_init t)

/-! ## §2  Axiom audit — the mechanical bridge is kernel-clean (no `sorryAx`). -/

#print axioms contains_do_false_of_ne
#print axioms contains_fold_false
#print axioms fresh_ts_state_of_ids

end Sal.Metatheory.RGAUpdateConvergenceAssembly
