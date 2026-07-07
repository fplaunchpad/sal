import Sal.MRDTs.Metatheory.Conditioned.ConditionedConvergence

/-!
# Task #10 (the final gate): does `interleavingFeasible` hold for the tombstone-free RGA?

`CONDITIONED_METATHEORY_PLAN.md`, stages 6–7.  `ConditionedConvergence.lean`
(task #9) closed the *order* half of conditioned convergence and localized the
whole residual RGA obstruction to a single oracle: the conditioned bubble
(`applySeq_swap_loOnA_incomparable_C`) needs, at every **hybrid** interleaved
fold state, the applicability side conditions `applicable a` / `applicable b`.
`interleavingFeasible D ev` is exactly the promise that supplies them —
*applicable-OR-no-op at every `nodup` sub-list fold from `init`*
(`ConditionedConvergence.lean:406`).  This file decides, on the **real** RGA
`do_`, whether that oracle holds — and if not, whether the failing case is a
genuine divergence or an artifact of the oracle.

## The concrete probe (all folds start from `init_st`, so `ev` is reachable)

Four events building the chain `root → node1 → node2`, plus a concurrent
insert under `node1` and a concurrent delete of `node1`:

* `insA = (1,0, Ins 10 [] 0)` — create `node1` at the root;
* `insB = (2,0, Ins 20 [] 1)` — create `node2` anchored at `node1`;
* `insC = (3,1, Ins 30 [] 1)` — create `node3` anchored at `node1` (its recorded
  path/anchor references `node1`);
* `delA = (4,0, Del [] 1)`   — delete `node1` (which **rehomes** its children up
  to `node1`'s parent, the root).

`insC` and `delA` are concurrent (different replicas, no vis edge), so `loOnA`
orders neither before the other — a `loOnA`-respecting linearization is free to
fold `delA` before `insC`, at which point `insC`'s anchor `node1` is gone.

## The verdict, established below (0 sorries, kernel-clean)

1. **The concurrent `Del` DOES stale the concurrent `Ins`'s path**
   (`rehoming_stales_path`): `insC` is `accurate` at `baseAB` but not at
   `do_ baseAB delA` (its anchor `node1` was physically removed).  Yet the two
   orders **do NOT diverge** (`orders_converge`, an instance of the RGA's proved
   `insdel_comm`): the staled `insC` climbs its path to the nearest live ancestor
   (the root `0`), which is *exactly* where `delA` rehomes `node1`'s children.
   Path-carrying convergence, as designed.

2. **The staled `Ins` is NOT a no-op** (`staled_ins_not_noop`): at
   `do_ baseAB delA` it still inserts `node3` (now anchored at the relocated
   root `0`), so `do_ (do_ baseAB delA) insC ≠ do_ baseAB delA`.  It is also not
   `applicable` there (`staled_ins_not_applicable`: `accurate` fails).  Hence
   `appOrNoop` fails, and therefore, per the task's dichotomy,

   > **`interleavingFeasible RGACondSig` is FALSE** (`not_interleavingFeasible_RGA`).

3. **But the failure is the ORACLE's, not the RGA's** — the decisive research
   finding.  `interleavingFeasible` is *sufficient* for the bubble, but it is
   NOT necessary for convergence: `full_enumerations_converge` exhibits two
   linearizations of the reachable set `{insA,insB,insC,delA}` — one of which
   (`[insA,insB,delA,insC]`) folds `insC` at the staled state that violates the
   oracle — that nonetheless **converge**.  The RGA's convergence is carried by
   the semantic swap `insdel_comm` (accuracy at the swap's *common base*
   `baseAB`, where BOTH events are applicable), NOT by applicable-or-no-op at
   every hybrid prefix.

## What it implies for hosting the RGA through `conditioned_convergence_on`

`conditioned_convergence_on` (the closed §3 headline) reduces to the
UNCONDITIONED `convergence_on_u` and needs `UpdateVCs` (Lean-`Eq`
`commutes`) — which the RGA lacks (`rc = Either`; its commutation lemmas
conclude the observational `eq`, not Lean `Eq`).  So the RGA must take the §4
`commutesOn`-only route, whose bubble is discharged only by
`interleavingFeasible`.  Since that oracle is **false** for the RGA, hosting
does **not** close through it as architected.

The obstruction is now fully characterized and it is NOT unreachability: the
violating prefix `[insA,insB,delA]` is a legitimate causal linearization
prefix; the staled `insC` folded there is genuinely non-applicable and
non-no-op, and `noopFeasible` cannot absorb it because it is not an identity
(it inserts `node3`).  The gap is that the bubble asks for POINTWISE
applicability at hybrid states, while the RGA only supplies SEMANTIC
commutation at the both-applicable common base.  So the required architecture
change is a bubble whose every swap is justified by the semantic `eq`-swap at a
state where both swapped events are `accurate`/`applicable` — i.e. the two
concurrent events are transposed at their last common causally-prior fold
(`baseAB`), never at a hybrid state that has already staled one of them.  A
"reachability-restricted" bubble in this SWAP-STATE sense (not an
interleaving-restriction) closes it; `interleavingFeasible` as stated is simply
too strong for a path-carrying / rehoming CRDT.

## Axiom status
Every headline decl is kernel-clean (`propext, Classical.choice, Quot.sound`
only — no `sorryAx`, no `native_decide`/`ofReduceBool`).  The imported
`Merge_Linearization_Set` sorries are not transitively touched.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGARehomingGate

open Sal.Emulation
open Sal.Metatheory.RGASig (RGACondSig)
open Sal.Metatheory.G2Probe (contains_doIns_self)
open Sal.Metatheory.ConditionedConvergence (interleavingFeasible appOrNoop)

/-! ## §1  The four events and the base chain `root → node1 → node2` -/

/-- Create `node1` (element 10) at the root. -/
def insA : Op app_op_t := (1, 0, .Ins 10 [] 0)
/-- Create `node2` (element 20) anchored at `node1`. -/
def insB : Op app_op_t := (2, 0, .Ins 20 [] 1)
/-- Create `node3` (element 30) anchored at `node1` — a *different replica* (`1`),
so this is concurrent with `delA`.  Its recorded anchor/path references `node1`. -/
def insC : Op app_op_t := (3, 1, .Ins 30 [] 1)
/-- Delete `node1`, rehoming its children up to `node1`'s parent (the root). -/
def delA : Op app_op_t := (4, 0, .Del [] 1)

/-- The base chain `root → node1 → node2`, built from `init_st` by real ops. -/
def baseAB : concrete_st := do_ (do_ init_st insA) insB

/-! ## §2  Base-state facts (kernel-clean, via the RGA map algebra) -/

/-- Reduce `baseAB` to two explicit `upd`s.  `insA`'s anchor `0` is dead
(`contains init_st 0 = false`) so it resolves to the root; `insB`'s anchor
`node1` is live so it resolves to itself. -/
theorem baseAB_eq : baseAB = upd (upd init_st 1 (10, 0)) 2 (20, 1) := by
  have hc0 : contains init_st 0 = false := by simp [init_st]
  have hA : do_ init_st insA = upd init_st 1 (10, 0) := by
    show do_ init_st (1, 0, app_op_t.Ins 10 [] 0) = upd init_st 1 (10, 0)
    simp only [do_]
    rw [resolve_dead_head init_st 0 [] hc0]
    simp only [resolve]
  show do_ (do_ init_st insA) insB = _
  rw [hA]
  show do_ (upd init_st 1 (10, 0)) (2, 0, app_op_t.Ins 20 [] 1) = _
  simp only [do_]
  have hc1 : contains (upd init_st 1 (10, 0)) 1 = true := by
    rw [lemma_InDomUpd1]; simp
  rw [resolve_live_head (upd init_st 1 (10, 0)) 1 [] hc1]

theorem contains_baseAB_1 : contains baseAB 1 = true := by
  rw [baseAB_eq, lemma_InDomUpd1, lemma_InDomUpd1]; simp

theorem contains_baseAB_0 : contains baseAB 0 = false := by
  rw [baseAB_eq, lemma_InDomUpd1, lemma_InDomUpd1]; simp [init_st]

theorem contains_baseAB_3 : contains baseAB 3 = false := by
  rw [baseAB_eq, lemma_InDomUpd1, lemma_InDomUpd1]; simp [init_st]

theorem anc_baseAB_1 : anc baseAB 1 = 0 := by
  rw [baseAB_eq]
  show (sel (upd (upd init_st 1 (10, 0)) 2 (20, 1)) 1).2 = 0
  rw [lemma_SelUpd2 (upd init_st 1 (10, 0)) 1 2 (20, 1) (by decide), lemma_SelUpd1]

/-! ## §3  Applicability of `insC` / `delA` at the common base `baseAB`

Both events are `accurate` (path is the true ancestor chain) and `fresh` at
`baseAB`: this is the state where a real execution *generates* them, and where
the semantic swap `insdel_comm` fires. -/

theorem accurate_insC_base : accurate insC baseAB := by
  show accurate (3, 1, app_op_t.Ins 30 [] 1) baseAB
  refine Or.inr ⟨contains_baseAB_1, ?_⟩
  show anc baseAB 1 = 0
  exact anc_baseAB_1

theorem accurate_delA_base : accurate delA baseAB := by
  show accurate (4, 0, app_op_t.Del [] 1) baseAB
  refine Or.inr ⟨contains_baseAB_1, ?_⟩
  show anc baseAB 1 = 0
  exact anc_baseAB_1

theorem fresh_insC_base : fresh_ts insC baseAB := by
  show (3 : ℕ) ≠ 0 ∧ contains baseAB 3 = false
  exact ⟨by decide, contains_baseAB_3⟩

theorem fresh_delA_base : fresh_ts delA baseAB := by
  show True; trivial

/-- `insC` is `applicable` (= `accurate ∧ fresh_ts`) at the common base. -/
theorem applicable_insC_base : RGACondSig.applicable insC baseAB :=
  ⟨accurate_insC_base, fresh_insC_base⟩

/-! ## §4  Step 1 — the concurrent `Del` stales the concurrent `Ins`'s path

`insC`'s anchor `node1` is physically removed by `delA`, so at `do_ baseAB delA`
the recorded path is no longer accurate.  (Contrast: it WAS accurate at
`baseAB`.) -/

/-- After `delA`, `node1` is absent. -/
theorem contains_node1_after_delA : contains (do_ baseAB delA) 1 = false := by
  show contains (do_ baseAB (4, 0, app_op_t.Del [] 1)) 1 = false
  rw [contains_doDel]; simp

/-- `insC` is no longer `accurate` after `delA`: its anchor `node1` is gone, so
neither `accurate` disjunct holds. -/
theorem accurate_insC_after_delA : ¬ accurate insC (do_ baseAB delA) := by
  show ¬ accurate (3, 1, app_op_t.Ins 30 [] 1) (do_ baseAB delA)
  intro h
  simp only [accurate, opLeaf, opPath] at h
  have hc := contains_node1_after_delA
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact one_ne_zero h1
  · rw [hc] at h1; exact Bool.noConfusion h1

/-- **Step 1 verdict.**  The concurrent `Del` DOES stale the concurrent `Ins`'s
path (`accurate` at the base, not `accurate` after the `Del`) — but §5 shows the
two orders nonetheless converge. -/
theorem rehoming_stales_path :
    accurate insC baseAB ∧ ¬ accurate insC (do_ baseAB delA) :=
  ⟨accurate_insC_base, accurate_insC_after_delA⟩

/-! ## §5  The two orders CONVERGE (path-carrying design; `insdel_comm`)

At the common base `baseAB` both events are `accurate` + `fresh`, so the RGA's
proved insert/delete commutation applies: `Del`-then-`Ins` = `Ins`-then-`Del`.
The staled `insC` climbs its path to the root `0` — exactly the target `delA`
rehomes `node1`'s children to — so the folds agree. -/

/-- **Step 1, second half.**  `do_ (do_ baseAB delA) insC = do_ (do_ baseAB insC) delA`
(as the RGA's observational `eq`), a direct instance of `insdel_comm`.  So the
concurrent `Del` rehoming does **not** cause the two orders to diverge. -/
theorem orders_converge :
    eq (do_ (do_ baseAB insC) delA) (do_ (do_ baseAB delA) insC) :=
  insdel_comm baseAB 3 1 30 1 [] 4 0 [] 1 (by decide) contains_baseAB_0
    accurate_insC_base accurate_delA_base fresh_insC_base fresh_delA_base

/-! ## §6  Step 2 — the staled `Ins` is NOT a no-op (so `interleavingFeasible` is FALSE)

Evaluate the staled application `do_ (do_ baseAB delA) insC` against the
interleaved state `do_ baseAB delA`.  They DIFFER: `insC` still inserts `node3`
(at the relocated anchor `0`), so it is neither the identity nor `applicable`.
Per the task's dichotomy this makes `interleavingFeasible` FALSE for the RGA. -/

/-- The staled `Ins` still inserts `node3`. -/
theorem contains_node3_after_staled_ins : contains (do_ (do_ baseAB delA) insC) 3 = true := by
  show contains (do_ (do_ baseAB delA) (3, 1, app_op_t.Ins 30 [] 1)) 3 = true
  exact contains_doIns_self (do_ baseAB delA) 3 1 30 1 []

/-- **Step 2, core.**  The staled `Ins` is NOT a no-op: applying it changes the
state (it adds `node3`), so `do_ (do_ baseAB delA) insC ≠ do_ baseAB delA`. -/
theorem staled_ins_not_noop : do_ (do_ baseAB delA) insC ≠ do_ baseAB delA := by
  intro h
  have hcontra : contains (do_ (do_ baseAB delA) insC) 3 = contains (do_ baseAB delA) 3 :=
    congrArg (fun s => contains s 3) h
  have hR : contains (do_ baseAB delA) 3 = false := by
    show contains (do_ baseAB (4, 0, app_op_t.Del [] 1)) 3 = false
    rw [contains_doDel, contains_baseAB_3]; simp
  rw [contains_node3_after_staled_ins, hR] at hcontra
  exact Bool.noConfusion hcontra

/-- The staled `Ins` is not `applicable` at the interleaved state either. -/
theorem staled_ins_not_applicable : ¬ RGACondSig.applicable insC (do_ baseAB delA) :=
  fun h => accurate_insC_after_delA h.1

/-! ## §7  The reachable event set and the `interleavingFeasible` refutation -/

/-- The reachable four-event set (single Ins-chain + concurrent Ins + concurrent Del). -/
def evR : Set (Op app_op_t) := {insA, insB, insC, delA}

/-- The interleaved prefix `[insA, insB, delA]` folds from `init` to `do_ baseAB delA`. -/
theorem applySeq_pre_eq :
    applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA] = do_ baseAB delA := rfl

/-- At the staled interleaved state, `insC` is neither `applicable` nor a no-op —
so `appOrNoop` fails.  This is the single side condition the conditioned bubble
cannot get from `noopFeasible`. -/
theorem not_appOrNoop_insC :
    ¬ appOrNoop RGACondSig insC (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA]) := by
  rw [applySeq_pre_eq]
  rintro (hApp | hNoop)
  · exact accurate_insC_after_delA hApp.1
  · exact staled_ins_not_noop hNoop

/-- **THE VERDICT (step 2).**  `interleavingFeasible` is FALSE for the tombstone-free
RGA: the reachable set `{insA,insB,insC,delA}` has a `nodup` prefix
`[insA,insB,delA]` after which the remaining op `insC` is neither `applicable`
nor a no-op — its anchor `node1` was rehomed away by the concurrent `delA`.
Hence the conditioned bubble of `ConditionedConvergence.lean` §5 cannot discharge
its `applicable a` / `applicable b` premises for the RGA, and the RGA does not
host through the `interleavingFeasible` oracle as architected. -/
theorem not_interleavingFeasible_RGA : ¬ interleavingFeasible RGACondSig evR := by
  intro h
  have hpre : ∀ x ∈ [insA, insB, delA], x ∈ evR := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Set.mem_insert _ _
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [List.mem_singleton] at hx; subst hx
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have ho : insC ∈ evR :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hnotin : insC ∉ [insA, insB, delA] := by decide
  have hnodup : ([insA, insB, delA] : List (Op app_op_t)).Nodup := by decide
  exact not_appOrNoop_insC (h [insA, insB, delA] insC hpre ho hnotin hnodup)

/-! ## §8  Step 3 — the oracle is too strong: convergence holds anyway

The two natural linearizations of `evR`

    π₁ = [insA, insB, insC, delA]   (insC before delA)
    π₂ = [insA, insB, delA, insC]   (delA before insC — folds insC at the staled state)

CONVERGE, even though π₂ violates `interleavingFeasible` at its last step.  Both
share the prefix `[insA,insB]` (folding to `baseAB`); their tails are the two
sides of `orders_converge`.  This is the crux: `interleavingFeasible` is
sufficient but NOT necessary for RGA convergence. -/

theorem full_enumerations_converge :
    eq (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, insC, delA])
       (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA, insC]) := by
  have h1 : applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, insC, delA]
          = do_ (do_ baseAB insC) delA := rfl
  have h2 : applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA, insC]
          = do_ (do_ baseAB delA) insC := rfl
  rw [h1, h2]; exact orders_converge

/-- **The full verdict, bundled.**  `interleavingFeasible` is FALSE for the RGA
(`.1`), yet the two linearizations of the reachable set — one of which folds the
staled `insC` at the oracle-violating prefix — still converge (`.2`).  So the
`interleavingFeasible`-based bubble does not close the RGA hosting, but the
obstruction is the oracle's excess strength, not a genuine divergence: the RGA's
convergence is carried by the semantic swap at the both-applicable common base
(`orders_converge`), which the current bubble architecture does not exploit. -/
theorem verdict_oracle_false_but_converges :
    (¬ interleavingFeasible RGACondSig evR)
    ∧ eq (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, insC, delA])
         (applySeq RGACondSig.toCRDTSig RGACondSig.init [insA, insB, delA, insC]) :=
  ⟨not_interleavingFeasible_RGA, full_enumerations_converge⟩

/-! ## §9  Axiom audit — kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms rehoming_stales_path
#print axioms orders_converge
#print axioms staled_ins_not_noop
#print axioms staled_ins_not_applicable
#print axioms not_interleavingFeasible_RGA
#print axioms full_enumerations_converge
#print axioms verdict_oracle_false_but_converges

end Sal.Metatheory.RGARehomingGate
