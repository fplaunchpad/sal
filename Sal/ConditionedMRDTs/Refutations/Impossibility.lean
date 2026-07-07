import Sal.ConditionedMRDTs.MRDT_Instances.MRDT_Instances
/-!
# Impossibility and separation results (FINDINGS, not junk)

The machine-checked boundary of the theory — each theorem here forced a
design decision recorded in `MRDT_METATHEORY_DRAFT.md`:

* `Counter_binary_lem_0op_false` (T4) — the LCA argument is load-bearing:
  the Counter satisfies the ternary 0-OP law but refutes the binary one, so
  the ternary theory strictly exceeds the binary one;
* `*_local_redistribute_false` (T9.2) — all three production MRDTs refute
  the *unconditional* delta contract: unconditional = group ⊕ lattice
  exactly, real LCA-sensitive MRDTs are strictly feasible-class;
* `ORSet_merge_peel_comm3_false`, `EWFlag_mergeL_init_false` (T9.3) — even
  the 0-OP and unit laws are feasibility-bounded, forcing the slim
  `CoreVCs3CD` core;
* `ORSetE_rc_non_comm_directional_false` (T10.2) — the forcing corner for
  the `differentReplicas` guard (= the F* artifact's own interface form);
* the classification facts (`*_not_all_comm`, `*_lca_sensitive`) placing
  each production mirror as LCA-sensitive and non-commuting.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §4. Classification: LCA-sensitive, non-commuting -/

/-- OR-Set: same-element Add/Rem do not commute (rem-then-add keeps the tag,
add-then-rem loses it). -/
theorem ORSet_not_all_comm :
    ¬ ∀ a b : Op ORSet.AppOp, ORSet.toCRDTSig.commutes a b := by
  intro h
  have h0 := congrFun (h (0, 0, ORSetOp.add 0) (1, 0, ORSetOp.rem 0)
    (fun _ => false)) (0, 0)
  simp [ORSet_update_eq, orUpdate] at h0

/-- OR-Set-efficient: same witness. -/
theorem ORSetE_not_all_comm :
    ¬ ∀ a b : Op ORSetE.AppOp, ORSetE.toCRDTSig.commutes a b := by
  intro h
  have h0 := congrFun (h (0, 0, ORSetOp.add 0) (1, 0, ORSetOp.rem 0)
    (fun _ => false)) (0, 0, 0)
  simp [ORSetE_update_eq, orEUpdate] at h0

/-- Enable-wins: Enable/Disable do not commute (the flag differs). -/
theorem EWFlag_not_all_comm :
    ¬ ∀ a b : Op EWFlag.AppOp, EWFlag.toCRDTSig.commutes a b := by
  intro h
  have h0 := congrFun (h (0, 0, EWOp.enable) (1, 0, EWOp.disable)
    (fun _ => ((0 : ℕ), false))) 0
  simp [EWFlag_update_eq, ewUpdate] at h0

/-- OR-Set: the merge reads its LCA argument (retraction!): with the tag in
`l ∩ a` but not `b`, the LCA decides between "kept" and "removed". -/
theorem ORSet_lca_sensitive :
    ∃ l l' a b : ORSet.State,
      ORSet.mergeL l a b ≠ ORSet.mergeL l' a b := by
  refine ⟨fun t => decide (t = (0, 0)), fun _ => false,
    fun t => decide (t = (0, 0)), fun _ => false, ?_⟩
  intro h
  have h0 := congrFun h (0, 0)
  simp [ORSet_mergeL_eq, orMergeL] at h0

/-- OR-Set-efficient: same witness. -/
theorem ORSetE_lca_sensitive :
    ∃ l l' a b : ORSetE.State,
      ORSetE.mergeL l a b ≠ ORSetE.mergeL l' a b := by
  refine ⟨fun t => decide (t = (0, 0, 0)), fun _ => false,
    fun t => decide (t = (0, 0, 0)), fun _ => false, ?_⟩
  intro h
  have h0 := congrFun h (0, 0, 0)
  simp [ORSetE_mergeL_eq, orEMergeL] at h0

/-- Enable-wins: the counter merge `a + b − l` reads the LCA. -/
theorem EWFlag_lca_sensitive :
    ∃ l l' a b : EWFlag.State,
      EWFlag.mergeL l a b ≠ EWFlag.mergeL l' a b := by
  refine ⟨fun _ => ((1 : ℕ), false), fun _ => ((0 : ℕ), false),
    fun _ => ((1 : ℕ), false), fun _ => ((1 : ℕ), false), ?_⟩
  intro h
  have h0 := congrFun h 0
  simp [EWFlag_mergeL_eq, ewMergeCF] at h0

/-! ## §5. Class placement: all three falsify the unconditional contracts

The witnesses are the T8.6 infeasible tuples, now against the real
definitions: an element (tag) sitting in `c ∩ l` only, or a flag set with a
zero counter — states no execution produces. -/

/-- **OR-Set falsifies unconditional `local_redistribute`** (T8.6 witness:
tag in `c ∩ l` only — the LHS drops it, the RHS keeps it). The production
OR-Set is therefore NOT in the group ⊕ lattice classes: it needs the
feasible-tuple contract. -/
theorem ORSet_local_redistribute_false :
    ¬ ∀ l m x c y : ORSet.State,
        ORSet.mergeL l (ORSet.mergeL m x c) y
          = ORSet.mergeL m (ORSet.mergeL l x y) c := by
  intro h
  have h0 := congrFun (h (fun t => decide (t = (0, 0))) (fun _ => false)
    (fun _ => false) (fun t => decide (t = (0, 0))) (fun _ => false)) (0, 0)
  simp [ORSet_mergeL_eq, orMergeL] at h0

/-- OR-Set-efficient: same. -/
theorem ORSetE_local_redistribute_false :
    ¬ ∀ l m x c y : ORSetE.State,
        ORSetE.mergeL l (ORSetE.mergeL m x c) y
          = ORSetE.mergeL m (ORSetE.mergeL l x y) c := by
  intro h
  have h0 := congrFun (h (fun t => decide (t = (0, 0, 0))) (fun _ => false)
    (fun _ => false) (fun t => decide (t = (0, 0, 0))) (fun _ => false))
    (0, 0, 0)
  simp [ORSetE_mergeL_eq, orEMergeL] at h0

/-- **Enable-wins falsifies unconditional `local_redistribute`** (a middle
LCA with an inflated counter suppresses a genuine enable on one side of the
re-association but not the other). -/
theorem EWFlag_local_redistribute_false :
    ¬ ∀ l m x c y : EWFlag.State,
        EWFlag.mergeL l (EWFlag.mergeL m x c) y
          = EWFlag.mergeL m (EWFlag.mergeL l x y) c := by
  intro h
  have h0 := congrFun (h (fun _ => ((0 : ℕ), false))
    (fun _ => ((100 : ℕ), false)) (fun _ => ((0 : ℕ), false))
    (fun _ => ((0 : ℕ), false)) (fun _ => ((1 : ℕ), true))) 0
  simp [EWFlag_mergeL_eq, ewMergeCF] at h0

/-- **OR-Set falsifies `CoreVCs3.merge_peel_comm3`** — when the LCA fold
already contains the peeled add's tag (infeasible: timestamps are fresh in
executions). This is why the feasible route runs on the slim `CoreVCs3CD`:
even the 0-OP-shaped laws of `CoreVCs3` are feasibility-bounded for tagged
RDTs. -/
theorem ORSet_merge_peel_comm3_false :
    ¬ ∀ (a : ORSet.State) (e : Op ORSet.AppOp)
        (π₀ π₂ : List (Op ORSet.AppOp)),
        (∀ x ∈ π₀, ORSet.toCRDTSig.commutes e x) →
        (∀ x ∈ π₂, ORSet.toCRDTSig.commutes e x) →
        ORSet.mergeL (applySeq ORSet.toCRDTSig ORSet.init π₀)
            (ORSet.update a e) (applySeq ORSet.toCRDTSig ORSet.init π₂)
          = ORSet.update (ORSet.mergeL (applySeq ORSet.toCRDTSig ORSet.init π₀)
              a (applySeq ORSet.toCRDTSig ORSet.init π₂)) e := by
  intro h
  have hcomm : ORSet.toCRDTSig.commutes (0, 0, ORSetOp.add 0)
      (0, 0, ORSetOp.add 0) := fun _ => rfl
  have h0 := congrFun (h ORSet.init (0, 0, ORSetOp.add 0)
    [(0, 0, ORSetOp.add 0)] []
    (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hcomm)
    (fun x hx => absurd hx List.not_mem_nil)) (0, 0)
  simp [applySeq, ORSet_update_eq, ORSet_mergeL_eq, ORSet_init_eq,
    orUpdate, orMergeL] at h0

/-- **Enable-wins falsifies `CoreVCs3.mergeL_init`** — on the infeasible
state "flag set, counter zero" (every reachable set flag has a positive
counter). The unit law itself is feasibility-bounded; hence
`FeasibleDeltaVCs3.feasible_init`. -/
theorem EWFlag_mergeL_init_false :
    ¬ ∀ s : EWFlag.State, EWFlag.mergeL EWFlag.init EWFlag.init s = s := by
  intro h
  have h0 := congrFun (h (fun _ => ((0 : ℕ), true))) 0
  simp [EWFlag_mergeL_eq, EWFlag_init_eq, ewMergeCF] at h0

/-- **The separation: the binary `lem_0op` is FALSE for the counter** — so the
counter, although all-commuting, cannot instantiate the 2-way `CoreVCs`, and the
binary metatheorem cannot host it. Ternary-ness (the LCA argument in `lem_0op3`)
is load-bearing, not an inert third argument. -/
theorem Counter_binary_lem_0op_false :
    ¬ ∀ (a b : Counter.State) (e : Op Counter.AppOp),
        Counter.toCRDTSig.merge (Counter.update a e) (Counter.update b e)
          = Counter.update (Counter.toCRDTSig.merge a b) e := by
  intro h
  -- `Counter.State` unfolds to `Int`, so the instance is accepted definitionally.
  have h00 : ((0 : Int) + 1) + ((0 : Int) + 1) = ((0 : Int) + (0 : Int)) + 1 :=
    h (0 : Int) (0 : Int) (0, 0, ())
  omega

/-- **The forcing corner**: the unguarded field is FALSE for ORSetE. -/
theorem ORSetE_rc_non_comm_directional_false :
    ¬ (∀ o₁ o₂ : Op ORSetE.AppOp,
        distinctOps o₁ o₂ →
        (¬ ORSetE.toCRDTSig.commutes o₁ o₂ ↔
         (ORSetE.toCRDTSig.rc o₁ o₂ = RcRes.Fst_then_snd ∨
          ORSetE.toCRDTSig.rc o₂ o₁ = RcRes.Fst_then_snd))) := by
  intro h
  have hd : distinctOps (D := ORSetE.toCRDTSig)
      (0, 0, ORSetOp.add 0) (1, 0, ORSetOp.add 0) :=
    Nat.zero_ne_one
  rcases (h _ _ hd).mp (ORSetE_ncomm_add_add_same 0 1 0 0 Nat.zero_ne_one)
    with hr | hr
  · exact RcRes.noConfusion (show RcRes.Either = _ from hr)
  · exact RcRes.noConfusion (show RcRes.Either = _ from hr)


end Sal.ConditionedMRDTs
