import Sal.ConditionedMRDTs.Metatheory.VC_Minimal_Core

/-!
# The nullary unit `VC5°` is an INDEPENDENT rule

The nullary unit law `mergeL σ₀ σ₀ σ₀ = σ₀` (`FeasibleInitAtEmpty`, the
`feasible_init` instance at `ev = ∅`) is NOT derivable from the other seven
verification conditions. The **poisoned-empty-merge G-set** `GSetPoison` satisfies
`CoreVCs3CD` (VC1–VC4), `FeasibleLocalRedistributeVC` (VC6),
`FeasibleRedistributeVC` (VC7) and `CDVC3` (VC8), yet its merge of two fresh
replicas is not a canonical state, so it is not RA-linearizable
(`GSetPoison_not_joinLemma3`). The single failing condition is `VC5°`.

## The datatype

* **Σ = `Bool`**, `init = false`; one op kind (`AppOp = Unit`, "set") with
  `do = const true`; `rc = Either` everywhere.
* **merge** `mergeL l a b = (a ∨ b) ∨ (¬l ∧ ¬a ∧ ¬b)`: the G-set union
  `a ∨ b`, EXCEPT the LCA-and-both-branches-empty cell `(false,false,false)`
  is poisoned to `true`.

## Why every other condition is green (hand-derivation)

The only op writes `true`, so the delta `u = do(B,e) = true` at *every*
`CDVC3`/`VC6`/`VC7` slot. `u = true` misses the poisoned cell entirely: every
`mergeL · · true` reads `_ ∨ true = true`, and `mergeL · true ·` reads
`true ∨ _ = true`, so those three laws collapse to `true = true` for *all*
`Bool` inputs (`gp_cd_id`, `gp_redis_id`, `gp_lredis_id`, each `by decide`).
VC1–VC3 are vacuous (one commuting kind, `rc = Either`); VC4 is the symmetry
of the merge table. Only `VC5°` (`mergeL false false false`) hits the poison:
`mergeL σ₀ σ₀ σ₀ = true ≠ false = σ₀`.

## The countermodel (the two-fresh-replica merge)

`JoinLemma3` at `ev₁ = ev₂ = ∅`, all canonical states `= σ₀ = false`, demands
`mergeL σ₀ σ₀ σ₀` be the canonical state of `∅`, i.e. `σ₀ = false`; but it is
`true`. This is the minimal non-RA-linearizable witness: the merge of two
replicas that have seen nothing produces a state no fold of the empty event
set attains.
-/

namespace Sal.ConditionedMRDTs.FeasibleInitNotDerivableAtEmpty

open Sal.Emulation

/-! ## §1. The poisoned-empty-merge G-set -/

/-- The poisoned merge table: G-set union, with the all-empty cell poisoned. -/
def gpMergeL (l a b : Bool) : Bool := (a || b) || (!l && !a && !b)

/-- **The poisoned-empty-merge G-set.** State `Bool`, `init = false`, one op
kind writing `true`, `rc = Either`, merge `gpMergeL`. -/
def GSetPoison : ConditionedMRDTSig where
  toMRDTSig :=
    { State := Bool
      dec_state := inferInstance
      init := false
      AppOp := Unit
      dec_op := inferInstance
      Query := Unit
      Value := Bool
      update := fun _ _ => true
      merge := fun a b => gpMergeL false a b
      query := fun s _ => s
      rc := fun _ _ => RcRes.Either
      mergeL := gpMergeL
      merge_init_slice := fun _ _ => rfl }
  Inv := fun _ => True
  applicable := fun _ _ => True

@[simp] theorem GSetPoison_mergeL (l a b : Bool) :
    GSetPoison.mergeL l a b = gpMergeL l a b := rfl
@[simp] theorem GSetPoison_update (s : Bool) (e : Op Unit) :
    GSetPoison.update s e = true := rfl
@[simp] theorem GSetPoison_init : GSetPoison.init = false := rfl
@[simp] theorem GSetPoison_rc (o₁ o₂ : Op Unit) :
    GSetPoison.rc o₁ o₂ = RcRes.Either := rfl

/-- Every pair of events commutes: `do` is the constant `true`. -/
theorem GSetPoison_commutes (o₁ o₂ : Op GSetPoison.AppOp) :
    GSetPoison.toCRDTSig.commutes o₁ o₂ := fun _ => rfl

/-- `rc` is never `Fst_then_snd`. -/
theorem GSetPoison_rc_ne (o₁ o₂ : Op GSetPoison.AppOp) :
    GSetPoison.rc o₁ o₂ ≠ RcRes.Fst_then_snd := by
  rw [GSetPoison_rc]; exact fun h => RcRes.noConfusion h

/-! ### The delta-dodges-the-poison Bool identities (`by decide`) -/

/-- VC8's cell: `mergeL B A true = true` for all `A B`. -/
theorem gp_cd_id : ∀ A B : Bool, gpMergeL B A true = true := by decide
/-- VC7's identity with the delta `u = true`. -/
theorem gp_redis_id : ∀ B t₀ t₁ t₂ : Bool,
    gpMergeL (gpMergeL B t₀ true) (gpMergeL B t₁ true) (gpMergeL B t₂ true)
      = gpMergeL B (gpMergeL t₀ t₁ t₂) true := by decide
/-- VC6's identity with the delta `u = true`. -/
theorem gp_lredis_id : ∀ s₀ B t₁ s₂ : Bool,
    gpMergeL s₀ (gpMergeL B t₁ true) s₂ = gpMergeL B (gpMergeL s₀ t₁ s₂) true := by
  decide
/-- VC4: merge symmetry. -/
theorem gp_comm_id : ∀ l a b : Bool, gpMergeL l a b = gpMergeL l b a := by decide

/-! ## §2. The seven green conditions

VC1–VC3 (the update layer): vacuous, every pair commutes and `rc = Either`. -/

theorem GSetPoison_updateVCs : UpdateVCs GSetPoison.toCRDTSig where
  rc_non_comm_directional := fun o₁ o₂ _ _ =>
    ⟨fun hnc => absurd (GSetPoison_commutes o₁ o₂) hnc,
     fun h => h.elim (fun hd => absurd hd (GSetPoison_rc_ne o₁ o₂))
                     (fun hd => absurd hd (GSetPoison_rc_ne o₂ o₁))⟩
  no_rc_chain := fun o₁ o₂ _ _ _ h => GSetPoison_rc_ne o₁ o₂ h.1
  cond_comm_lift := fun _ e e' _ _ _ _ _ hrc _ => absurd hrc (GSetPoison_rc_ne e e')

/-- VC4: merge symmetry. -/
theorem GSetPoison_mergeL_comm (l a b : GSetPoison.State) :
    GSetPoison.mergeL l a b = GSetPoison.mergeL l b a := gp_comm_id l a b

/-- The slim core (VC1–VC4). -/
theorem GSetPoison_coreVCs3CD : CoreVCs3CD GSetPoison where
  update_core := GSetPoison_updateVCs
  mergeL_comm := GSetPoison_mergeL_comm

/-- **VC8 (CDVC3) is green.** The delta `do B e = true` dodges the poison:
`mergeL B A true = true = do A e` for every `A B : Bool`. -/
theorem GSetPoison_cdVC3 : CDVC3 GSetPoison := by
  intro C U A B e _ _ _ _ _ _ _ _
  simp only [GSetPoison_mergeL, GSetPoison_update]
  exact gp_cd_id A B

/-- **VC7 (feasible_redistribute) is green.** Every inner `mergeL B tᵢ true`
saturates to `true`; both sides collapse to `true`. -/
theorem GSetPoison_feasibleRedistribute :
    FeasibleRedistributeVC GSetPoison := by
  intro C ev₁ ev₂ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [GSetPoison_mergeL, GSetPoison_update]
  exact gp_redis_id B t₀ t₁ t₂

/-- **VC6 (feasible_local_redistribute) is green.** Same collapse: `u = true`
saturates the inner and outer merges away from the poison. -/
theorem GSetPoison_feasibleLocalRedistribute :
    FeasibleLocalRedistributeVC GSetPoison := by
  intro C ev₁ ev₂ s₀ B t₁ s₂ e _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [GSetPoison_mergeL, GSetPoison_update]
  exact gp_lredis_id s₀ B t₁ s₂

/-! ## §3. The single failing condition: `VC5°`

`mergeL σ₀ σ₀ σ₀ = mergeL false false false` hits the poisoned cell. -/

/-- **`VC5°` fails** (hand-derived value `true ≠ false`): the poisoned cell. -/
theorem GSetPoison_not_feasibleInitAtEmpty :
    ¬ FeasibleInitAtEmpty GSetPoison := by
  intro h
  unfold FeasibleInitAtEmpty at h
  rw [GSetPoison_mergeL, GSetPoison_init] at h
  simp [gpMergeL] at h

/-- And so the full `feasible_init` field fails a fortiori. -/
theorem GSetPoison_not_feasibleInitVC : ¬ FeasibleInitVC GSetPoison :=
  fun h => GSetPoison_not_feasibleInitAtEmpty h.atEmpty

/-! ### SPOT pins (PASS + FAIL) -/

/-- PASS: away from the poison, the merge is the ordinary G-set union. -/
example : GSetPoison.mergeL false false true = true := rfl
/-- PASS: `mergeL · · true` is constantly `true` (delta dodges the poison). -/
example : GSetPoison.mergeL true false true = true := rfl
/-- FAIL: the poisoned cell, `VC5°`'s left side is `true`, not `σ₀ = false`. -/
example : GSetPoison.mergeL false false false = true := rfl
example : GSetPoison.mergeL GSetPoison.init GSetPoison.init GSetPoison.init
    ≠ GSetPoison.init := by simp [GSetPoison_mergeL, GSetPoison_init, gpMergeL]

/-! ## §4. Non-RA-linearizability: the two-fresh-replica merge -/

/-- `initConfig`'s visibility is empty. -/
theorem initConfig_vis_False {D' : CRDTSig} (a b : Op D'.AppOp) :
    ¬ (Sal.Emulation.initConfig D').vis a b := fun h => h

/-- **The Join fails at `ev₁ = ev₂ = ∅`.** `mergeL σ₀ σ₀ σ₀ = true` is no
canonical state of the empty event set (whose only canonical state is
`σ₀ = false`). -/
theorem GSetPoison_not_joinLemma3 : ¬ JoinLemma3 GSetPoison := by
  intro h
  have hcan := h (Sal.Emulation.initConfig GSetPoison.toCRDTSig) ∅ ∅
    GSetPoison.init GSetPoison.init GSetPoison.init
    (fun hab _ => absurd hab (initConfig_vis_False _ _))
    (fun a => initConfig_vis_False a a)
    (fun a ha => absurd ha (Set.notMem_empty a))
    (fun a ha => absurd ha (Set.notMem_empty a))
    (fun _ _ _ _ hb => absurd hb (Set.notMem_empty _))
    (fun _ _ _ _ hb => absurd hb (Set.notMem_empty _))
    (by rw [Set.empty_inter]; exact isCanonicalState_empty_init _)
    (isCanonicalState_empty_init _) (isCanonicalState_empty_init _)
  rw [Set.empty_union] at hcan
  have heq := isCanonicalState_empty rfl hcan
  rw [GSetPoison_mergeL, GSetPoison_init] at heq
  simp [gpMergeL] at heq

/-! ## §5. The independence result -/

/-- **`VC5°` is an independent VC.** There is a `ConditionedMRDTSig` satisfying
`CoreVCs3CD` (VC1–VC4), `FeasibleLocalRedistributeVC` (VC6),
`FeasibleRedistributeVC` (VC7) and `CDVC3` (VC8), whose nullary unit law fails
and which is not RA-linearizable (the Join fails). Hence the flat set cannot be
reduced by dropping the empty-set instance of `feasible_init`. -/
theorem feasible_init_not_derivable_at_empty :
    ∃ D : ConditionedMRDTSig,
      CoreVCs3CD D ∧ FeasibleLocalRedistributeVC D ∧
      FeasibleRedistributeVC D ∧ CDVC3 D ∧
      ¬ FeasibleInitAtEmpty D ∧ ¬ JoinLemma3 D :=
  ⟨GSetPoison, GSetPoison_coreVCs3CD, GSetPoison_feasibleLocalRedistribute,
   GSetPoison_feasibleRedistribute, GSetPoison_cdVC3,
   GSetPoison_not_feasibleInitAtEmpty, GSetPoison_not_joinLemma3⟩

#print axioms feasible_init_not_derivable_at_empty

end Sal.ConditionedMRDTs.FeasibleInitNotDerivableAtEmpty
