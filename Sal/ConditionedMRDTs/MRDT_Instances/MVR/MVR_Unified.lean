import Sal.ConditionedMRDTs.MRDT_Instances.FlatUnifiedCertificates

/-!
# Conditioned unified certificate for the multi-valued register

The issuer guard is the one-step form of `mvrOK`: the new stamp is fresh and
the overwrite payload is exactly the set of tags visible at the issuer.  The
distributed history deliberately retains existential causal enumerations;
concurrent writes need not, and generally cannot, form one `mvrOK` sequence.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- Public MVR issuer policy: fresh stamp and an exact overwrite snapshot. -/
def mvrApplicable (o : Op MVROp) (s : MVR.State) : Prop :=
  (∀ v, s.1 (o.1, v) = false) ∧
  ∀ w O, o.2.2 = MVROp.write w O →
    ∀ n, n ∈ O ↔ mvrVis s n

/-- The guard is exactly the new-operation clause used by `mvrOK`. -/
theorem mvrApplicable_iff_step (ρ : List (Op MVROp)) (o : Op MVROp) :
    mvrApplicable o (seqFold MVR ρ) ↔
      (∀ v, (seqFold MVR ρ).1 (o.1, v) = false) ∧
      (∀ w O, o.2.2 = MVROp.write w O →
        ∀ n, n ∈ O ↔ mvrVis (seqFold MVR ρ) n) := by
  rfl

/-- Distributed MVR histories retain one causal mint witness per event. -/
def MVRMintHistory (C : Configuration MVR) : Prop :=
  MintHonest MVR mvrApplicable (Configuration.core C)

/-- Existential mint provenance is precisely the history evidence consumed by
the MVR package; no universal-permutation strengthening is hidden here. -/
theorem mvr_history_of_mint (C : Configuration MVR)
    (h : MintHonest MVR mvrApplicable (Configuration.core C)) :
    MVRMintHistory C := h

noncomputable def mvrGeneration : GenerationContract MVR where
  Guard := mvrApplicable
  History := MVRMintHistory
  history_of_mint := mvr_history_of_mint

/-- Independent last-write sequential machine. -/
def mvrSpecMachine : SequentialSpec (Op MVR.AppOp) where
  State := Option ℕ
  init := none
  step := fun _ o => match o.2.2 with | .write v _ => some v

theorem mvrSpecMachine_run (ρ : List (Op MVR.AppOp)) :
    mvrSpecMachine.run ρ = mvrSpecFold ρ := by
  rfl

def mvrRefinement : HistorySequentialRefinement MVR mvrSpecMachine where
  Honest := mvrOK
  Rel s q := ∀ v, mvrView s v ↔ q = some v
  init := by
    intro v
    constructor
    · rintro ⟨n, hn, -⟩
      exact Bool.noConfusion hn
    · intro h
      simp [mvrSpecMachine] at h
  sound := by
    intro ρ hOK v
    rw [mvrSpecMachine_run]
    exact mvr_seq_sound hOK v

def mvrVerified : VerifiedMRDT MVR where
  Honest := fun _ => True
  initInv := trivial
  join := fun C _ => (joinKitAt_plain_iff MVR C).2
    ((join_lemma3_of_cd_feasible MVR_coreVCs3CD MVR_feasibleDeltaVCs3
      MVR_cdVC3) C)
  Spec := mvrSpecMachine
  seq := mvrRefinement

/-- MVR has no additional client invariant beyond its conditioned generation
policy; its observable semantics is supplied by `mvrRefinement`. -/
def mvrSafety : SafetyCertificate MVR mvrGeneration :=
  SafetyCertificate.trivial mvrGeneration

noncomputable def mvrUnified : UnifiedVerifiedMRDT MVR where
  verified := mvrVerified
  generation := mvrGeneration
  history_entails_honest := fun _ _ => True.intro
  safety := mvrSafety

/-! ## SPOT controls -/

-- PASS: the first write is fresh and has nothing to overwrite.
example : mvrApplicable (0, 0, MVROp.write 7 []) MVR.init := by
  simp [mvrApplicable, mvrVis, mvrTag, MVR_init_eq]

-- FAIL: an initial write may not claim a nonexistent visible tag.
example : ¬ mvrApplicable (0, 0, MVROp.write 7 [4]) MVR.init := by
  intro h
  have h4 := (h.2 7 [4] rfl 4).mp (by simp)
  simpa [mvrVis, mvrTag, MVR_init_eq] using h4

-- FAIL: reusing a stamp after a write violates freshness.
example : ¬ mvrApplicable (3, 1, MVROp.write 9 [])
    (MVR.update MVR.init (3, 0, MVROp.write 8 [])) := by
  intro h
  have hf := h.1 8
  simp [MVR_update_eq, mvrUpdate, MVR_init_eq] at hf

#print axioms mvr_history_of_mint
#print axioms mvrRefinement
#print axioms mvrUnified

end Sal.ConditionedMRDTs
