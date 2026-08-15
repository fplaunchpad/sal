import Sal.ConditionedMRDTs.Metatheory.UnifiedVerifiedMRDT
import Sal.ConditionedMRDTs.MRDT_Instances.SeqSpec_Flat

/-!
# Unified certificates for the flat production datatypes

These wrappers expose the already proved unconditional Join results and the
independent sequential models in `SeqSpec_Flat`.  Their generation contract is
deliberately `True`: in particular, this file does **not** promote the
experimental `fwwApplicable` predicate into a production execution guard.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

def flatGeneration (D : ConditionedMRDTSig) : GenerationContract D where
  Guard := fun _ _ => True
  History := fun _ => True
  history_of_mint := fun _ _ => True.intro

def flatVerified {D : ConditionedMRDTSig}
    (hInit : D.Inv D.init) (hJoin : JoinLemma3 D)
    (S : SequentialSpec (Op D.AppOp))
    (R : HistorySequentialRefinement D S) : VerifiedMRDT D where
  Honest := fun _ => True
  initInv := hInit
  join := fun C _ => (joinKitAt_plain_iff D C).2 (hJoin C)
  Spec := S
  seq := R

def flatUnified {D : ConditionedMRDTSig}
    (hInit : D.Inv D.init) (hJoin : JoinLemma3 D)
    (S : SequentialSpec (Op D.AppOp))
    (R : HistorySequentialRefinement D S) : UnifiedVerifiedMRDT D where
  verified := flatVerified hInit hJoin S R
  generation := flatGeneration D
  history_entails_honest := fun _ _ => True.intro
  safety := SafetyCertificate.trivial (flatGeneration D)

def counterSpec : SequentialSpec (Op Counter.AppOp) where
  State := Int
  init := 0
  step n _ := n + 1

def counterRefinement : HistorySequentialRefinement Counter counterSpec where
  Honest := fun _ => True
  Rel := (· = ·)
  init := rfl
  sound := by
    intro ops _
    change seqFold Counter ops = _
    rw [counter_seq_sound]
    induction ops using List.reverseRecOn with
    | nil => rfl
    | append_singleton ops o ih =>
      rw [SequentialSpec.run_append_single, ← ih]
      simp [counterSpec]

def counterUnified : UnifiedVerifiedMRDT Counter :=
  flatUnified trivial Counter_joinLemma3_cd counterSpec counterRefinement

def iocSpec : SequentialSpec (Op IOC.AppOp) where
  State := Int
  init := 0
  step n _ := n + 1

def iocRefinement : HistorySequentialRefinement IOC iocSpec where
  Honest := fun _ => True
  Rel := (· = ·)
  init := rfl
  sound := by
    intro ops _
    change seqFold IOC ops = _
    rw [ioc_seq_sound]
    induction ops using List.reverseRecOn with
    | nil => rfl
    | append_singleton ops o ih =>
      rw [SequentialSpec.run_append_single, ← ih]
      simp [iocSpec]

def iocUnified : UnifiedVerifiedMRDT IOC :=
  flatUnified trivial (join_lemma3_of_cd IOC_coreVCs3 IOC_deltaVCs3
      (cdVC3_of_all_comm IOC_coreVCs3 IOC_all_comm))
    iocSpec iocRefinement

def pnSpecMachine : SequentialSpec (Op PN.AppOp) where
  State := List (Op PN.AppOp)
  init := []
  step q o := q ++ [o]

theorem pnSpecMachine_run (ops : List (Op PN.AppOp)) :
    pnSpecMachine.run ops = ops := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops o ih =>
    rw [SequentialSpec.run_append_single, ih]
    rfl

def pnRefinement : HistorySequentialRefinement PN pnSpecMachine where
  Honest := fun _ => True
  Rel s q := s = pnSpec q
  init := rfl
  sound := by
    intro ops _
    change seqFold PN ops = _
    rw [pn_seq_sound]
    rw [pnSpecMachine_run]

def pnUnified : UnifiedVerifiedMRDT PN :=
  flatUnified trivial (join_lemma3_of_cd PN_coreVCs3 PN_deltaVCs3
      (cdVC3_of_all_comm PN_coreVCs3 PN_all_comm))
    pnSpecMachine pnRefinement

def orsetSpec : SequentialSpec (Op ORSet.AppOp) where
  State := ℕ → Bool
  init := fun _ => false
  step := orSpecStep

def orsetRefinement : HistorySequentialRefinement ORSet orsetSpec where
  Honest := fun _ => True
  Rel s q := ∀ e, orView s e ↔ q e = true
  init := by intro e; simp [orView, orsetSpec, ORSet_init_eq]
  sound := by
    intro ops _ e
    simpa [orsetSpec, SequentialSpec.run, orSpecFold] using orset_seq_sound ops e

def orsetUnified : UnifiedVerifiedMRDT ORSet :=
  flatUnified trivial ORSet_joinLemma3 orsetSpec orsetRefinement

def orseteSpec : SequentialSpec (Op ORSetE.AppOp) where
  State := ℕ → Bool
  init := fun _ => false
  step := orSpecStep

def orseteRefinement : HistorySequentialRefinement ORSetE orseteSpec where
  Honest := fun _ => True
  Rel s q := ∀ e, orEView s e ↔ q e = true
  init := by intro e; simp [orEView, orseteSpec]; intro x y; rfl
  sound := by
    intro ops _ e
    simpa [orseteSpec, SequentialSpec.run, orSpecFold] using orsete_seq_sound ops e

def orseteUnified : UnifiedVerifiedMRDT ORSetE :=
  flatUnified trivial ORSetE_joinLemma3 orseteSpec orseteRefinement

def ewflagSpec : SequentialSpec (Op EWFlag.AppOp) where
  State := Bool
  init := false
  step := ewSpecStep

def ewflagRefinement : HistorySequentialRefinement EWFlag ewflagSpec where
  Honest := fun _ => True
  Rel s q := ewView s ↔ q = true
  init := by simp [ewView, ewflagSpec, EWFlag_init_eq]
  sound := by
    intro ops _
    simpa [ewflagSpec, SequentialSpec.run, ewSpecFold] using ewflag_seq_sound ops

/-- EWFlag stays on the full-closure doctrine. No `JoinLemma3F → JoinLemma3`
converse is assumed. -/
def ewflagVerifiedF : VerifiedMRDTF EWFlag where
  initInv := trivial
  joinF := EWFlag_joinLemma3F
  Spec := ewflagSpec
  seq := ewflagRefinement

def ewflagUnifiedF : UnifiedVerifiedMRDTF EWFlag where
  verified := ewflagVerifiedF
  generation := flatGeneration EWFlag
  safety := SafetyCertificate.trivial (flatGeneration EWFlag)

def gosetSpec : SequentialSpec (Op GOSet.AppOp) where
  State := List (Op GOSet.AppOp)
  init := []
  step q o := q ++ [o]

def gosetRefinement : HistorySequentialRefinement GOSet gosetSpec where
  Honest := fun _ => True
  Rel := fun s (q : List (Op GOSet.AppOp)) => ∀ x, s x = true ↔
    ∃ o : Op GOSet.AppOp, o ∈ q ∧ o.2.2 = x
  init := by simp [GOSet, gosetSpec]
  sound := by
    intro ops _ x
    have hr : gosetSpec.run ops = ops := by
      induction ops using List.reverseRecOn with
      | nil => rfl
      | append_singleton ops o ih =>
        rw [SequentialSpec.run_append_single, ih]
        rfl
    rw [hr]
    exact goset_seq_sound ops x

def gosetUnified : UnifiedVerifiedMRDT GOSet :=
  flatUnified trivial (join_lemma3_of_cd GOSet_coreVCs3 GOSet_deltaVCs3
      (cdVC3_of_all_comm GOSet_coreVCs3 GOSet_all_comm))
    gosetSpec gosetRefinement

def gomapSpec : SequentialSpec (Op GOMap.AppOp) where
  State := List (Op GOMap.AppOp)
  init := []
  step q o := q ++ [o]

def gomapRefinement : HistorySequentialRefinement GOMap gomapSpec where
  Honest := fun _ => True
  Rel := fun s (q : List (Op GOMap.AppOp)) => ∀ p, s p = true ↔
    ∃ o : Op GOMap.AppOp, o ∈ q ∧ o.2.2 = p
  init := by simp [GOMap, gomapSpec]
  sound := by
    intro ops _ p
    have hr : gomapSpec.run ops = ops := by
      induction ops using List.reverseRecOn with
      | nil => rfl
      | append_singleton ops o ih =>
        rw [SequentialSpec.run_append_single, ih]
        rfl
    rw [hr]
    exact gomap_seq_sound ops p

def gomapUnified : UnifiedVerifiedMRDT GOMap :=
  flatUnified trivial (join_lemma3_of_cd GOMap_coreVCs3 GOMap_deltaVCs3
      (cdVC3_of_all_comm GOMap_coreVCs3 GOMap_all_comm))
    gomapSpec gomapRefinement

def lwwSpecMachine : SequentialSpec (Op LWW.AppOp) where
  State := Option ℕ
  init := none
  step := fun _ o => some (lwwVal o)

def lwwRefinement : HistorySequentialRefinement LWW lwwSpecMachine where
  Honest := stampsMono
  Rel s q := lwwView (lwwSt s) = q
  init := rfl
  sound := by
    intro ops h
    simpa [lwwSpecMachine, SequentialSpec.run, lwwSpecFold] using lww_seq_sound ops h

def lwwUnified : UnifiedVerifiedMRDT LWW :=
  flatUnified trivial (join_lemma3_of_cd LWW_coreVCs3 LWW_deltaVCs3
      (cdVC3_of_all_comm LWW_coreVCs3 LWW_all_comm))
    lwwSpecMachine lwwRefinement

def fwwSpecMachine : SequentialSpec (Op FWW.AppOp) where
  State := Option (ℕ × ℕ)
  init := none
  step q o := match q with | none => some (o.1, fwwVal o) | some p => some p

def fwwRefinement : HistorySequentialRefinement FWW fwwSpecMachine where
  Honest := stampsMono
  Rel s q := fwwView (fwwSt s) = q
  init := rfl
  sound := by
    intro ops h
    simpa [fwwSpecMachine, SequentialSpec.run, fwwSpecFold] using fww_seq_sound ops h

/-- Uses the unconditional production semantics; `fwwApplicable` remains
staged and is intentionally absent from this certificate. -/
def fwwUnified : UnifiedVerifiedMRDT FWW :=
  flatUnified trivial (join_lemma3_of_cd FWW_coreVCs3 FWW_deltaVCs3
      (cdVC3_of_all_comm FWW_coreVCs3 FWW_all_comm))
    fwwSpecMachine fwwRefinement

def awpqSpecMachine : SequentialSpec (Op AWPQ.AppOp) where
  State := (ℕ → Bool) × List (Op AWPQ.AppOp)
  init := (fun _ => false, [])
  step q o := (awpqSpecStep q.1 o, q.2 ++ [o])

theorem awpqSpecMachine_run (ops : List (Op AWPQ.AppOp)) :
    awpqSpecMachine.run ops = (awpqSpecFold ops, ops) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops o ih =>
    rw [SequentialSpec.run_append_single, ih, awpqSpecFold_snoc]
    rfl

def awpqRefinement : HistorySequentialRefinement AWPQ awpqSpecMachine where
  Honest := fun _ => True
  Rel s q :=
    (∀ e, awpqMemView s e ↔ q.1 e = true) ∧
    (∀ t e a, s.2 (t, e, a) = true ↔
      ∃ o ∈ q.2, o.2.2 = AWPQOp.inc e a ∧ o.1 = t)
  init := by simp [awpqMemView, awpqSpecMachine, AWPQ_init_eq]
  sound := by
    intro ops _
    rw [awpqSpecMachine_run]
    exact ⟨awpq_mem_seq_sound ops, awpq_inc_log_sound ops⟩

def awpqUnified : UnifiedVerifiedMRDT AWPQ :=
  flatUnified trivial
    (join_lemma3_of_cd_feasible AWPQ_coreVCs3CD AWPQ_feasibleDeltaVCs3 AWPQ_cdVC3)
    awpqSpecMachine awpqRefinement

#print axioms orsetUnified
#print axioms fwwUnified
#print axioms awpqUnified
#print axioms ewflagUnifiedF

end Sal.ConditionedMRDTs
