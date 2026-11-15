import LeanProofs.Implementations.DisableWinsFlag.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The flag core: clause 2

The specification is a single Boolean. A `winning` sets it and a `reset`
clears it, read through `true`. Nothing about replicas or counters survives
the abstraction, which is why the sequential premise is the unrestricted
`SpecSound` rather than the execution-scoped one.

The implementation's `active` reads the physical state, and `active_foldl`
says that after a replay it depends only on the last event in that replay.
That is what matches the specification's single Boolean.
-/

namespace LeanProofs.Implementations.DisableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

/-- How one request moves the physical bit. -/
def flagStep (_ : Bool) (o : AppOp) : Bool :=
  match o with
  | .winning => true
  | .reset => false

/-- How one request moves the client Boolean. -/
def boolStep (invert : Bool) (_ : Bool) (o : AppOp) : Bool :=
  match o with
  | .reset => invert
  | .winning => !invert

/-- The client reading of the physical bit. -/
theorem machine_fold (invert : Bool) (ops : List AppOp) (b : Bool) :
    ops.foldl (boolStep invert) (if invert then !b else b)
      = if invert then !(ops.foldl flagStep b) else ops.foldl flagStep b := by
  induction ops generalizing b with
  | nil => rfl
  | cons o ops ih =>
      cases o with
      | winning =>
          have hb : boolStep invert (if invert then !b else b) AppOp.winning
              = if invert then !(flagStep b AppOp.winning) else flagStep b AppOp.winning := by
            cases invert <;> simp [boolStep, flagStep]
          rw [List.foldl_cons, List.foldl_cons, hb, ih]
      | reset =>
          have hb : boolStep invert (if invert then !b else b) AppOp.reset
              = if invert then !(flagStep b AppOp.reset) else flagStep b AppOp.reset := by
            cases invert <;> simp [boolStep, flagStep]
          rw [List.foldl_cons, List.foldl_cons, hb, ih]

/-- After a replay the physical reading depends only on the last request. -/
theorem active_foldl (pi : List (Event)) :
    active (pi.foldl step (fun _ => (0, true)))
      = (pi.map Op.op).foldl flagStep true := by
  induction pi using List.reverseRecOn with
  | nil => simp [active]
  | append_singleton pi e ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
        List.foldl_append]
      cases he : e.op with
      | winning =>
          have hact : active (step (pi.foldl step (fun _ => (0, true))) e) = true := by
            rw [active]
            simp only [decide_eq_true_eq]
            exact ⟨e.rep, by simp [step, he]⟩
          rw [hact]
          simp [flagStep, he]
      | reset =>
          have hact : active (step (pi.foldl step (fun _ => (0, true))) e) = false := by
            rw [active]
            simp [step, he]
          rw [hact]
          simp [flagStep, he]

/-- `Spec`: one Boolean, set by `winning` and cleared by `reset`, read
directly or negated according to `true`. -/
def specMachine :
    DeterministicSpec type.OType type.QType type.ValType where
  State := Bool
  initial := if true then !true else true
  update := boolStep true
  query b _ := b

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type :=
  specMachine.toSpec

/-- The sequential premise, in its unrestricted form: every replay of the
implementation is explained by the one-Boolean language. -/
theorem specSound :
    Soundness.SpecSound D historySpec := by
  intro pi q
  have hlabels : projectedUpdates (D := D.toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, specMachine.updates_query_iff]
  show (if true then !active (pi.foldl step (fun _ => (0, true)))
      else active (pi.foldl step (fun _ => (0, true)))) = _
  rw [active_foldl]
  exact (machine_fold true (pi.map Op.op) true).symm

end LeanProofs.Implementations.DisableWinsFlag
