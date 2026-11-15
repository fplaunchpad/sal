import LeanProofs.Implementations.EfficientORSet.Definition
import Artifact.MRDTs.Metatheory.Correctness

/-!
# The efficient OR-set: clause 2

The ordinary-set specification of Appendix `app:dt-or-set`, the abstraction
function of Section 6, and sequential correctness. The abstraction is
`elements`, which erases the replica and timestamp from every record, so a
state with one record per replica per element reads as a plain set.

Nothing here mentions `merge`, `vis` or the replay order.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs

open Artifact.MRDTs.Foundation
open Classical
variable {α : Type} [DecidableEq α]

def abstractAction : AppOp α → Paper1.NaturalSetSpec.Action α
  | .add x => .add x
  | .remove x => .remove x

@[simp] theorem abstractAction_add (x : α) : abstractAction (.add x) = .add x := rfl
@[simp] theorem abstractAction_remove (x : α) : abstractAction (.remove x) = .remove x := rfl

def setStep (s : Finset α) (e : Event α) : Finset α :=
  Paper1.NaturalSetSpec.step s (abstractAction e.2.2)

def spec : SequentialSpec (D α) where
  State := Finset α
  init := ∅
  step := setStep
  Legal _ := True
  query s x := decide (x ∈ s)

def stateRel (s : State α) (q : Finset α) : Prop := elements s = q

theorem elements_update (s : State α) (e : Event α) :
    elements (update s e) = setStep (elements s) e := by
  rcases e with ⟨t, r, op⟩
  cases op with
  | add x =>
    ext y
    simp only [elements, update, setStep, abstractAction, Paper1.NaturalSetSpec.step, Finset.mem_image, Finset.mem_insert,
      Finset.mem_filter]
    constructor
    · rintro ⟨p, hp | hp, hpy⟩
      · subst p; exact Or.inl hpy.symm
      · exact Or.inr ⟨p, hp.1, hpy⟩
    · rintro (h | ⟨p, hp, hpy⟩)
      · exact ⟨(r,t,x), Or.inl rfl, h.symm⟩
      · by_cases hy : y = x
        · exact ⟨(r,t,x), Or.inl rfl, hy.symm⟩
        · exact ⟨p, Or.inr ⟨hp, fun h => hy (hpy.symm.trans h.2)⟩, hpy⟩
  | remove x =>
    ext y
    simp only [elements, update, setStep, abstractAction, Paper1.NaturalSetSpec.step, Finset.mem_image, Finset.mem_filter,
      Finset.mem_erase]
    constructor
    · rintro ⟨p, ⟨hp, hpx⟩, hpy⟩
      exact ⟨fun h => hpx (hpy.trans h), p, hp, hpy⟩
    · rintro ⟨hy, p, hp, hpy⟩
      exact ⟨p, ⟨hp, fun h => hy (hpy.symm.trans h)⟩, hpy⟩

theorem elements_fold (ops : List (Event α)) (s : State α) :
    elements (ops.foldl update s) = ops.foldl setStep (elements s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons e ops ih => simpa only [List.foldl_cons, elements_update] using ih (update s e)

theorem sequential_refinement (ops : List (Event α)) :
    stateRel (applySeq (D α).toUpdateSig (D α).init ops) (spec.run ops) := by
  simpa [stateRel, applySeq, D, spec, SequentialMachine.run, elements] using
    elements_fold ops (∅ : State α)

/-- Public sequential refinement for any replay witness supplied by the
execution proof. This does not assert the missing replay-adequacy premise. -/
def sequentialCorrectness :
    SequentialCorrectnessCertificate (D α) issuance rc spec stateRel where
  sound := by
    intro C _exec replay v state E hver
    obtain ⟨ops, hp, hr, hf⟩ := replay v state E hver
    have hrel := sequential_refinement (α := α) ops
    rw [hf] at hrel
    refine ⟨ops, hp, hr, True.intro, hrel, ?_⟩
    intro x
    change decide ((x : α) ∈ elements state) =
      decide ((x : α) ∈ ops.foldl setStep (∅ : Finset α))
    change elements state = ops.foldl setStep (∅ : Finset α) at hrel
    exact congrArg (fun (q : Finset α) => decide ((x : α) ∈ q)) hrel

#print axioms sequential_refinement
#print axioms sequentialCorrectness

end LeanProofs.Implementations.EfficientORSet
