import Sal.MRDTs.Paper1.RemoveWinsSetReplay
import Sal.MRDTs.Paper1.ProjectedSimulation

/-! Ordinary finite-set histories, independently of removal tags. Full events
are labels, but the abstract machine decodes only the Add/Rem request. -/
namespace Sal.MRDTs.Paper1.RemoveWinsSet
open Foundation Instances.RemoveWinsSet
variable {α : Type} [DecidableEq α] [Fintype α]

def decode : Update α → NaturalSetSpec.Action α
  | .add x => .add x
  | .remove x => .remove x

def model (α : Type) [DecidableEq α] : DeterministicSpec (Op (Update α)) α Bool :=
  NaturalSetSpec.model (fun e => decode e.op)

def spec (α : Type) [DecidableEq α] := (model α).toSpec

@[simp] theorem view_initial : view (initial α) = ∅ := by
  simp [view,initial,Finset.image_image,Function.comp_def]

@[simp] theorem view_step (s : State α) (e : Op (Update α)) :
    view (step s e) = NaturalSetSpec.step (view s) (decode e.op) := by
  rcases e with ⟨ts,r,op⟩
  cases op with
  | remove x =>
    ext y
    simp [view,step,decode,NaturalSetSpec.step,Op.op]
  | add x =>
    ext y
    simp only [view,step,decode,NaturalSetSpec.step,Op.op,Finset.mem_sdiff,
      Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_image,Finset.mem_filter]
    constructor
    · intro h
      by_cases same : y = x
      · exact Or.inl same
      · right
        rintro ⟨p,hp,rfl⟩
        exact h ⟨p,⟨hp,same⟩,rfl⟩
    · rintro (rfl | h) ⟨p,⟨hp,neq⟩,same⟩
      · exact neq same
      · exact h ⟨p,hp,same⟩

def projection : MachineProjection (D α) (model α) id where
  project := view
  initial := view_initial
  update := view_step
  observes _ _ := rfl

def simulation : EventSequentialSimulation (D α) (model α) := by
  derive_projected_simulation projection

theorem historySound : EventFoldHistorySound (D α) (spec α) := simulation.sound

theorem compatible : CommutationCompatibility (D α) id (spec α) := by
  intro a b hc
  apply projection.language_commutes _ a b hc
  intro s
  refine ⟨(Finset.univ \ s).image (fun x => (x,0)),?_⟩
  change view ((Finset.univ \ s).image (fun x => (x,0))) = s
  ext x
  simp [view,Finset.image_image,Function.comp_def]

end Sal.MRDTs.Paper1.RemoveWinsSet
