import Sal.MRDTs.Paper1.SetWinsMapVC
import Sal.MRDTs.Paper1.ProjectedSimulation

/-! Independent, timestamp-free accumulating multimap specification. Neem's
source provides no query; this chosen projection reflects its retained values,
without attributing a query contract to the source or ruling out other reads. -/
namespace Sal.MRDTs.Paper1.SetWinsMap
open Foundation Instances.SetWinsMap
open Classical
abbrev AbstractState := Finset (Nat × Nat)

def naturalStep (s : AbstractState) (a : Action) : AbstractState := match a with
  | .set k v => insert (k,v) s
  | .del k => s.filter (fun p => p.1 ≠ k)

def naturalLookup (s : AbstractState) (k : Nat) : Finset Nat :=
  (s.filter (fun p => p.1 = k)).image Prod.snd

def model : DeterministicSpec (Op Action) Nat (Finset Nat) where
  State := AbstractState
  initial := ∅
  update s e := naturalStep s e.op
  query := naturalLookup

def spec := model.toSpec

def view (s : State) : AbstractState := s.image Prod.snd

@[simp] theorem view_update (s : State) (e : Op Action) :
    view (update s e) = naturalStep (view s) e.op := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | set k v => simp [view,update,naturalStep,Op.op]
  | del k =>
    ext p
    simp only [view,update,naturalStep,Op.op,Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨q,⟨hq,ne⟩,rfl⟩
      exact ⟨⟨q,hq,rfl⟩,ne⟩
    · rintro ⟨⟨q,hq,eq⟩,ne⟩
      exact ⟨q,⟨hq,eq ▸ ne⟩,eq⟩

@[simp] theorem lookup_view (s : State) (k : Nat) : lookup s k = naturalLookup (view s) k := by
  ext v
  simp only [lookup,naturalLookup,view,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨q,⟨hq,key⟩,val⟩
    exact ⟨q.2,⟨⟨q,hq,rfl⟩,key⟩,val⟩
  · rintro ⟨p,⟨⟨q,hq,rfl⟩,key⟩,val⟩
    exact ⟨q,⟨hq,key⟩,val⟩

def projection : MachineProjection D model id where
  project := view
  initial := by simp [D,model,view]
  update := view_update
  observes := lookup_view

def simulation : EventSequentialSimulation D model := by
  derive_projected_simulation projection

theorem historySound : EventFoldHistorySound D spec := simulation.sound

theorem compatibility : CommutationCompatibility D id spec := by
  intro a b commute
  apply projection.language_commutes _ a b commute
  intro s
  refine ⟨s.image (fun p => (0,p)),?_⟩
  change view (s.image (fun p => (0,p))) = s
  simp [view,Finset.image_image]

#print axioms historySound
#print axioms compatibility
end Sal.MRDTs.Paper1.SetWinsMap
