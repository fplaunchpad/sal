import Sal.MRDTs.Instances.NotionCoreMachineGenesis
import Sal.MRDTs.Instances.NotionCoreProtocol

/-! A concrete two-version Sal factory execution. This establishes that the
initialization theorem has an actual raw execution instance, not just a
conditional implication with an uninhabited application premise. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineGenesisControl
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionCorePayload (Transaction)
open NotionCoreMRDT (D)

def factoryEvent : Op Transaction := (0,0,NotionCorePayload.bootstrap [97,98])
noncomputable def factoryState : D.State := D.update D.init factoryEvent
private noncomputable def factoryVer (v : Version) : Option (D.State × Set (Op Transaction)) :=
  if v = 0 then some (D.init,∅) else if v = 1 then some (factoryState,{factoryEvent}) else none
private def factoryHead (r : Replica) : Option Version := if r = 0 then some 1 else none
private def factoryParents (v : Version) : List Version := if v = 1 then [0] else []
private theorem factory_rank : ∀ v p, p ∈ factoryParents v → p < v := by
  intro v p h
  by_cases hv : v = 1 <;> simp [factoryParents,hv] at h
  subst v; subst p; decide
private theorem factory_observed {r : Replica} {E : Set (Op Transaction)}
    (h : headEventsFrom factoryVer factoryHead r = some E) {e : Op Transaction} (he : e ∈ E) :
    e = factoryEvent := by
  by_cases hr : r = 0
  · subst r
    simp [headEventsFrom,factoryHead,factoryVer] at h
    subst E
    exact he
  · simp [headEventsFrom,factoryHead,hr] at h
private theorem factory_version_cases {v : Version} {s : D.State} {E : Set (Op Transaction)}
    (h : factoryVer v = some (s,E)) :
    (v = 0 ∧ s = D.init ∧ E = ∅) ∨ (v = 1 ∧ s = factoryState ∧ E = {factoryEvent}) := by
  by_cases hv : v = 0
  · simp [factoryVer,hv] at h
    exact Or.inl ⟨hv,h.1.symm,h.2.symm⟩
  · by_cases h1 : v = 1
    · simp [factoryVer,h1] at h
      exact Or.inr ⟨h1,h.1.symm,h.2.symm⟩
    · simp [factoryVer,hv,h1] at h

noncomputable def factoryConfig : Configuration D where
  vis := fun _ _ => False
  ver := factoryVer
  head := factoryHead
  parents := factoryParents
  parents_lt := factory_rank
  ver_init := by simp [factoryVer]
  head_alloc := by
    intro r v h
    by_cases hr : r = 0
    · simp [factoryHead,hr] at h
      subst v; simp [factoryVer]
    · simp [factoryHead,hr] at h
  vis_src := fun h => h.elim
  vis_tgt := fun h => h.elim
  vis_causal := fun h => h.elim
  timestamps_distinct := by
    intro a b r E r' E' ha he hb he' different
    exact (different ((factory_observed ha he).trans (factory_observed hb he').symm)).elim
  causal_mono := fun h => h.elim
  vis_total_same_replica := by
    intro a b r E r' E' ha he hb he' different same
    exact (different ((factory_observed ha he).trans (factory_observed hb he').symm)).elim
  gca_events := by
    intro v1 v2 vT s1 E1 s2 E2 sT ET gca hv1 hv2 hvT
    rcases factory_version_cases hv1 with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals rcases factory_version_cases hv2 with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals rcases factory_version_cases hvT with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals try simp
    all_goals try (simp only [IsGCA] at gca)
    all_goals try (exact (Nat.not_succ_le_zero 0 (reaches_le factory_rank gca.1)).elim)
    all_goals try (exact (Nat.not_succ_le_zero 0 (reaches_le factory_rank gca.2.1)).elim)
    exact (Nat.not_succ_le_zero 0 (reaches_le factory_rank (gca.2.2 1 .refl .refl))).elim

private theorem init_no_events : (initConfig D).events = ∅ := by
  ext e
  constructor
  · rintro ⟨r,E,h,he⟩
    by_cases hr : r = 0
    · simp [Configuration.headEvents,headEventsFrom,initConfig,hr] at h
      subst E; exact he
    · simp [Configuration.headEvents,headEventsFrom,initConfig,hr] at h
  · intro h; exact h.elim

theorem factory_step : Step D (initConfig D) (.apply 0 0 (NotionCorePayload.bootstrap [97,98])) factoryConfig := by
  apply Step.apply (v := 0) (s := D.init) (ev := ∅) (vnew := 1)
  · simp [initConfig]
  · simp [initConfig]
  · intro e he
    rw [init_no_events] at he
    exact he.elim
  · intro w sw Ew hw e he
    by_cases h0 : w = 0
    · simp [initConfig,h0] at hw
      obtain ⟨rfl,rfl⟩ := hw
      exact he.elim
    · simp [initConfig,h0] at hw
  · simp [initConfig]
  · decide
  · ext a b; change False ↔ False ∨ ((∅ : Set (Op Transaction)) a ∧ b = _); simp only [false_or]; constructor <;> intro h; exact h.elim; exact h.1.elim
  · funext w
    by_cases h0 : w = 0 <;> by_cases h1 : w = 1
    all_goals simp [factoryConfig,factoryVer,factoryState,factoryEvent,initConfig,h0,h1]
  · funext r
    by_cases hr : r = 0 <;> simp [factoryConfig,factoryHead,initConfig,hr]
  · rfl


def sessions (replica : Replica) : NotionRunAllocation.Session := 65 :: List.replicate replica 0

theorem sessions_injective : Function.Injective sessions := by
  intro left right same
  have lengths := congrArg List.length same
  simpa [sessions] using lengths

theorem paired_factory :
    NotionCoreMachineExecution.Pair factoryConfig (NotionCorePayloadNetwork.seeded [97,98])
      sessions (NotionCoreMachineExecution.extendLift (fun _ => factoryEvent)
        (NotionCorePayload.bootstrap [97,98]) factoryEvent) := by
  exact NotionCoreMachineGenesis.factory_pair sessions (fun _ => factoryEvent)
    (NotionCoreMachineGenesis.initial_pair sessions sessions_injective (fun _ => factoryEvent))
    0 0 [97,98] rfl factory_step

theorem protocol_factory :
    NotionCoreProtocol.Reach sessions (fun _ => factoryEvent) factoryConfig
      (NotionCorePayloadNetwork.seeded [97,98])
      (NotionCoreMachineExecution.extendLift (fun _ => factoryEvent)
        (NotionCorePayload.bootstrap [97,98]) factoryEvent) :=
  .factory .init 0 0 [97,98] rfl factory_step

/-- PASS+FAIL: the concrete Sal factory stores and renders the hand-derived ab
document. Neither reconstruction failure nor an empty root is its answer. -/
theorem factory_control :
    Step D (initConfig D) (.apply 0 0 (NotionCorePayload.bootstrap [97,98])) factoryConfig ∧
    D.query factoryState () = some [(0,[97,98])] ∧
    D.query factoryState () ≠ none ∧
    D.query factoryState () ≠ some [(0,[])] := by
  refine ⟨factory_step, ?_⟩
  exact NotionCoreMRDT.SPOT.render_control

#print axioms factory_step
#print axioms paired_factory
#print axioms protocol_factory
#print axioms factory_control
end Sal.MRDTs.Instances.NotionCoreMachineGenesisControl
