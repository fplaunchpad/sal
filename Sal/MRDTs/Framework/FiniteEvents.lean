import Sal.MRDTs.Framework.Certificates
import Mathlib.Data.Set.Finite.Basic

/-! A finite execution observes finitely many events even though the replica
and version maps have infinite domains. Fork and merge only copy/union old
head events; apply adds one event. No finiteness premise is required of heads.
-/
namespace Sal.MRDTs
open Foundation

private theorem head_event_subset {D : MRDTSig} (C : Configuration D)
    {r : Replica} {v : Version} {s : D.State} {E : Set (Op D.AppOp)}
    (hh : C.head r = some v) (hv : C.ver v = some (s,E)) : E ⊆ C.events := by
  intro e he
  exact ⟨r,E,C.headEvents_eq_of_head_ver hh hv,he⟩

private theorem finite_after_head_update {D : MRDTSig} {C C' : Configuration D}
    {r : Replica} {E : Set (Op D.AppOp)}
    (hh : C'.headEvents = updateRep C.headEvents r E)
    (old : C.events.Finite) (new : E.Finite) : C'.events.Finite := by
  apply (new.union old).subset
  rintro e ⟨r',S,hS,he⟩
  rw [hh] at hS
  by_cases same : r' = r
  · subst r'
    simp [updateRep] at hS
    exact Or.inl (hS.symm ▸ he)
  · simp only [updateRep,if_neg same] at hS
    exact Or.inr ⟨r',S,hS,he⟩

theorem Step.events_finite {D : MRDTSig} {C C' : Configuration D} {l : Label D}
    (h : Step D C l C') (old : C.events.Finite) : C'.events.Finite := by
  cases h with
  | fork freshReplica sourceHead sourceVersion freshVersion rank C' vis ver head parents =>
    exact finite_after_head_update
      (Configuration.headEvents_update_of_store_head_update _ _ freshVersion ver head)
      old (old.subset (head_event_subset _ sourceHead sourceVersion))
  | apply headAt versionAt freshTime freshStore freshVersion rank C' vis ver head parents =>
    exact finite_after_head_update
      (Configuration.headEvents_update_of_store_head_update _ _ freshVersion ver head)
      old ((old.subset (head_event_subset _ headAt versionAt)).union (Set.finite_singleton _))
  | merge head₁ head₂ version₁ version₂ gca versionGCA freshVersion rank₁ rank₂ C' vis ver head parents =>
    exact finite_after_head_update
      (Configuration.headEvents_update_of_store_head_update _ _ freshVersion ver head)
      old ((old.subset (head_event_subset _ head₁ version₁)).union
        (old.subset (head_event_subset _ head₂ version₂)))
  | query => exact old

theorem StepV.events_finite {D : MRDTSig} {V : VirtualMergeBaseResolver D}
    {C C' : Configuration D} {l : Label D}
    (h : StepV D V C l C') (old : C.events.Finite) : C'.events.Finite := by
  cases h with
  | base one => exact one.events_finite old
  | mergeVirtual head₁ head₂ version₁ version₂ freshVersion rank₁ rank₂ C' vis ver head parents =>
    exact finite_after_head_update
      (Configuration.headEvents_update_of_store_head_update _ _ freshVersion ver head)
      old ((old.subset (head_event_subset _ head₁ version₁)).union
        (old.subset (head_event_subset _ head₂ version₂)))

@[simp] theorem initConfig_events_finite (D : MRDTSig) : (initConfig D).events.Finite := by
  have empty : (initConfig D).events = ∅ := by
    ext e
    constructor
    · rintro ⟨r,E,hE,he⟩
      by_cases hr : r = 0
      · subst r
        simp [Configuration.headEvents,headEventsFrom,initConfig] at hE
        subst E
        exact he
      · simp [Configuration.headEvents,headEventsFrom,initConfig,hr] at hE
    · intro h
      exact h.elim
  rw [empty]
  exact Set.finite_empty

theorem reachableV_events_finite {D : MRDTSig} {V : VirtualMergeBaseResolver D}
    {C : Configuration D}
    (h : (labeledTSV D V).ReachableFrom (initConfig D) C) : C.events.Finite := by
  induction h with
  | refl => exact initConfig_events_finite D
  | tail h one ih =>
    obtain ⟨l,step⟩ := one
    exact step.events_finite ih

theorem MintCertifiedReachV.events_finite {D : MRDTSig}
    {V : VirtualMergeBaseResolver D} {I : Issuance D} {C : Configuration D}
    (h : MintCertifiedReachV D V I C) : C.events.Finite :=
  reachableV_events_finite h.toReachable

end Sal.MRDTs
