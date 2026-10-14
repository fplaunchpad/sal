import Sal.MRDTs.Instances.NotionCoreStructuralTransport
import Sal.MRDTs.Instances.NotionCoreProtocol

/-! Operational configuration transport for the structural carrier. Honest
query equality is explicit until the structural renderer is connected. The
source protocol, including its real issuance guards and factory phase, is
reused; no replacement permissive issuance policy is introduced. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralExecution
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionCorePayload (Transaction)
open NotionCoreStructuralTransport (project)
open NotionCoreStructuralFacts (State)

abbrev Query := State → Unit → Option NotionCoreHistory.View
noncomputable abbrev Target (query : Query) := NotionCoreStructuralVC.D query
abbrev Archive := Finset Transaction
abbrev Events := Set (Op Transaction)

def mapVer (ver : Version → Option (Archive × Events)) : Version → Option (State × Events) :=
 fun v => (ver v).map (fun pair => (project pair.1,pair.2))

@[simp] theorem mapVer_some {ver : Version → Option (Archive × Events)}
    {v archive events} (registered : ver v = some (archive,events)) :
    mapVer ver v = some (project archive,events) := by simp [mapVer,registered]

@[simp] theorem mapVer_none {ver : Version → Option (Archive × Events)}
    {v} (unallocated : ver v = none) : mapVer ver v = none := by simp [mapVer,unallocated]

theorem mapVer_some_iff (ver : Version → Option (Archive × Events))
    (v : Version) (state : State) (events : Events) :
    mapVer ver v = some (state,events) ↔
      ∃ archive, ver v = some (archive,events) ∧ project archive = state := by
  cases h : ver v with
  | none => simp [mapVer,h]
  | some pair =>
    rcases pair with ⟨archive,stored⟩
    simp only [mapVer,h,Option.map_some,Option.some.injEq,Prod.mk.injEq]
    aesop

@[simp] theorem headEvents_mapVer (query : Query)
    (ver : Version → Option (Archive × Events)) (head : Replica → Option Version)
    (r : Replica) :
    @headEventsFrom (Target query) (mapVer ver) head r =
      @headEventsFrom NotionCoreMRDT.D ver head r := by
  unfold headEventsFrom
  cases h : head r with
  | none => simp
  | some v => cases hv : ver v <;> simp [mapVer,hv]

noncomputable def mapConfig (query : Query) (C : Configuration NotionCoreMRDT.D) :
    Configuration (Target query) where
  vis := C.vis
  ver := mapVer C.ver
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by simp [mapVer,C.ver_init,Target,NotionCoreStructuralVC.D,
    Sal.MRDTs.Paper1.Automation.QueryLift.withQuery,FinsetStore.D]
  head_alloc := by intro r v h; simpa [mapVer] using C.head_alloc r v h
  vis_src := by
    intro a b h
    obtain ⟨r,s,hs,member⟩ := C.vis_src h
    exact ⟨r,s,by simpa using hs,member⟩
  vis_tgt := by
    intro a b h
    obtain ⟨r,s,hs,member⟩ := C.vis_tgt h
    exact ⟨r,s,by simpa using hs,member⟩
  vis_causal := by intro a b r s h head member; exact C.vis_causal h (by simpa using head) member
  timestamps_distinct := by
    intro a b r s r' s' head member head' member' ne
    exact C.timestamps_distinct (by simpa using head) member (by simpa using head') member' ne
  causal_mono := C.causal_mono
  vis_total_same_replica := by
    intro a b r s r' s' head member head' member' ne same
    exact C.vis_total_same_replica (by simpa using head) member (by simpa using head') member' ne same
  gca_events := by
    intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT gca h₁ h₂ hT
    obtain ⟨a₁,ha₁,_⟩ := (mapVer_some_iff C.ver v₁ s₁ e₁).mp h₁
    obtain ⟨a₂,ha₂,_⟩ := (mapVer_some_iff C.ver v₂ s₂ e₂).mp h₂
    obtain ⟨aT,haT,_⟩ := (mapVer_some_iff C.ver vT sT eT).mp hT
    exact C.gca_events gca ha₁ ha₂ haT

@[simp] theorem map_headEvents (query : Query) (C : Configuration NotionCoreMRDT.D) :
    (mapConfig query C).headEvents = C.headEvents := by
  funext r
  exact headEvents_mapVer query C.ver C.head r

@[simp] theorem map_events (query : Query) (C : Configuration NotionCoreMRDT.D) :
    (mapConfig query C).events = C.events := by
  unfold Configuration.events
  rw [map_headEvents]
  rfl

@[simp] theorem map_headState (query : Query) (C : Configuration NotionCoreMRDT.D) (r : Replica) :
    (mapConfig query C).headState r = (C.headState r).map project := by
  unfold Configuration.headState headStateFrom
  change (C.head r >>= fun v => (mapVer C.ver v).map Prod.fst) = _
  cases h : C.head r with
  | none => simp
  | some v => cases hv : C.ver v <;> simp [mapVer,hv]

private theorem config_ext {D : MRDTSig} (C C' : Configuration D)
    (vis : C.vis = C'.vis) (ver : C.ver = C'.ver)
    (head : C.head = C'.head) (parents : C.parents = C'.parents) : C = C' := by
  cases C; cases C'; cases vis; cases ver; cases head; cases parents; rfl

@[simp] theorem map_init (query : Query) :
    mapConfig query (initConfig NotionCoreMRDT.D) = initConfig (Target query) := by
  apply config_ext <;> try rfl
  funext v
  by_cases zero : v = 0 <;>
    simp [mapConfig,mapVer,initConfig,zero,Target,NotionCoreStructuralVC.D,
      Sal.MRDTs.Paper1.Automation.QueryLift.withQuery,FinsetStore.D]

def mapLabel (query : Query) : Label NotionCoreMRDT.D → Label (Target query)
 | .fork dst src => .fork dst src
 | .apply time sender tx => .apply time sender tx
 | .merge target source => .merge target source
 | .query sender q answer => .query sender q answer

/-- Equality only at actual source heads. An arbitrary raw archive equality
would be stronger than the intended honest renderer theorem. -/
def QueryAgreement (query : Query) (C : Configuration NotionCoreMRDT.D) : Prop :=
 ∀ r archive, C.headState r = some archive →
   query (project archive) () = NotionCoreMRDT.observe archive

private theorem mapVer_update (ver : Version → Option (Archive × Events))
    (fresh : Version) (archive : Archive) (events : Events) :
    mapVer (fun v => if v = fresh then some (archive,events) else ver v) =
      fun v => if v = fresh then some (project archive,events) else mapVer ver v := by
  funext v; by_cases h : v = fresh <;> simp [mapVer,h]

/-- Every actual raw step maps to a raw structural step with exactly the same
operation/query label and all event/version metadata preserved. -/
theorem step (query : Query) {C C' : Configuration NotionCoreMRDT.D}
    {label : Label NotionCoreMRDT.D} (agreement : QueryAgreement query C)
    (raw : Step NotionCoreMRDT.D C label C') :
    Step (Target query) (mapConfig query C) (mapLabel query label) (mapConfig query C') := by
  cases raw with
  | fork freshReplica sourceHead sourceVersion freshVersion rank next vis ver head parents =>
    apply Step.fork (D := Target query) freshReplica sourceHead (mapVer_some sourceVersion) (mapVer_none freshVersion) rank
    · exact vis
    · change mapVer C'.ver = _
      rw [ver,mapVer_update]
      rfl
    · exact head
    · exact parents
  | apply headAt versionAt freshTime freshStore freshVersion rank next vis ver head parents =>
    apply Step.apply (D := Target query) headAt (mapVer_some versionAt)
    · simpa using freshTime
    · intro w sw Ew registered event member
      obtain ⟨archive,stored,_⟩ := (mapVer_some_iff C.ver w sw Ew).mp registered
      exact freshStore w archive Ew stored event member
    · exact mapVer_none freshVersion
    · exact rank
    · exact vis
    · change mapVer C'.ver = _
      rw [ver,mapVer_update,NotionCoreStructuralTransport.update_commutes query]
      rfl
    · exact head
    · exact parents
  | merge head₁ head₂ version₁ version₂ gca versionGCA freshVersion rank₁ rank₂ next vis ver head parents =>
    apply Step.merge (D := Target query) head₁ head₂ (mapVer_some version₁) (mapVer_some version₂) gca
      (mapVer_some versionGCA) (mapVer_none freshVersion) rank₁ rank₂
    · exact vis
    · change mapVer C'.ver = _
      rw [ver,mapVer_update,NotionCoreStructuralTransport.merge_commutes query]
      rfl
    · exact head
    · exact parents
  | @query r q value archive stateAt answer =>
    apply Step.query (D := Target query) (s := project archive)
    · rw [map_headState,stateAt]; rfl
    · cases q
      exact answer.trans (agreement r archive stateAt).symm

/-- Canonical recursive-base merges transport through the actual target
resolver. Base-state equality is unnecessary because both merges ignore base. -/
theorem stepV (query : Query) {C C' : Configuration NotionCoreMRDT.D}
    {label : Label NotionCoreMRDT.D} (agreement : QueryAgreement query C)
    (raw : StepV NotionCoreMRDT.D (canonicalVirtualMergeBase NotionCoreMRDT.D) C label C') :
    StepV (Target query) (canonicalVirtualMergeBase (Target query))
      (mapConfig query C) (mapLabel query label) (mapConfig query C') := by
  cases raw with
  | base raw => exact .base (step query agreement raw)
  | mergeVirtual head₁ head₂ version₁ version₂ freshVersion rank₁ rank₂ next vis ver head parents =>
    apply StepV.mergeVirtual (D := Target query) head₁ head₂ (mapVer_some version₁) (mapVer_some version₂)
      (mapVer_none freshVersion) rank₁ rank₂
    · exact vis
    · change mapVer C'.ver = _
      rw [ver,mapVer_update]
      simp only [NotionCoreMRDT.merge_union,NotionCoreStructuralTransport.project_union]
      rfl
    · exact head
    · exact parents

/-- Reuses the existing factory/client protocol exactly. Query agreement is
needed only at configurations that this honest protocol actually reaches. -/
theorem protocol_reachable (query : Query)
    (sessions : Replica → NotionRunAllocation.Session)
    (initialLift : Transaction → NotionCoreArchiveEvents.Event)
    (agreement : ∀ {C network lift},
      NotionCoreProtocol.Reach sessions initialLift C network lift → QueryAgreement query C)
    {C network lift} (honest : NotionCoreProtocol.Reach sessions initialLift C network lift) :
    (labeledTSV (Target query) (canonicalVirtualMergeBase (Target query))).ReachableFrom
      (initConfig (Target query)) (mapConfig query C) := by
  induction honest with
  | init => rw [map_init]; exact .refl
  | fork before target source raw ih =>
    exact ih.tail ⟨_,.base (step query (agreement before) raw)⟩
  | merge before target source raw ih => exact ih.tail ⟨_,stepV query (agreement before) raw⟩
  | factory before time sender atoms factorySession raw ih =>
    exact ih.tail ⟨_,.base (step query (agreement before) raw)⟩
  | apply before time sender tx v state events head registered guard raw ih =>
    exact ih.tail ⟨_,.base (step query (agreement before) raw)⟩
  | query before sender q answer raw ih => exact ih

#print axioms step
#print axioms stepV
#print axioms protocol_reachable
end Sal.MRDTs.Instances.NotionCoreStructuralExecution
