import Sal.MRDTs.Instances.NotionCoreMachineGenesis

/-! Constructive finite participant support before factory initialization.
An actual fork-only Sal prefix allocates empty participants. Its source partner
remains literally the initial network; this is not a transformation theorem
for arbitrary timed source traces. -/
namespace Sal.MRDTs.Instances.NotionCoreMachinePreallocation
open Sal.MRDTs Sal.MRDTs.Foundation
open NotionCoreMRDT (D)
open NotionCoreArchiveEvents (Event)
open NotionCorePayload (Transaction)
open NotionRunAllocation (Session)

private noncomputable def emptyVer (allocated : Finset Replica) (v : Version) :
    Option (D.State × Set Event) :=
  if v = 0 then some (D.init,∅) else if v - 1 ∈ allocated then some (D.init,∅) else none
private def emptyHead (allocated : Finset Replica) (replica : Replica) : Option Version :=
  if replica = 0 then some 0 else if replica ∈ allocated then some (replica + 1) else none
private def emptyParents (allocated : Finset Replica) (v : Version) : List Version :=
  if v = 0 then [] else if v - 1 ∈ allocated then [0] else []

private theorem version_empty (allocated : Finset Replica) {v : Version} {state : D.State} {events : Set Event}
    (stored : emptyVer allocated v = some (state,events)) : state = D.init ∧ events = ∅ := by
  unfold emptyVer at stored
  split at stored
  · exact ⟨(Prod.mk.inj (Option.some.inj stored)).1.symm,(Prod.mk.inj (Option.some.inj stored)).2.symm⟩
  · split at stored
    · exact ⟨(Prod.mk.inj (Option.some.inj stored)).1.symm,(Prod.mk.inj (Option.some.inj stored)).2.symm⟩
    · contradiction

private theorem observed_empty (allocated : Finset Replica) {replica : Replica} {events : Set Event}
    (observed : headEventsFrom (emptyVer allocated) (emptyHead allocated) replica = some events) : events = ∅ := by
  unfold headEventsFrom at observed
  cases head : emptyHead allocated replica with
  | none => simp [head] at observed
  | some v =>
    cases stored : emptyVer allocated v with
    | none => simp [head,stored] at observed
    | some pair =>
      have empty := (version_empty allocated stored).2
      simpa [head,stored,empty] using observed.symm

/-- A finite star of empty copies of version zero. Replica zero remains the
fork source; every nonzero participant keeps its own distinct child version. -/
noncomputable def emptyConfig (allocated : Finset Replica) : Configuration D where
  vis := fun _ _ => False
  ver := emptyVer allocated
  head := emptyHead allocated
  parents := emptyParents allocated
  parents_lt := by
    intro v parent member
    by_cases zero : v = 0
    · simp [emptyParents,zero] at member
    · have positive : 0 < v := Nat.pos_of_ne_zero zero
      by_cases present : v - 1 ∈ allocated
      · simp [emptyParents,zero,present] at member
        subst parent
        exact positive
      · simp [emptyParents,zero,present] at member
  ver_init := by simp [emptyVer]
  head_alloc := by
    intro replica v head
    by_cases zero : replica = 0
    · simp [emptyHead,zero] at head
      subst v
      simp [emptyVer]
    · by_cases present : replica ∈ allocated
      · simp [emptyHead,zero,present] at head
        subst v
        simp [emptyVer,present]
      · simp [emptyHead,zero,present] at head
  vis_src := fun h => h.elim
  vis_tgt := fun h => h.elim
  vis_causal := fun h => h.elim
  timestamps_distinct := by
    intro a b replica events other otherEvents head member rest otherMember distinct
    have empty := observed_empty allocated head
    exact False.elim (by simpa only [empty] using member)
  causal_mono := fun h => h.elim
  vis_total_same_replica := by
    intro a b replica events other otherEvents head member rest otherMember distinct same
    exact False.elim (by simpa only [observed_empty allocated head] using member)
  gca_events := by
    intro v1 v2 base s1 e1 s2 e2 sb eb gca first second initial
    rw [(version_empty allocated first).2,(version_empty allocated second).2,(version_empty allocated initial).2]
    simp

 theorem empty_config_initial : emptyConfig ∅ = initConfig D := by
  unfold emptyConfig initConfig
  simp only [Configuration.mk.injEq]
  refine ⟨trivial,?_,?_,?_⟩
  · funext v; simp [emptyVer]
  · funext replica; simp [emptyHead]
  · funext v; simp [emptyParents]

/-- Each genuinely fresh nonzero participant is allocated by the literal
raw fork semantics, with no operation mint and no source clock reservation. -/
theorem empty_fork_step (allocated : Finset Replica) (replica : Replica)
    (nonzero : replica ≠ 0) (fresh : replica ∉ allocated) :
    Step D (emptyConfig allocated) (.fork replica 0) (emptyConfig (insert replica allocated)) := by
  apply Step.fork (v := 0) (vnew := replica + 1) (s := D.init) (ev := ∅)
  · simp [emptyConfig,emptyHead,nonzero,fresh]
  · simp [emptyConfig,emptyHead]
  · simp [emptyConfig,emptyVer]
  · simp [emptyConfig,emptyVer,fresh]
  · exact Nat.zero_lt_succ replica
  · rfl
  · funext v
    by_cases zero : v = 0
    · subst v
      simp [emptyConfig,emptyVer]
    · have same : v - 1 = replica ↔ v = replica + 1 := by
        constructor
        · intro equal
          have back := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero)
          rw [equal] at back
          exact back.symm
        · intro equal
          rw [equal]
          simp
      by_cases selected : v = replica + 1
      · subst v
        simp [emptyConfig,emptyVer]
      · simp [emptyConfig,emptyVer,zero,selected,same]
  · funext peer
    by_cases same : peer = replica
    · subst peer
      simp [emptyConfig,emptyHead,nonzero]
    · simp [emptyConfig,emptyHead,same]
  · funext v
    by_cases zero : v = 0
    · subst v
      simp [emptyConfig,emptyParents]
    · have same : v - 1 = replica ↔ v = replica + 1 := by
        constructor
        · intro equal
          have back := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero)
          rw [equal] at back
          exact back.symm
        · intro equal
          rw [equal]
          simp
      by_cases selected : v = replica + 1
      · subst v
        simp [emptyConfig,emptyParents]
      · simp [emptyConfig,emptyParents,zero,selected,same]

/-- Proof-only restriction to actual empty forks; this is not an interpreter. -/
inductive EmptyForkPrefix : Configuration D → Prop where
  | initial : EmptyForkPrefix (initConfig D)
  | fork {before after : Configuration D} (replica : Replica) :
      EmptyForkPrefix before → Step D before (.fork replica 0) after → EmptyForkPrefix after

 theorem finite_empty_prefix (allocated : Finset Replica) (nonzero : 0 ∉ allocated) :
    EmptyForkPrefix (emptyConfig allocated) := by
  induction allocated using Finset.induction_on with
  | empty => simpa only [empty_config_initial] using EmptyForkPrefix.initial
  | @insert replica rest fresh ih =>
    have different : replica ≠ 0 := by intro equal; exact nonzero (by simp [equal])
    have old : 0 ∉ rest := by intro member; exact nonzero (Finset.mem_insert_of_mem member)
    exact EmptyForkPrefix.fork replica (ih old) (empty_fork_step rest replica different fresh)

 theorem exchange_initial (target source : Session) :
    NotionCorePayloadNetwork.exchange NotionCorePayloadNetwork.initial target source = NotionCorePayloadNetwork.initial := rfl

/-- Source identities, archive, receipt lists, and clocks are literally
unchanged by the complete preallocation prefix. -/
theorem prefix_pair (config : Configuration D) (forks : EmptyForkPrefix config)
    (sessions : Replica → Session) (injective : Function.Injective sessions)
    (lift : Transaction → Event) :
    NotionCoreMachineExecution.Pair config NotionCorePayloadNetwork.initial sessions lift := by
  induction forks with
  | initial => exact NotionCoreMachineGenesis.initial_pair sessions injective lift
  | fork replica prior step ih =>
    simpa only [exchange_initial] using NotionCoreMachineExecution.fork_preserves
      NotionCorePayloadNetwork.initial sessions lift ih replica 0 step

 theorem finite_participants (participants : Finset Replica) :
    ∃ config, EmptyForkPrefix config ∧
      ∀ replica ∈ participants, ∃ version,
        config.head replica = some version ∧ config.ver version = some (D.init,∅) := by
  refine ⟨emptyConfig (participants.erase 0),finite_empty_prefix _ (by simp),?_⟩
  intro replica member
  by_cases zero : replica = 0
  · subst replica
    exact ⟨0,by simp [emptyConfig,emptyHead],by simp [emptyConfig,emptyVer]⟩
  · refine ⟨replica + 1,?_,?_⟩
    · simp [emptyConfig,emptyHead,zero,member]
    · simp [emptyConfig,emptyVer,zero,member]

theorem EmptyForkPrefix.raw {config : Configuration D} (forks : EmptyForkPrefix config) :
    (labeledTS D).ReachableFrom (initConfig D) config := by
  induction forks with
  | initial => exact .refl
  | fork replica prior step ih => exact ih.tail ⟨.fork replica 0,step⟩

/-- Any finite collection of session-assigned source participants can be
available before factory creation. Their source allocator identities and
network remain unchanged throughout this actual Sal prefix. -/
theorem finite_source_participants (participants : Finset Replica)
    (sessions : Replica → Session) (injective : Function.Injective sessions)
    (lift : Transaction → Event) :
    ∃ config, EmptyForkPrefix config ∧
      NotionCoreMachineExecution.Pair config NotionCorePayloadNetwork.initial sessions lift ∧
      ∀ replica ∈ participants, ∃ version,
        config.head replica = some version ∧ config.ver version = some (D.init,∅) := by
  obtain ⟨config,forks,heads⟩ := finite_participants participants
  exact ⟨config,forks,prefix_pair config forks sessions injective lift,heads⟩

namespace SPOT
/-- A distinct empty participant is allocated a copied CHILD version, not
reset to root zero, while the source carrier and event set remain empty. -/
theorem copied_empty_control :
    Step D (emptyConfig ∅) (.fork 2 0) (emptyConfig {2}) ∧
    (emptyConfig {2}).head 2 = some 3 ∧ (emptyConfig {2}).head 2 ≠ some 0 ∧
    (emptyConfig {2}).ver 3 = some (D.init,∅) := by
  refine ⟨empty_fork_step ∅ 2 (by decide) (by simp),?_,?_,?_⟩ <;> simp [emptyConfig,emptyHead,emptyVer]
end SPOT

#print axioms EmptyForkPrefix.raw
#print axioms finite_source_participants
#print axioms empty_fork_step
#print axioms finite_empty_prefix
#print axioms prefix_pair
#print axioms finite_participants
#print axioms SPOT.copied_empty_control
end Sal.MRDTs.Instances.NotionCoreMachinePreallocation
