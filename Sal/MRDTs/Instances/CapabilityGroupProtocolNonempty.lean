import Sal.MRDTs.Instances.CapabilityGroupProtocol

/-! Nonvacuity of the real authenticated single-owner issuance protocol.
Replica/actor 0 first grants itself capability 1, then assigns name 10 using
that grant. Both applies, their mint-time cuts, and all configuration fields
are constructed explicitly. No reachable-configuration premise is supplied.
-/
namespace Sal.MRDTs.Instances.CapabilityGroup.ProtocolNonempty
open Sal.MRDTs Sal.MRDTs.Foundation

abbrev D := Protocol.D 0
abbrev I := Protocol.issuance 0 id 0

def grant : Event := ⟨1,0,∅,.grant 0⟩
def assignment : Event := ⟨2,0,{1},.assign 1 10⟩
def grantEvent : Op Event := (1,0,grant)
def assignmentEvent : Op Event := (2,0,assignment)
def log : State := {grant,assignment}

private def versions (both : Bool) (v : Version) : Option (State × Set (Op Event)) :=
  if v = 0 then some (∅,∅) else if v = 1 then some ({grant},{grantEvent})
  else if both && v == 2 then some (log,{grantEvent,assignmentEvent}) else none
private def heads (both : Bool) (r : Replica) : Option Version :=
  if r = 0 then some (if both then 2 else 1) else none
private def parents (both : Bool) (v : Version) : List Version :=
  if v = 1 then [0] else if both && v == 2 then [1] else []
private def visibility (both : Bool) (a b : Op Event) : Prop :=
  both = true ∧ a = grantEvent ∧ b = assignmentEvent

private theorem parents_rank (both : Bool) : ∀ v p, p ∈ parents both v → p < v := by
  intro v p member
  by_cases first : v = 1
  · subst v; simp [parents] at member; subst p; decide
  · cases both <;> simp [parents,first] at member
    rcases member with ⟨rfl,rfl⟩
    decide

private theorem head_events {both : Bool} {r : Replica} {E : Set (Op Event)}
    (head : headEventsFrom (D := D) (versions both) (heads both) r = some E) :
    E = if both then {grantEvent,assignmentEvent} else {grantEvent} := by
  by_cases owner : r = 0
  · cases both <;> simpa [headEventsFrom,heads,versions,owner] using head.symm
  · simp [headEventsFrom,heads,owner] at head

private theorem grant_versions_cases {v : Version} {state : State} {E : Set (Op Event)}
    (version : versions false v = some (state,E)) :
    (v = 0 ∧ state = ∅ ∧ E = ∅) ∨ (v = 1 ∧ state = {grant} ∧ E = {grantEvent}) := by
  by_cases zero : v = 0
  · simp [versions,zero] at version; exact .inl ⟨zero,version.1.symm,version.2.symm⟩
  · by_cases one : v = 1
    · simp [versions,one] at version; exact .inr ⟨one,version.1.symm,version.2.symm⟩
    · simp [versions,zero,one] at version

private theorem versions_cases {v : Version} {state : State} {E : Set (Op Event)}
    (version : versions true v = some (state,E)) :
    (v = 0 ∧ state = ∅ ∧ E = ∅) ∨ (v = 1 ∧ state = {grant} ∧ E = {grantEvent}) ∨
      (v = 2 ∧ state = log ∧ E = {grantEvent,assignmentEvent}) := by
  by_cases zero : v = 0
  · simp [versions,zero] at version; exact .inl ⟨zero,version.1.symm,version.2.symm⟩
  · by_cases one : v = 1
    · simp [versions,one] at version; exact .inr (.inl ⟨one,version.1.symm,version.2.symm⟩)
    · by_cases two : v = 2
      · simp [versions,two] at version
        exact .inr (.inr ⟨two,version.1.symm,version.2.symm⟩)
      · simp [versions,zero,one,two] at version

private theorem one_two : Reaches (parents true) 1 2 := .single (by simp [parents])

private def configuration (both : Bool) : Configuration D where
  vis := visibility both
  ver := versions both
  head := heads both
  parents := parents both
  parents_lt := parents_rank both
  ver_init := by simp [versions]
  head_alloc := by
    intro r v head
    by_cases owner : r = 0
    · cases both <;> simp [heads,owner] at head <;> subst v <;> simp [versions]
    · simp [heads,owner] at head
  vis_src := by
    intro a b visible
    obtain ⟨rfl,rfl,rfl⟩ := visible
    exact ⟨0,{grantEvent,assignmentEvent},rfl,Or.inl rfl⟩
  vis_tgt := by
    intro a b visible
    obtain ⟨rfl,rfl,rfl⟩ := visible
    exact ⟨0,{grantEvent,assignmentEvent},rfl,Or.inr rfl⟩
  vis_causal := by
    intro a b r E visible head member
    obtain ⟨rfl,rfl,rfl⟩ := visible
    rw [head_events head]
    exact Or.inl rfl
  timestamps_distinct := by
    intro a b r E r' E' head member head' member' different
    rw [head_events head] at member
    rw [head_events head'] at member'
    cases both <;> simp only [Bool.false_eq_true,↓reduceIte] at member member'
    · subst a; subst b; exact (different rfl).elim
    · rcases member with rfl | rfl <;> rcases member' with rfl | rfl
      all_goals first | exact (different rfl).elim | decide
  causal_mono := by
    intro a b visible
    obtain ⟨rfl,rfl,rfl⟩ := visible
    decide
  vis_total_same_replica := by
    intro a b r E r' E' head member head' member' different same
    rw [head_events head] at member
    rw [head_events head'] at member'
    cases both <;> simp only [Bool.false_eq_true,↓reduceIte] at member member'
    · subst a; subst b; exact (different rfl).elim
    · rcases member with rfl | rfl <;> rcases member' with rfl | rfl
      · exact (different rfl).elim
      · exact .inl ⟨rfl,rfl,rfl⟩
      · exact .inr ⟨rfl,rfl,rfl⟩
      · exact (different rfl).elim
  gca_events := by
    intro v1 v2 vT s1 E1 s2 E2 sT ET gca version1 version2 versionT
    cases both with
    | false =>
      rcases grant_versions_cases version1 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
        rcases grant_versions_cases version2 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
        rcases grant_versions_cases versionT with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩
      all_goals try simp
      all_goals try (have bound := reaches_le (parents_rank false) gca.1; norm_num at bound)
      all_goals try (have bound := reaches_le (parents_rank false) gca.2.1; norm_num at bound)
      all_goals try (have bound := reaches_le (parents_rank false) (gca.2.2 1 .refl .refl); norm_num at bound)
    | true =>
      rcases versions_cases version1 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
        rcases versions_cases version2 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
        rcases versions_cases versionT with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩
      all_goals try simp
      all_goals try (have bound := reaches_le (parents_rank true) gca.1; norm_num at bound)
      all_goals try (have bound := reaches_le (parents_rank true) gca.2.1; norm_num at bound)
      all_goals try (have bound := reaches_le (parents_rank true) (gca.2.2 1 .refl .refl); norm_num at bound)
      all_goals try (have bound := reaches_le (parents_rank true) (gca.2.2 1 .refl one_two); norm_num at bound)
      all_goals try (have bound := reaches_le (parents_rank true) (gca.2.2 1 one_two .refl); norm_num at bound)
      all_goals try (have bound := reaches_le (parents_rank true) (gca.2.2 2 .refl .refl); norm_num at bound)

def grantConfig : Configuration D := configuration false
def config : Configuration D := configuration true

private theorem events_eq (both : Bool) :
    (configuration both).events = if both then {grantEvent,assignmentEvent} else {grantEvent} := by
  ext event
  constructor
  · rintro ⟨r,E,head,member⟩
    rw [head_events head] at member
    exact member
  · intro member
    exact ⟨0,_,by cases both <;> rfl,member⟩

theorem grant_guard : I.CanIssue grantEvent ∅ := by
  dsimp [I,Protocol.issuance]
  decide +kernel
theorem assignment_guard : I.CanIssue assignmentEvent {grant} := by
  dsimp [I,Protocol.issuance]
  decide +kernel

theorem grant_step : Step D (initConfig D) (.apply 1 0 grant) grantConfig := by
  apply Step.apply (D := D) (v := 0) (s := ∅) (ev := ∅) (vnew := 1)
  · simp [initConfig]
  · simp [initConfig]
  · intro event member
    obtain ⟨r,E,head,present⟩ := member
    by_cases owner : r = 0
    · simp [Configuration.headEvents,headEventsFrom,initConfig,owner] at head
      subst E; exact present.elim
    · simp [Configuration.headEvents,headEventsFrom,initConfig,owner] at head
  · intro v state E version event member
    by_cases zero : v = 0
    · simp [initConfig,zero] at version; obtain ⟨rfl,rfl⟩ := version; exact member.elim
    · simp [initConfig,zero] at version
  · simp [initConfig]
  · decide
  · funext a b
    apply propext
    change (false = true ∧ a = grantEvent ∧ b = assignmentEvent) ↔
      False ∨ ((∅ : Set (Op Event)) a ∧ b = grantEvent)
    constructor
    · intro impossible; exact (Bool.false_ne_true impossible.1).elim
    · rintro (impossible | impossible)
      · exact impossible.elim
      · exact impossible.1.elim
  · funext v
    by_cases zero : v = 0 <;> by_cases one : v = 1 <;>
      simp [grantConfig,configuration,versions,initConfig,step,zero,one,grantEvent,Op.op]
  · funext r
    by_cases owner : r = 0 <;> simp [grantConfig,configuration,heads,initConfig,owner]
  · funext v
    by_cases one : v = 1 <;> simp [grantConfig,configuration,parents,initConfig,one]

theorem assignment_step : Step D grantConfig (.apply 2 0 assignment) config := by
  apply Step.apply (D := D) (v := 1) (s := {grant}) (ev := {grantEvent}) (vnew := 2)
  · rfl
  · rfl
  · intro event member
    change event ∈ (configuration false).events at member
    rw [events_eq] at member
    have same := Set.mem_singleton_iff.mp member
    subst event; decide
  · intro v state E version event member
    rcases grant_versions_cases version with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩
    · exact member.elim
    · have same := Set.mem_singleton_iff.mp member; subst event; decide
  · rfl
  · decide
  · funext a b
    apply propext
    change (true = true ∧ a = grantEvent ∧ b = assignmentEvent) ↔
      (false = true ∧ a = grantEvent ∧ b = assignmentEvent) ∨
        (({grantEvent} : Set (Op Event)) a ∧ b = assignmentEvent)
    constructor
    · rintro ⟨_,sameA,sameB⟩
      exact .inr ⟨sameA,sameB⟩
    · rintro (impossible | visible)
      · exact (Bool.false_ne_true impossible.1).elim
      · exact ⟨rfl,visible.1,visible.2⟩
  · funext v
    by_cases zero : v = 0 <;> by_cases one : v = 1 <;> by_cases two : v = 2
    all_goals simp [config,grantConfig,configuration,versions,step,log,zero,one,two,
      grantEvent,assignmentEvent,Op.op,Finset.pair_comm,Set.pair_comm]
  · funext r
    by_cases owner : r = 0 <;> simp [config,grantConfig,configuration,heads,owner]
  · funext v
    by_cases one : v = 1 <;> by_cases two : v = 2 <;>
      simp [config,grantConfig,configuration,parents,one,two]

private theorem mint_honest (both : Bool) : MintHonest D I.CanIssue (configuration both) := by
  intro event member
  rw [events_eq] at member
  cases both with
  | false =>
    have same := Set.mem_singleton_iff.mp member
    subst event
    refine ⟨[],?_,?_,grant_guard⟩
    · constructor
      · simp
      · intro event; simp [configuration,visibility]
    · simp [respects]
  | true =>
    rcases Set.mem_insert_iff.mp member with same | same
    · subst event
      refine ⟨[],?_,?_,grant_guard⟩
      · constructor
        · simp
        · intro event; simp [configuration,visibility,grantEvent,assignmentEvent]
      · simp [respects]
    · have same := Set.mem_singleton_iff.mp same
      subst event
      refine ⟨[grantEvent],?_,?_,?_⟩
      · constructor
        · simp
        · intro event
          change event ∈ [grantEvent] ↔ event ∈ (configuration true).events ∧
            visibility true event assignmentEvent
          rw [events_eq]
          simp [visibility,grantEvent,assignmentEvent]
          intro same
          exact .inl same
      · simp [respects,configuration,visibility,grantEvent,assignmentEvent]
      · simpa [applySeq,Protocol.D,step] using assignment_guard

theorem grant_reach : MintCertifiedReach D I grantConfig :=
  .step .init (MintCertifiedReach.mintHonest .init)
    (.apply rfl rfl grant_guard grant_step) (mint_honest false)

theorem reach : MintCertifiedReach D I config :=
  .step grant_reach (mint_honest false)
    (.apply rfl rfl assignment_guard assignment_step) (mint_honest true)

theorem reachV : MintCertifiedReachV D (canonicalVirtualMergeBase D) I config := reach.toV

theorem registered : config.ver 2 = some (log,{grantEvent,assignmentEvent}) := rfl

/-- PASS+FAIL: the reachable final registered state exposes name 10; the
protocol and its query are neither empty-only nor universally rejecting. -/
theorem query_control : D.query log () = {10} ∧ D.query log () ≠ ∅ := by decide +kernel

theorem source_control : WellFormed log ∧ LocallyAdmitted 0 log ∧ OwnerOrdered 0 log :=
  Protocol.registered_source config reachV 2 log {grantEvent,assignmentEvent} registered

#print axioms grant_step
#print axioms assignment_step
#print axioms reachV
#print axioms query_control
#print axioms source_control
end Sal.MRDTs.Instances.CapabilityGroup.ProtocolNonempty
