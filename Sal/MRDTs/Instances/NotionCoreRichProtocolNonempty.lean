import Sal.MRDTs.Instances.NotionCoreRichProtocol

/-! A concrete actual version-DAG execution bootstraps ab and toggles the
actual displayed selection. Its whole format transaction is prepared and
allocated by the repaired source caller, not supplied as a verdict premise. -/
namespace Sal.MRDTs.Instances.NotionCoreRichProtocolNonempty
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open NotionCoreRichPayload (Transaction Payload Part)
open NotionCoreRichProtocolCarrier (D)
open NotionCoreRichProtocolEvents (Event)
abbrev State := Finset Transaction
local instance : EmptyCollection D.State := (inferInstance : EmptyCollection State)
local instance : Singleton Transaction D.State := (inferInstance : Singleton Transaction State)
private theorem init_empty : D.init = (∅ : State) := rfl
attribute [local simp] init_empty

def bootstrap : Transaction := NotionCoreRichProtocol.factoryTx [97,98]
def formatPayload : Payload := .format [⟨0,⟨.item ⟨1,[65]⟩,.before⟩,⟨.finish,.before⟩⟩] true
def formatting : Transaction := ⟨⟨3,[65]⟩,formatPayload⟩
def bootstrapEvent : Event := (1,0,bootstrap)
def formatEvent : Event := (2,0,formatting)
def log : State := {bootstrap,formatting}
def step (state : State) (tx : Transaction) : State := insert tx state

private def versions (both : Bool) (v : Version) : Option (State × Set Event) :=
  if v = 0 then some (∅,∅) else if v = 1 then some ({bootstrap},{bootstrapEvent})
  else if both && v == 2 then some (log,{bootstrapEvent,formatEvent}) else none
private def heads (both : Bool) (r : Replica) : Option Version :=
  if r = 0 then some (if both then 2 else 1) else none
private def parents (both : Bool) (v : Version) : List Version :=
  if v = 1 then [0] else if both && v == 2 then [1] else []
private def visibility (both : Bool) (a b : Event) : Prop :=
  both = true ∧ a = bootstrapEvent ∧ b = formatEvent

private theorem parents_rank (both : Bool) : ∀ v p, p ∈ parents both v → p < v := by
  intro v p member
  by_cases first : v = 1
  · subst v; simp [parents] at member; subst p; decide
  · cases both <;> simp [parents,first] at member
    rcases member with ⟨rfl,rfl⟩
    decide

private theorem head_events {both : Bool} {r : Replica} {E : Set Event}
    (head : headEventsFrom (D := D) (versions both) (heads both) r = some E) :
    E = if both then {bootstrapEvent,formatEvent} else {bootstrapEvent} := by
  by_cases owner : r = 0
  · cases both <;> simpa [headEventsFrom,heads,versions,owner] using head.symm
  · simp [headEventsFrom,heads,owner] at head

private theorem bootstrap_versions_cases {v : Version} {state : State} {E : Set Event}
    (version : versions false v = some (state,E)) :
    (v = 0 ∧ state = ∅ ∧ E = ∅) ∨ (v = 1 ∧ state = {bootstrap} ∧ E = {bootstrapEvent}) := by
  by_cases zero : v = 0
  · simp [versions,zero] at version; exact .inl ⟨zero,version.1.symm,version.2.symm⟩
  · by_cases one : v = 1
    · simp [versions,one] at version; exact .inr ⟨one,version.1.symm,version.2.symm⟩
    · simp [versions,zero,one] at version

private theorem versions_cases {v : Version} {state : State} {E : Set Event}
    (version : versions true v = some (state,E)) :
    (v = 0 ∧ state = ∅ ∧ E = ∅) ∨ (v = 1 ∧ state = {bootstrap} ∧ E = {bootstrapEvent}) ∨
      (v = 2 ∧ state = log ∧ E = {bootstrapEvent,formatEvent}) := by
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
    exact ⟨0,{bootstrapEvent,formatEvent},rfl,Or.inl rfl⟩
  vis_tgt := by
    intro a b visible
    obtain ⟨rfl,rfl,rfl⟩ := visible
    exact ⟨0,{bootstrapEvent,formatEvent},rfl,Or.inr rfl⟩
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
      rcases bootstrap_versions_cases version1 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
        rcases bootstrap_versions_cases version2 with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;>
        rcases bootstrap_versions_cases versionT with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩
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

def bootstrapConfig : Configuration D := configuration false
def config : Configuration D := configuration true

private theorem events_eq (both : Bool) :
    (configuration both).events = if both then {bootstrapEvent,formatEvent} else {bootstrapEvent} := by
  ext event
  constructor
  · rintro ⟨r,E,head,member⟩
    rw [head_events head] at member
    exact member
  · intro member
    exact ⟨0,_,by cases both <;> rfl,member⟩

theorem bootstrap_step : Step D (initConfig D) (.apply 1 0 bootstrap) bootstrapConfig := by
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
    change (false = true ∧ a = bootstrapEvent ∧ b = formatEvent) ↔
      False ∨ ((∅ : Set Event) a ∧ b = bootstrapEvent)
    constructor
    · intro impossible; exact (Bool.false_ne_true impossible.1).elim
    · rintro (impossible | impossible)
      · exact impossible.elim
      · exact impossible.1.elim
  · funext v
    by_cases zero : v = 0 <;> by_cases one : v = 1 <;>
      simp [bootstrapConfig,configuration,versions,initConfig,step,zero,one,bootstrapEvent,Op.op]
  · funext r
    by_cases owner : r = 0 <;> simp [bootstrapConfig,configuration,heads,initConfig,owner]
  · funext v
    by_cases one : v = 1 <;> simp [bootstrapConfig,configuration,parents,initConfig,one]

theorem format_step : Step D bootstrapConfig (.apply 2 0 formatting) config := by
  apply Step.apply (D := D) (v := 1) (s := {bootstrap}) (ev := {bootstrapEvent}) (vnew := 2)
  · rfl
  · rfl
  · intro event member
    change event ∈ (configuration false).events at member
    rw [events_eq] at member
    have same := Set.mem_singleton_iff.mp member
    subst event; decide
  · intro v state E version event member
    rcases bootstrap_versions_cases version with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩
    · exact member.elim
    · have same := Set.mem_singleton_iff.mp member; subst event; decide
  · rfl
  · decide
  · funext a b
    apply propext
    change (true = true ∧ a = bootstrapEvent ∧ b = formatEvent) ↔
      (false = true ∧ a = bootstrapEvent ∧ b = formatEvent) ∨
        (({bootstrapEvent} : Set Event) a ∧ b = formatEvent)
    constructor
    · rintro ⟨_,sameA,sameB⟩
      exact .inr ⟨sameA,sameB⟩
    · rintro (impossible | visible)
      · exact (Bool.false_ne_true impossible.1).elim
      · exact ⟨rfl,visible.1,visible.2⟩
  · funext v
    by_cases zero : v = 0 <;> by_cases one : v = 1 <;> by_cases two : v = 2
    all_goals simp [config,bootstrapConfig,configuration,versions,step,log,zero,one,two,
      bootstrapEvent,formatEvent,Op.op,Finset.pair_comm,Set.pair_comm]
  · funext r
    by_cases owner : r = 0 <;> simp [config,bootstrapConfig,configuration,heads,owner]
  · funext v
    by_cases one : v = 1 <;> by_cases two : v = 2 <;>
      simp [config,bootstrapConfig,configuration,parents,one,two]


def sessions (replica : Replica) : NotionRunAllocation.Session := 65 :: List.replicate replica 0

theorem sessions_injective : Function.Injective sessions := by
  intro left right same
  have lengths := congrArg List.length same
  simpa [sessions] using lengths

def sourceBase := NotionCoreRichProtocolNetwork.seeded [97,98]
def sourceFinal := NotionCoreRichProtocolNetwork.emit sourceBase [65] formatPayload
noncomputable def initialLift (_tx : Transaction) : Event := bootstrapEvent
noncomputable def bootstrapLift := NotionCoreRichProtocolPair.extendLift initialLift bootstrap bootstrapEvent
noncomputable def finalLift := NotionCoreRichProtocolPair.extendLift bootstrapLift formatting formatEvent

theorem actual_preparation :
    NotionCoreRichProtocolNetwork.prepareAt sourceBase [65] (.toggle .initial 0 2) = some formatPayload ∧
    (NotionCoreRichProtocolNetwork.references formatPayload).all
      (NotionCoreRichProtocolNetwork.known sourceBase [65]) = true := by decide +kernel

theorem bootstrap_reachable :
    NotionCoreRichProtocol.Reach sessions initialLift bootstrapConfig sourceBase bootstrapLift :=
  .factory .init 1 0 [97,98] rfl bootstrap_step

theorem reachable :
    NotionCoreRichProtocol.Reach sessions initialLift config sourceFinal finalLift := by
  exact .request bootstrap_reachable 2 0 (.toggle .initial 0 2) formatPayload
    actual_preparation.1 actual_preparation.2 format_step

theorem registered : config.ver 2 = some (log,{bootstrapEvent,formatEvent}) := rfl

def expected (bold : Bool) : NotionCoreRichProtocolCarrier.View :=
  [(0,[⟨NotionCorePhysicalReplay.address 0 ⟨1,[65]⟩,97,bold⟩,
        ⟨NotionCorePhysicalReplay.address 0 ⟨2,[65]⟩,98,bold⟩])]

/-- PASS+FAIL: the actual finite-carrier rich query returns two bold visible
characters after actual positional selection. Neither failure, empty output
nor the unformatted bootstrap is its observation. -/
theorem query_control :
    D.query log () = some (expected true) ∧ D.query log () ≠ none ∧
      D.query log () ≠ some [] ∧ D.query log () ≠ some (expected false) := by
  have ordered : [bootstrap,formatting].Pairwise
      (fun a b => NotionRunAllocation.Before a.id b.id) := by decide +kernel
  have image : log = [bootstrap,formatting].toFinset := rfl
  have query : D.query log () = some (expected true) := by
    change NotionCoreRichProtocolCarrier.observe log = _
    rw [NotionCoreRichProtocolCarrier.observe,image,
      NotionCoreRichProtocolCarrier.transactions_of_sorted _ ordered]
    decide +kernel
  refine ⟨query,?_,?_,?_⟩
  · rw [query]
    change (some (expected true) : Option NotionCoreRichProtocolCarrier.View) ≠ none
    decide +kernel
  · rw [query]
    change (some (expected true) : Option NotionCoreRichProtocolCarrier.View) ≠ some []
    decide +kernel
  · rw [query]
    change (some (expected true) : Option NotionCoreRichProtocolCarrier.View) ≠ some (expected false)
    decide +kernel

#print axioms reachable
#print axioms query_control
end Sal.MRDTs.Instances.NotionCoreRichProtocolNonempty
