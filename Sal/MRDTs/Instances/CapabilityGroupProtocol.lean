import Sal.MRDTs.Instances.CapabilityGroupOwnerOrder
import Sal.MRDTs.Paper1.SimpleConcretePorts
import Sal.MRDTs.Paper1.Automation.GenericQueryLift
import Sal.MRDTs.Framework.FiniteEvents

/-!
Capability-group issuance in the actual version-DAG execution semantics.

An authenticated subject is an explicit input bound to the issuing replica.
The owner has one issuing replica; recipients can use multiple replicas.
Payload IDs equal the framework's globally fresh timestamps, while payload
precursors describe precisely the local finite carrier. The five VCs establish
that carrier. Source validity and authorisation are proved separately below.
-/
namespace Sal.MRDTs.Instances.CapabilityGroup.Protocol
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Paper1.ConcreteMRDT

abbrev D (owner : Actor) : MRDTSig where
  State := State
  dec_state := inferInstance
  init := ∅
  AppOp := Event
  dec_op := inferInstance
  Query := Unit
  Value := Finset Name
  update state event := step state event.op
  merge := merge
  query state _ := names owner state

def issuance (owner : Actor) (principal : Replica → Actor) (ownerReplica : Replica) :
    Issuance (D owner) where
  CanIssue event state := event.op.id = event.time ∧
    event.op.actor = principal event.2.1 ∧
    (event.op.actor = owner → event.2.1 = ownerReplica) ∧
    CanIssue owner state event.op

theorem all_comm (owner : Actor) (a b : Op Event) :
    (D owner).toUpdateSig.commutes a b := FinsetStore.all_comm a b

abbrev representation (owner : Actor) : Representation (D owner) :=
  CommutingPort.representation (D owner)

abbrev scheme (owner : Actor) (C : ReplayContext (D owner).toUpdateSig) :=
  CommutingPort.scheme (all_comm owner) C

theorem fiveVCs (owner : Actor) :
    @Raw.MergeVCs (D owner) (commutingPolicy Event) (representation owner) (scheme owner) := by
  exact Automation.QueryLift.transport (FinsetStore.D Event) Unit (Finset Name)
    (fun state _ => names owner state) (commutingPolicy Event)
    (CommutingPort.representation (FinsetStore.D Event))
    (CommutingPort.scheme (FinsetStore.all_comm (α := Event)))
    (SimplePorts.Finite.conditions (A := Event)).vcs

noncomputable def replayConditions (owner : Actor) (I : Issuance (D owner)) :
    VCReplayConditions (commutingPolicy Event) I :=
  CommutingPort.automatedReplayConditions (all_comm owner) (fiveVCs owner) I

theorem fold_payloads (owner : Actor) (state : State) (events : List (Op Event)) :
    applySeq (D owner).toUpdateSig state events = state ∪ (events.map Op.op).toFinset := by
  induction events generalizing state with
  | nil => simp [applySeq]
  | cons event rest ih =>
    change applySeq (D owner).toUpdateSig (insert event.op state) rest = _
    rw [ih]
    ext x
    simp [or_left_comm]

theorem fold_mem (owner : Actor) (events : List (Op Event)) (payload : Event) :
    payload ∈ applySeq (D owner).toUpdateSig (D owner).init events ↔
      ∃ event ∈ events, event.op = payload := by
  rw [fold_payloads]
  simp [D]

theorem represented_mem (owner : Actor) (C : ReplayContext (D owner).toUpdateSig)
    (E : Set (Op Event)) (state : State) (represented : representation owner C E state)
    (payload : Event) : payload ∈ state ↔ ∃ event ∈ E, event.op = payload := by
  obtain ⟨_, events, enumeration, folded⟩ := represented
  rw [← folded, fold_mem]
  exact exists_congr fun event => and_congr (enumeration.2 event) Iff.rfl

theorem event_time_injective (owner : Actor) (C : Configuration (D owner))
    {a b : Op Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (time : a.time = b.time) : a = b := by
  by_contra different
  obtain ⟨r, E, hr, ha⟩ := ha
  obtain ⟨r', E', hr', hb⟩ := hb
  exact C.timestamps_distinct hr ha hr' hb different time

theorem event_guard {owner : Actor} {principal : Replica → Actor} {ownerReplica : Replica}
    (C : Configuration (D owner))
    (honest : MintHonest (D owner) (issuance owner principal ownerReplica).CanIssue C)
    {event : Op Event} (member : event ∈ C.events) :
    event.op.id = event.time ∧ event.op.actor = principal event.2.1 ∧
      (event.op.actor = owner → event.2.1 = ownerReplica) := by
  obtain ⟨_, _, _, guard⟩ := honest event member
  exact ⟨guard.1, guard.2.1, guard.2.2.1⟩

/-- Payload predecessor membership is derived from the issuer's actual
mint-time state, rather than assumed as a completed source invariant. -/
theorem before_iff_visibility {owner : Actor} {principal : Replica → Actor}
    {ownerReplica : Replica} (C : Configuration (D owner))
    (honest : MintHonest (D owner) (issuance owner principal ownerReplica).CanIssue C)
    {a b : Op Event} (ha : a ∈ C.events) (hb : b ∈ C.events) :
    before a.op b.op ↔ C.vis a b := by
  obtain ⟨past, enumeration, _, guard⟩ := honest b hb
  have fresh := guard.2.2.2.1
  have aid := (event_guard C honest ha).1
  constructor
  · intro predecessor
    change a.op.id ∈ b.op.past at predecessor
    rw [fresh.1] at predecessor
    obtain ⟨payload, present, sameId⟩ := Finset.mem_image.mp predecessor
    obtain ⟨old, oldMember, payloadSame⟩ := (fold_mem owner past payload).mp present
    have oldGlobal := ((enumeration.2 old).mp oldMember).1
    have oldId := (event_guard C honest oldGlobal).1
    have sameTime : old.time = a.time := by rw [← oldId, payloadSame, sameId, aid]
    have same := event_time_injective owner C oldGlobal ha sameTime
    exact same ▸ ((enumeration.2 old).mp oldMember).2
  · intro visibility
    change a.op.id ∈ b.op.past
    rw [fresh.1]
    apply Finset.mem_image.mpr
    exact ⟨a.op, (fold_mem owner past a.op).mpr
      ⟨a, (enumeration.2 a).mpr ⟨ha, visibility⟩, rfl⟩, rfl⟩

theorem predecessor_exists {owner : Actor} {principal : Replica → Actor}
    {ownerReplica : Replica} (C : Configuration (D owner))
    (honest : MintHonest (D owner) (issuance owner principal ownerReplica).CanIssue C)
    {event : Op Event} (member : event ∈ C.events) {identifier : Id}
    (predecessor : identifier ∈ event.op.past) :
    ∃ old ∈ C.events, C.vis old event ∧ old.op.id = identifier := by
  obtain ⟨past, enumeration, _, guard⟩ := honest event member
  rw [guard.2.2.2.1.1] at predecessor
  obtain ⟨payload, present, sameId⟩ := Finset.mem_image.mp predecessor
  obtain ⟨old, oldMember, payloadSame⟩ := (fold_mem owner past payload).mp present
  obtain ⟨oldGlobal, visible⟩ := (enumeration.2 old).mp oldMember
  exact ⟨old, oldGlobal, visible, by rw [payloadSame, sameId]⟩

/-- The source history hypotheses are consequences of the local issuer and
the five-VC represented-state induction. No source invariant is a premise. -/
theorem registered_source {owner : Actor} {principal : Replica → Actor}
    {ownerReplica : Replica} (C : Configuration (D owner))
    (reach : MintCertifiedReachV (D owner) (canonicalVirtualMergeBase (D owner))
      (issuance owner principal ownerReplica) C)
    (v : Version) (state : State) (E : Set (Op Event))
    (registered : C.ver v = some (state,E)) :
    WellFormed state ∧ LocallyAdmitted owner state ∧ OwnerOrdered owner state := by
  have honest := reach.mintHonest
  have good := CommutingPort.automatedCanonicalConfig (all_comm owner) (fiveVCs owner) reach
  have represented := (replayConditions owner (issuance owner principal ownerReplica)).representedVersions
    C reach v state E registered
  have payloads := represented_mem owner C.replayContext E state represented
  have supported : ∀ event ∈ E, event ∈ C.events := represented.1
  have wf : WellFormed state := by
    constructor
    · intro a ha b hb sameId
      obtain ⟨ea, hea, rfl⟩ := (payloads a).mp ha
      obtain ⟨eb, heb, rfl⟩ := (payloads b).mp hb
      have ga := event_guard C honest (supported ea hea)
      have gb := event_guard C honest (supported eb heb)
      have equal := event_time_injective owner C (supported ea hea) (supported eb heb)
        (ga.1.symm.trans (sameId.trans gb.1))
      exact congrArg Op.op equal
    · intro event he identifier predecessor
      obtain ⟨e, member, rfl⟩ := (payloads event).mp he
      obtain ⟨old, oldGlobal, visible, sameId⟩ :=
        predecessor_exists C honest (supported e member) predecessor
      have oldMember := good.version_events_causal v state E registered old e visible member
      exact ⟨old.op, (payloads old.op).mpr ⟨old,oldMember,rfl⟩,sameId⟩
    · intro event he previous hp beforeEvent identifier predecessor
      obtain ⟨e, member, rfl⟩ := (payloads event).mp he
      obtain ⟨p, previousMember, rfl⟩ := (payloads previous).mp hp
      have pe := (before_iff_visibility C honest (supported p previousMember)
        (supported e member)).mp beforeEvent
      obtain ⟨old, oldGlobal, op, sameId⟩ :=
        predecessor_exists C honest (supported p previousMember) predecessor
      have oe := good.vis_trans op pe
      have payloadBefore := (before_iff_visibility C honest oldGlobal (supported e member)).mpr oe
      simpa only [before, sameId] using payloadBefore
    · intro event he identifier predecessor
      obtain ⟨e, member, rfl⟩ := (payloads event).mp he
      obtain ⟨old, oldGlobal, visible, sameId⟩ :=
        predecessor_exists C honest (supported e member) predecessor
      have increasing := C.causal_mono visible
      change old.time < e.time at increasing
      rw [← (event_guard C honest oldGlobal).1,
        ← (event_guard C honest (supported e member)).1, sameId] at increasing
      exact increasing
  have locally : LocallyAdmitted owner state := by
    intro event he
    obtain ⟨e, member, rfl⟩ := (payloads event).mp he
    obtain ⟨past, enumeration, _, guard⟩ := honest e (supported e member)
    have cut : pre state e.op = applySeq (D owner).toUpdateSig (D owner).init past := by
      ext payload
      rw [mem_pre, fold_mem]
      constructor
      · rintro ⟨present, causal⟩
        obtain ⟨p, previousMember, rfl⟩ := (payloads payload).mp present
        have visible := (before_iff_visibility C honest (supported p previousMember)
          (supported e member)).mp causal
        exact ⟨p,(enumeration.2 p).mpr ⟨supported p previousMember,visible⟩,rfl⟩
      · rintro ⟨p, previousMember, rfl⟩
        obtain ⟨oldGlobal,visible⟩ := (enumeration.2 p).mp previousMember
        have oldMember := good.version_events_causal v state E registered p e visible member
        exact ⟨(payloads p.op).mpr ⟨p,oldMember,rfl⟩,
          (before_iff_visibility C honest oldGlobal (supported e member)).mpr visible⟩
    unfold admitted
    rw [cut]
    exact authorized_at_issue guard.2.2.2
  have ownerOrdered : OwnerOrdered owner state := by
    intro a ha b hb ownerA ownerB
    obtain ⟨ea, hea, rfl⟩ := (payloads a).mp ha
    obtain ⟨eb, heb, rfl⟩ := (payloads b).mp hb
    by_cases equal : ea = eb
    · exact Or.inl (congrArg Op.op equal)
    · have eaGlobal := supported ea hea
      have ebGlobal := supported eb heb
      have ga := event_guard C honest eaGlobal
      have gb := event_guard C honest ebGlobal
      obtain ⟨ra, Ea, headA, eventA⟩ := eaGlobal
      obtain ⟨rb, Eb, headB, eventB⟩ := ebGlobal
      have sameReplica : ea.2.1 = eb.2.1 := (ga.2.2 ownerA).trans (gb.2.2 ownerB).symm
      rcases C.vis_total_same_replica headA eventA headB eventB equal sameReplica with ab | ba
      · exact Or.inr (Or.inl ((before_iff_visibility C honest (supported ea hea)
          (supported eb heb)).mpr ab))
      · exact Or.inr (Or.inr ((before_iff_visibility C honest (supported eb heb)
          (supported ea hea)).mpr ba))
  exact ⟨wf,locally,ownerOrdered⟩

#print axioms fiveVCs
#print axioms before_iff_visibility
#print axioms registered_source

end Sal.MRDTs.Instances.CapabilityGroup.Protocol
