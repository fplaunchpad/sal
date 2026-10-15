import Sal.MRDTs.Instances.PublishedAddWinsPriorityQueue
import Sal.MRDTs.Instances.AddWinsPriorityQueueFull

/-! An intentional repair of published Add-Win CRPQ: select innate and acquired
priority from the SAME latest surviving insertion. All effects and preparation
snapshots are unchanged. Signed increments target only observed insertion IDs;
removed records never contribute to a later insertion. This is not Algorithm 2's
independent Most-Change-Win query. Integer priorities and natural element IDs.

Stored versions under Sal's issuance discipline are causally closed. An early
increment placeholder without its birth is therefore outside that execution
claim. Raw states are totalized by querying only known, unremoved births; forged
birth-ID collisions choose the greatest innate value. Honest globally unique
IDs make this fallback immaterial. Maximum ties choose the greatest element ID.
-/
namespace Sal.MRDTs.Instances.PriorityQueueSameRecord
open Foundation
abbrev State := PublishedAddWinsPriorityQueue.State
abbrev Event := PublishedAddWinsPriorityQueue.Event
abbrev Payload := PublishedAddWinsPriorityQueue.Payload
abbrev Request := PublishedAddWinsPriorityQueue.Request
abbrev Query := AddWinsPriorityQueue.FullQuery
abbrev Answer := AddWinsPriorityQueue.Answer
abbrev step := PublishedAddWinsPriorityQueue.step
abbrev merge := PublishedAddWinsPriorityQueue.merge
abbrev prepare := PublishedAddWinsPriorityQueue.prepare

/-- Only live births, ordered by timestamp, then innate value on forged ties. -/
def candidates (s : State) (x : Nat) : Finset (Lex (Nat × Int)) :=
  (s.births.filter (fun b => b.1.1 = x ∧ b.1 ∉ s.removed)).image
    (fun b => toLex (b.1.2,b.2))

def priority (s : State) (x : Nat) : Option Int :=
  Option.map (fun b => (ofLex b).2 + PublishedAddWinsPriorityQueue.acquired s (x,(ofLex b).1)) (candidates s x).max

def elements (s : State) : Finset Nat :=
  (s.births.filter (fun b => b.1 ∉ s.removed)).image (fun b => b.1.1)

def getMax (s : State) : Option (Nat × Int) :=
  AddWinsPriorityQueue.selectMax (elements s) (priority s)

def read (s : State) : Query → Answer
  | .empty => .boolean (decide (elements s = ∅))
  | .lookup x => .boolean (decide (x ∈ elements s))
  | .getPri x => .priority (priority s x)
  | .getMax => .maximum (getMax s)

def D : MRDTSig where
  State := State
  dec_state := inferInstance
  init := {}
  AppOp := Payload
  dec_op := inferInstance
  Query := Query
  Value := Answer
  update := step
  merge := merge
  query := read

def generation : Issuance D where
  CanIssue e s := prepare s e.time e.rep (PublishedAddWinsPriorityQueue.requestOf e.op) = some e

/-- Observe locally, issue the existing observed Remove, return the observed
pair. This client operation makes no atomic cross-replica extraction claim. -/
def prepareRmvMax (s : State) (timestamp replica : Nat) :
    Option (Event × (Nat × Int)) :=
  (getMax s).map (fun pair =>
    ((timestamp,replica,.remove pair.1 (PublishedAddWinsPriorityQueue.observed s pair.1)),pair))

def rmvMax (s : State) (timestamp replica : Nat) : Option ((Nat × Int) × State) :=
  (prepareRmvMax s timestamp replica).map (fun prepared => (prepared.2,step s prepared.1))

theorem priority_none_iff (s : State) (x : Nat) :
    priority s x = none ↔ x ∉ elements s := by
  simp only [priority,Option.map_eq_none_iff]
  change (candidates s x).max = ⊥ ↔ _
  rw [Finset.max_eq_bot]
  simp only [candidates,Finset.image_eq_empty,Finset.filter_eq_empty_iff,
    elements,Finset.mem_image,Finset.mem_filter]
  constructor
  · intro absent ⟨b,⟨hb,hr⟩,he⟩
    exact absent hb ⟨he,hr⟩
  · intro absent b hb ⟨he,hr⟩
    exact absent ⟨b,⟨hb,hr⟩,he⟩

theorem getMax_none_iff (s : State) : getMax s = none ↔ elements s = ∅ := by
  rw [getMax,AddWinsPriorityQueue.selectMax_none_iff]
  constructor
  · intro absent
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (priority_none_iff s x).mp (absent x hx) hx
  · intro empty x hx
    rw [empty] at hx
    exact False.elim (Finset.notMem_empty _ hx)

theorem getMax_sound (s : State) (x : Nat) (p : Int)
    (selected : getMax s = some (x,p)) :
    x ∈ elements s ∧ priority s x = some p ∧
      ∀ y q, y ∈ elements s → priority s y = some q → q ≤ p :=
  AddWinsPriorityQueue.selectMax_sound (elements s) (priority s) x p selected

/-- A reported priority comes from an actual live birth, with the greatest
insertion timestamp, and that SAME birth's increment attachments. -/
theorem priority_selected_record (s : State) (x : Nat) (p : Int)
    (reported : priority s x = some p) :
    ∃ t v, ((x,t),v) ∈ s.births ∧ (x,t) ∉ s.removed ∧
      p = v + PublishedAddWinsPriorityQueue.acquired s (x,t) ∧
      ∀ u w, ((x,u),w) ∈ s.births → (x,u) ∉ s.removed → u ≤ t := by
  cases h : (candidates s x).max with
  | bot => simp only [priority,h] at reported; cases reported
  | coe best =>
    have value : p = (ofLex best).2 +
        PublishedAddWinsPriorityQueue.acquired s (x,(ofLex best).1) := by
      exact (Option.some.inj (by simpa only [priority,h] using reported)).symm
    obtain ⟨b,hb,equal⟩ := Finset.mem_image.mp (Finset.mem_of_max h)
    obtain ⟨member,key,live⟩ := Finset.mem_filter.mp hb
    have pair : (b.1.2,b.2) = ofLex best := congrArg ofLex equal
    have bt := congrArg Prod.fst pair
    have bv := congrArg Prod.snd pair
    refine ⟨b.1.2,b.2,?_,?_,?_,?_⟩
    · simpa only [← key] using member
    · simpa only [← key] using live
    · simpa only [← bt,← bv] using value
    · intro u w member live
      have candidate : toLex (u,w) ∈ candidates s x :=
        Finset.mem_image.mpr ⟨((x,u),w),Finset.mem_filter.mpr ⟨member,rfl,live⟩,rfl⟩
      have ordered := Prod.Lex.le_iff.mp (Finset.le_max_of_eq candidate h)
      rcases ordered with less | same
      · exact le_of_lt (by simpa only [← bt] using less)
      · exact le_of_eq (by simpa only [← bt] using same.1)

private theorem birth_observed (s : State) (b : PublishedAddWinsPriorityQueue.Birth)
    (member : b ∈ s.births) (live : b.1 ∉ s.removed) :
    b.1.2 ∈ PublishedAddWinsPriorityQueue.observed s b.1.1 := by
  apply Finset.mem_image.mpr
  refine ⟨b.1,Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
  apply Finset.mem_sdiff.mpr
  exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,member,rfl⟩),live⟩

/-- An observed Remove clears exactly its own element, preserving all others.
The finite candidate equality holds even on raw states with placeholders. -/
theorem candidates_remove (s : State) (t r x y : Nat) :
    candidates (step s (t,r,.remove x (PublishedAddWinsPriorityQueue.observed s x))) y =
      if y = x then ∅ else candidates s y := by
  by_cases equal : y = x
  · subst y
    rw [if_pos rfl]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨b,hb,_⟩ := Finset.mem_image.mp hp
    obtain ⟨member,key,live⟩ := Finset.mem_filter.mp hb
    change b ∈ s.births at member
    change b.1 ∉ s.removed ∪
      (PublishedAddWinsPriorityQueue.observed s x).image (fun tag => (x,tag)) at live
    have oldLive : b.1 ∉ s.removed := fun h => live (Finset.mem_union_left _ h)
    have obs : b.1.2 ∈ PublishedAddWinsPriorityQueue.observed s x := by
      simpa only [key] using birth_observed s b member oldLive
    exact live (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b.1.2,obs,by
      exact Prod.ext key.symm rfl⟩))
  · rw [if_neg equal]
    apply congrArg (Finset.image _)
    ext b
    simp only [candidates,step,PublishedAddWinsPriorityQueue.step,Finset.mem_filter,
      Finset.mem_union,Finset.mem_image,not_or]
    constructor
    · rintro ⟨member,key,live,_⟩
      exact ⟨member,key,live⟩
    · rintro ⟨member,key,live⟩
      refine ⟨member,key,live,?_⟩
      rintro ⟨tag,_,eq⟩
      have first := congrArg Prod.fst eq
      exact equal (key.symm.trans first.symm)

theorem priority_remove (s : State) (t r x y : Nat) :
    priority (step s (t,r,.remove x (PublishedAddWinsPriorityQueue.observed s x))) y =
      if y = x then none else priority s y := by
  unfold priority
  rw [candidates_remove]
  by_cases equal : y = x
  · simp only [if_pos equal,Finset.max_empty]; rfl
  · simp only [if_neg equal]; rfl

theorem elements_remove (s : State) (t r x : Nat) :
    elements (step s (t,r,.remove x (PublishedAddWinsPriorityQueue.observed s x))) =
      (elements s).erase x := by
  ext y
  simp only [Finset.mem_erase]
  rw [← not_iff_not,← priority_none_iff,not_and_or,← priority_none_iff,priority_remove]
  by_cases equal : y = x <;> simp [equal]

/-- The local extraction returns the actual observed maximum, clears that
identity and preserves every acquired attachment (disabled records included). -/
theorem prepared_remove_effect (s : State) (t r x : Nat) (p : Int)
    (selected : getMax s = some (x,p)) :
    prepareRmvMax s t r = some ((t,r,.remove x
      (PublishedAddWinsPriorityQueue.observed s x)),(x,p)) ∧
    priority (step s (t,r,.remove x (PublishedAddWinsPriorityQueue.observed s x))) x = none ∧
    (step s (t,r,.remove x (PublishedAddWinsPriorityQueue.observed s x))).increments = s.increments := by
  exact ⟨by simp [prepareRmvMax,selected],by simp [priority_remove],rfl⟩

/-- Maximum extraction's emitted event satisfies the SAME actual source
Remove preparation rule. Global event freshness remains an execution premise. -/
theorem prepared_remove_issued (s : State) (t r x : Nat) (p : Int)
    (selected : getMax s = some (x,p)) :
    generation.CanIssue (t,r,.remove x (PublishedAddWinsPriorityQueue.observed s x)) s := by
  obtain ⟨member,_,_⟩ := getMax_sound s x p selected
  obtain ⟨b,hb,key⟩ := Finset.mem_image.mp member
  obtain ⟨known,alive⟩ := Finset.mem_filter.mp hb
  have live : b.1 ∈ PublishedAddWinsPriorityQueue.liveTags s :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨b,known,rfl⟩),alive⟩
  have sourceMember : x ∈ PublishedAddWinsPriorityQueue.liveElements s :=
    Finset.mem_image.mpr ⟨b.1,live,key⟩
  have present : PublishedAddWinsPriorityQueue.lookup s x = true := decide_eq_true sourceMember
  simp [generation,prepare,PublishedAddWinsPriorityQueue.requestOf,
    PublishedAddWinsPriorityQueue.prepare,Op.time,Op.rep,Op.op,present]

theorem effects_commute (a b : Event) : D.toUpdateSig.commutes a b :=
  PublishedAddWinsPriorityQueue.effects_commute a b

#print axioms priority_selected_record
#print axioms getMax_sound
#print axioms prepared_remove_issued
end Sal.MRDTs.Instances.PriorityQueueSameRecord
