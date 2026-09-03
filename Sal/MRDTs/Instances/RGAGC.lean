import Sal.MRDTs.Framework.StateGC
import Sal.MRDTs.Instances.RGASequential

/-!
# Continuation-safe compaction for tombstone RGA

The public issuance policy permits a fresh insertion to name any previously
inserted identifier as its anchor, even after that identifier was deleted.
Consequently a collector cannot erase a dead identifier merely because its
deletion is stable: the identifier and its parent remain continuation state.

This module packages a lossless representation quotient that does not change
that policy.  Honest RGA insertions satisfy `timestamp = id`, so the
compact state stores one `(id, parent)` pair rather than the redundant
`(timestamp, parent, id)` triple.  It also stores the usually-small live set
rather than the graveyard.  Collection is lossless and preserves subsequent
updates and ternary merges.  It is representation compaction, not deleted-ID
reclamation; the negative SPOT at the end states why that distinction is
load-bearing.
-/

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.RGA.GC

open Sal.MRDTs.Foundation
open Classical

/-- Compact insertion metadata: the inserted identifier and its parent. -/
abbrev ParentEntry := ℕ × ℕ

structure PackedState where
  parents : Finset ParentEntry
  live : Finset ℕ
deriving DecidableEq

def parentEntry (e : RGAEntry) : ParentEntry := (e.2.2, e.2.1)

def birthEntry (p : ParentEntry) : RGAEntry := (p.1, p.2, p.1)

def birthIds (q : BirthGraveState) : Finset ℕ :=
  q.adds.image (fun e => e.2.2)

def parentIds (q : PackedState) : Finset ℕ :=
  q.parents.image Prod.fst

/-- Reachable birth/grave states satisfy precisely the invariants used by the
packing quotient: an insertion's timestamp is its identifier, and every grave
has a corresponding birth. -/
structure BirthGraveWellFormed (q : BirthGraveState) : Prop where
  timestamp_eq_id : ∀ e ∈ q.adds, e.1 = e.2.2
  grave_has_birth : q.grave ⊆ birthIds q

def pack (q : BirthGraveState) : PackedState where
  parents := q.adds.image parentEntry
  live := birthIds q \ q.grave

def unpack (q : PackedState) : BirthGraveState where
  adds := q.parents.image birthEntry
  grave := parentIds q \ q.live

/-- A simple machine-word model for the two finite encodings.  It counts the
three natural-number fields of every raw birth and every grave identifier,
versus two fields per packed parent edge and one per live identifier. -/
def rawWords (q : BirthGraveState) : ℕ :=
  3 * q.adds.card + q.grave.card

def packedWords (q : PackedState) : ℕ :=
  2 * q.parents.card + q.live.card

theorem packedWords_pack_le (q : BirthGraveState) :
    packedWords (pack q) ≤ rawWords q := by
  have parentsLe : (pack q).parents.card ≤ q.adds.card := by
    exact Finset.card_image_le
  have liveBirthLe : (pack q).live.card ≤ (birthIds q).card := by
    exact Finset.card_le_card Finset.sdiff_subset
  have birthLe : (birthIds q).card ≤ q.adds.card := by
    exact Finset.card_image_le
  simp only [packedWords, rawWords]
  omega

theorem packedWords_pack_lt_of_grave (q : BirthGraveState)
    (deleted : q.grave.Nonempty) :
    packedWords (pack q) < rawWords q := by
  have le := packedWords_pack_le q
  have positive : 0 < q.grave.card := Finset.card_pos.mpr deleted
  have parentsLe : (pack q).parents.card ≤ q.adds.card := Finset.card_image_le
  have liveBirthLe : (pack q).live.card ≤ (birthIds q).card :=
    Finset.card_le_card Finset.sdiff_subset
  have birthLe : (birthIds q).card ≤ q.adds.card := Finset.card_image_le
  simp only [packedWords, rawWords] at le ⊢
  omega

theorem parentIds_pack (q : BirthGraveState) :
    parentIds (pack q) = birthIds q := by
  ext id
  constructor
  · intro member
    obtain ⟨p, pMember, pId⟩ := Finset.mem_image.mp member
    obtain ⟨e, eMember, eParent⟩ := Finset.mem_image.mp pMember
    apply Finset.mem_image.mpr
    refine ⟨e, eMember, ?_⟩
    simpa [parentEntry] using pId ▸ congrArg Prod.fst eParent
  · intro member
    obtain ⟨e, eMember, eId⟩ := Finset.mem_image.mp member
    apply Finset.mem_image.mpr
    refine ⟨parentEntry e, Finset.mem_image.mpr ⟨e, eMember, rfl⟩, ?_⟩
    simpa [parentEntry] using eId

theorem unpack_pack (q : BirthGraveState) (wf : BirthGraveWellFormed q) :
    unpack (pack q) = q := by
  have addsEq : (unpack (pack q)).adds = q.adds := by
    ext e
    constructor
    · intro member
      simp only [unpack, Finset.mem_image] at member
      obtain ⟨p, pMember, rfl⟩ := member
      simp only [pack, Finset.mem_image] at pMember
      obtain ⟨source, sourceMember, parentEq⟩ := pMember
      have timeEq := wf.timestamp_eq_id source sourceMember
      have sourceEq : birthEntry (parentEntry source) = source := by
        rcases source with ⟨ts, anchor, id⟩
        simp [birthEntry, parentEntry] at timeEq ⊢
        exact timeEq.symm
      rw [← parentEq, sourceEq]
      exact sourceMember
    · intro member
      refine Finset.mem_image.mpr ⟨parentEntry e, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨e, member, rfl⟩
      · have timeEq := wf.timestamp_eq_id e member
        rcases e with ⟨ts, anchor, id⟩
        simp [birthEntry, parentEntry] at timeEq ⊢
        exact timeEq.symm
  have graveEq : (unpack (pack q)).grave = q.grave := by
    ext id
    change id ∈ parentIds (pack q) \ (birthIds q \ q.grave) ↔ id ∈ q.grave
    rw [Finset.mem_sdiff, parentIds_pack]
    constructor
    · rintro ⟨inBirth, notOutside⟩
      by_contra notGrave
      exact notOutside (Finset.mem_sdiff.mpr ⟨inBirth, notGrave⟩)
    · intro grave
      exact ⟨wf.grave_has_birth grave, fun outside =>
        (Finset.mem_sdiff.mp outside).2 grave⟩
  cases q
  exact congrArg₂ BirthGraveState.mk addsEq graveEq

theorem unpack_wellFormed (q : PackedState) :
    BirthGraveWellFormed (unpack q) := by
  constructor
  · intro e member
    simp only [unpack, Finset.mem_image] at member
    obtain ⟨p, _, rfl⟩ := member
    simp [birthEntry]
  · intro id grave
    simp only [unpack, Finset.mem_sdiff] at grave
    obtain ⟨idMember, _⟩ := grave
    simp only [parentIds, Finset.mem_image] at idMember
    obtain ⟨p, parentMember, rfl⟩ := idMember
    exact Finset.mem_image.mpr ⟨birthEntry p,
      Finset.mem_image.mpr ⟨p, parentMember, rfl⟩, by simp [birthEntry]⟩

/-- The compact interpreter admits an uncollected finite state at startup and
a packed state after collection or any subsequent operation. -/
inductive CompactState where
  | raw (state : BirthGraveState)
  | packed (state : PackedState)
deriving DecidableEq

def materialize : CompactState → BirthGraveState
  | .raw q => q
  | .packed q => unpack q

def normalize (q : BirthGraveState) : CompactState := .packed (pack q)

theorem materialize_normalize (q : BirthGraveState)
    (wf : BirthGraveWellFormed q) : materialize (normalize q) = q := by
  exact unpack_pack q wf

def step (q : BirthGraveState) (e : Op RGAOp) : BirthGraveState :=
  birthGraveMachine.step q e

def merge (l a b : BirthGraveState) : BirthGraveState where
  adds := l.adds ∪ a.adds ∪ b.adds
  grave := l.grave ∪ a.grave ∪ b.grave

theorem birthGraveRel_step {s : RGAM.State} {q : BirthGraveState}
    (represented : birthGraveRel s q) (e : Op RGAOp) :
    birthGraveRel (RGAM.update s e) (step q e) := by
  rcases e with ⟨ts, replica, op⟩
  cases op with
  | addAfter anchor id =>
      constructor
      · intro p
        change (s.1 p || decide (p = (ts, anchor, id))) =
          decide (p ∈ insert (ts, anchor, id) q.adds)
        rw [represented.1 p]
        simp [Bool.or_comm]
      · intro x
        simpa [RGAM, rgaUpdate, step, birthGraveMachine] using represented.2 x
  | remove id =>
      constructor
      · intro p
        simpa [RGAM, rgaUpdate, step, birthGraveMachine] using represented.1 p
      · intro x
        change (s.2 x || decide (x = id)) = decide (x ∈ insert id q.grave)
        rw [represented.2 x]
        simp [eq_comm, Bool.or_comm]

theorem wellFormed_step {s : RGAM.State} {q : BirthGraveState}
    (represented : birthGraveRel s q) (wf : BirthGraveWellFormed q)
    {e : Op RGAOp} (canIssue : applicable e s) :
    BirthGraveWellFormed (step q e) := by
  rcases e with ⟨ts, replica, op⟩
  cases op with
  | addAfter anchor id =>
      rcases canIssue with ⟨idEq, _, _, _, _⟩
      constructor
      · intro p member
        simp only [step, birthGraveMachine, Finset.mem_insert] at member
        rcases member with rfl | old
        · simpa using idEq.symm
        · exact wf.timestamp_eq_id p old
      · intro x grave
        apply Finset.mem_image.mpr
        obtain ⟨birth, birthMember, birthId⟩ :=
          Finset.mem_image.mp (wf.grave_has_birth grave)
        exact ⟨birth, Finset.mem_insert_of_mem birthMember, birthId⟩
  | remove deletedId =>
      obtain ⟨⟨birthTs, birthParent, present⟩, _⟩ := canIssue
      constructor
      · exact wf.timestamp_eq_id
      · intro x member
        simp only [step, birthGraveMachine, Finset.mem_insert] at member
        rcases member with newest | old
        · subst x
          have birthMember : (birthTs, birthParent, deletedId) ∈ q.adds := by
            have := represented.1 (birthTs, birthParent, deletedId)
            rw [this] at present
            simpa using present
          exact Finset.mem_image.mpr
            ⟨(birthTs, birthParent, deletedId), birthMember, rfl⟩
        · exact wf.grave_has_birth old

theorem birthGraveRel_merge {sl sa sb : RGAM.State}
    {l a b : BirthGraveState}
    (hl : birthGraveRel sl l) (ha : birthGraveRel sa a)
    (hb : birthGraveRel sb b) :
    birthGraveRel (RGAM.merge sl sa sb) (merge l a b) := by
  constructor
  · intro p
    change (sl.1 p || (sa.1 p || sb.1 p)) =
      decide (p ∈ l.adds ∪ a.adds ∪ b.adds)
    rw [hl.1 p, ha.1 p, hb.1 p]
    simp
  · intro id
    change (sl.2 id || (sa.2 id || sb.2 id)) =
      decide (id ∈ l.grave ∪ a.grave ∪ b.grave)
    rw [hl.2 id, ha.2 id, hb.2 id]
    simp

theorem wellFormed_merge {l a b : BirthGraveState}
    (hl : BirthGraveWellFormed l) (ha : BirthGraveWellFormed a)
    (hb : BirthGraveWellFormed b) :
    BirthGraveWellFormed (merge l a b) := by
  constructor
  · intro e member
    simp only [merge, Finset.mem_union] at member
    rcases member with (left | middle) | right
    · exact hl.timestamp_eq_id e left
    · exact ha.timestamp_eq_id e middle
    · exact hb.timestamp_eq_id e right
  · intro id member
    simp only [merge, Finset.mem_union] at member
    rcases member with (left | middle) | right
    · obtain ⟨e, eMember, rfl⟩ := Finset.mem_image.mp (hl.grave_has_birth left)
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ eMember), rfl⟩
    · obtain ⟨e, eMember, rfl⟩ := Finset.mem_image.mp (ha.grave_has_birth middle)
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ eMember), rfl⟩
    · obtain ⟨e, eMember, rfl⟩ := Finset.mem_image.mp (hb.grave_has_birth right)
      exact Finset.mem_image.mpr
        ⟨e, Finset.mem_union_right _ eMember, rfl⟩

def Represents (compact : CompactState) (full : RGAM.State) : Prop :=
  birthGraveRel full (materialize compact) ∧
    BirthGraveWellFormed (materialize compact)

def collect (_ : Unit) (compact : CompactState) : CompactState :=
  normalize (materialize compact)

def compactUpdate (compact : CompactState) (e : Op RGAOp) : CompactState :=
  normalize (step (materialize compact) e)

def compactMerge (cl ca cb : CompactState) : CompactState :=
  normalize (merge (materialize cl) (materialize ca) (materialize cb))

noncomputable def compactQuery (compact : CompactState) (_ : Unit) : List ℕ :=
  sequence (materialize compact)

/-- Representation-changing state-GC certificate for tombstone RGA.  The
evidence is trivial because this quotient uses only invariants already
maintained by honest issuance; no stability frontier authorizes identifier
erasure. -/
noncomputable def certificate : StateGCCertificate RGAM generation where
  CompactState := CompactState
  Evidence := Unit
  Represents := Represents
  EvidenceValid := fun _ _ _ => True
  Compatible := fun _ _ => True
  init := .raw ⟨∅, ∅⟩
  collect := collect
  update := compactUpdate
  merge := compactMerge
  query := compactQuery
  init_represents := by
    constructor
    · constructor <;> intro x <;> simp [RGAM, materialize]
    · constructor <;> simp [birthIds, materialize]
  collect_represents := by
    intro evidence compact full represented _
    refine ⟨?_, unpack_wellFormed _⟩
    simpa [collect, materialize_normalize _ represented.2] using represented.1
  update_represents := by
    intro compact full op represented issued
    have wf := wellFormed_step represented.1 represented.2 issued
    refine ⟨?_, ?_⟩
    · simpa [compactUpdate, materialize_normalize _ wf] using
        birthGraveRel_step represented.1 op
    · simpa [compactUpdate, materialize_normalize _ wf] using wf
  merge_represents := by
    intro cl ca cb l a b representedL representedA representedB _
    have wf := wellFormed_merge representedL.2 representedA.2 representedB.2
    refine ⟨?_, ?_⟩
    · simpa [compactMerge, materialize_normalize _ wf] using
        birthGraveRel_merge representedL.1 representedA.1 representedB.1
    · simpa [compactMerge, materialize_normalize _ wf] using wf
  query_correct := by
    intro compact full represented query
    exact (read_eq_sequence_of_birthGraveRel represented.1).symm

/-! ## Negative oracle: dead anchors are continuation state -/

def eraseId (id : ℕ) (q : BirthGraveState) : BirthGraveState where
  adds := q.adds.filter (fun e => e.2.2 ≠ id)
  grave := q.grave.erase id

def deadAnchorState : BirthGraveState where
  adds := {(1, 0, 1), (2, 0, 2)}
  grave := {1}

def futureAfterDeadAnchor : Op RGAOp := (3, 1, .addAfter 1 3)

/-- The unordered live projection used by the negative oracle.  Equality here
is intentionally weaker than the real ordered query, making the refutation
strictly harder rather than self-fulfilling. -/
def liveIds (q : BirthGraveState) : Finset ℕ := birthIds q \ q.grave

/-- PASS: naïve erasure preserves the current live identifiers. -/
theorem erase_dead_anchor_current_live_ids :
    liveIds (eraseId 1 deadAnchorState) = liveIds deadAnchorState := by
  decide

def finiteState (q : BirthGraveState) : RGAM.State :=
  (fun e => decide (e ∈ q.adds), fun id => decide (id ∈ q.grave))

theorem finiteState_rel (q : BirthGraveState) :
    birthGraveRel (finiteState q) q := ⟨fun _ => rfl, fun _ => rfl⟩

/-- PASS: the future operation is honestly issuable while the dead anchor is
retained. -/
theorem future_after_dead_anchor_applicable :
    applicable futureAfterDeadAnchor (finiteState deadAnchorState) := by
  change 3 = 3 ∧
    (1 = 0 ∨ ∃ ts parent, ts < 3 ∧
      (finiteState deadAnchorState).1 (ts, parent, 1) = true) ∧
    (∀ anchor id, (finiteState deadAnchorState).1 (3, anchor, id) = false) ∧
    (∀ ts anchor, (finiteState deadAnchorState).1 (ts, anchor, 3) = false) ∧
    (finiteState deadAnchorState).2 3 = false
  refine ⟨rfl, Or.inr ⟨1, 0, by omega, ?_⟩, ?_, ?_, ?_⟩
  · simp [finiteState, deadAnchorState]
  · intro anchor id
    simp [finiteState, deadAnchorState]
  · intro ts anchor
    simp [finiteState, deadAnchorState]
  · simp [finiteState, deadAnchorState]

/-- FAIL companion: present-read equivalence does not preserve issuance.  The
same future operation is rejected once the deleted anchor is erased. -/
theorem erase_dead_anchor_breaks_future_issuance :
    ¬ applicable futureAfterDeadAnchor
      (finiteState (eraseId 1 deadAnchorState)) := by
  intro issued
  simp only [futureAfterDeadAnchor, applicable] at issued
  rcases issued.2.1 with root | ⟨ts, parent, earlier, present⟩
  · omega
  · simp [finiteState, eraseId, deadAnchorState] at present

#print axioms certificate
#print axioms erase_dead_anchor_breaks_future_issuance

end Sal.MRDTs.Instances.RGA.GC
