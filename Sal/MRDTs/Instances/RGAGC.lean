import Sal.MRDTs.Framework.StateGC
import Sal.MRDTs.Instances.RGASequential

/-!
# Continuation-safe representation conversion for RGA

Both representations store `(identifier, anchor)` birth pairs. The alternate
representation stores live identifiers instead of graves; it saves words when
the live set is smaller than the graveyard. Conversion is lossless under the
invariant that every grave has a birth, and preserves issued updates, ternary
merges, and queries. It does not reclaim birth identifiers.

Issuance rejects insertion after an observed deleted anchor. The controls at
the end check this before and after erasure; they do not prove a general
impossibility of identifier reclamation.
-/

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.RGA.GC

open Sal.MRDTs.Foundation
open Classical

structure PackedState where
  parents : Finset RGAEntry
  live : Finset ℕ
deriving DecidableEq

def birthIds (q : BirthGraveState) : Finset ℕ :=
  q.adds.image (fun e => e.1)

def parentIds (q : PackedState) : Finset ℕ :=
  q.parents.image Prod.fst

/-- Every grave has a corresponding birth. Timestamp and identifier are the
same field by construction, so no equality invariant is needed. -/
structure BirthGraveWellFormed (q : BirthGraveState) : Prop where
  grave_has_birth : q.grave ⊆ birthIds q

def pack (q : BirthGraveState) : PackedState where
  parents := q.adds
  live := birthIds q \ q.grave

def unpack (q : PackedState) : BirthGraveState where
  adds := q.parents
  grave := parentIds q \ q.live

/-- Both encodings use two words per birth, then one per grave or live ID. -/
def rawWords (q : BirthGraveState) : ℕ :=
  2 * q.adds.card + q.grave.card

def packedWords (q : PackedState) : ℕ :=
  2 * q.parents.card + q.live.card

theorem packedWords_pack_le (q : BirthGraveState)
    (smaller : (pack q).live.card ≤ q.grave.card) :
    packedWords (pack q) ≤ rawWords q := by
  simp only [packedWords, rawWords, pack] at *
  omega

theorem packedWords_pack_lt_of_live_lt_grave (q : BirthGraveState)
    (smaller : (pack q).live.card < q.grave.card) :
    packedWords (pack q) < rawWords q := by
  simp only [packedWords, rawWords, pack] at *
  omega

/-- Conversion can grow an all-live state: there is no redundant timestamp
left to pay for the new live-ID set. -/
theorem all_live_conversion_grows :
    let q : BirthGraveState := ⟨{(1, 0), (2, 0)}, ∅⟩
    rawWords q < packedWords (pack q) := by decide

/-- With both identifiers deleted, replacing graves by live IDs saves words. -/
theorem all_deleted_conversion_shrinks :
    let q : BirthGraveState := ⟨{(1, 0), (2, 0)}, {1, 2}⟩
    packedWords (pack q) < rawWords q := by decide

theorem parentIds_pack (q : BirthGraveState) :
    parentIds (pack q) = birthIds q := rfl

theorem unpack_pack (q : BirthGraveState) (wf : BirthGraveWellFormed q) :
    unpack (pack q) = q := by
  have addsEq : (unpack (pack q)).adds = q.adds := rfl
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
  · intro id grave
    simp only [unpack, Finset.mem_sdiff] at grave
    obtain ⟨idMember, _⟩ := grave
    simp only [parentIds, Finset.mem_image] at idMember
    obtain ⟨p, parentMember, rfl⟩ := idMember
    exact Finset.mem_image.mpr ⟨p, parentMember, rfl⟩

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
  | addAfter anchor =>
      constructor
      · intro p
        change (s.1 p || decide (p = (ts, anchor))) =
          decide (p ∈ insert (ts, anchor) q.adds)
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
  | addAfter anchor =>
      constructor
      · intro x grave
        apply Finset.mem_image.mpr
        obtain ⟨birth, birthMember, birthId⟩ :=
          Finset.mem_image.mp (wf.grave_has_birth grave)
        exact ⟨birth, Finset.mem_insert_of_mem birthMember, birthId⟩
  | remove deletedId =>
      obtain ⟨⟨birthParent, present⟩, _⟩ := canIssue
      constructor
      · intro x member
        simp only [step, birthGraveMachine, Finset.mem_insert] at member
        rcases member with newest | old
        · subst x
          have birthMember : (deletedId, birthParent) ∈ q.adds := by
            have := represented.1 (deletedId, birthParent)
            rw [this] at present
            simpa using present
          exact Finset.mem_image.mpr
            ⟨(deletedId, birthParent), birthMember, rfl⟩
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

/-- Representation-changing state-GC certificate for RGA.  The
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
  adds := q.adds.filter (fun e => e.1 ≠ id)
  grave := q.grave.erase id

def deadAnchorState : BirthGraveState where
  adds := {(1, 0), (2, 0)}
  grave := {1}

def futureAfterDeadAnchor : Op RGAOp := (3, 1, .addAfter 1)

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

/-- PASS: an issuer may not generate an insertion after an anchor whose
deletion it has observed, even though the implementation retains that anchor
to integrate operations generated concurrently with the deletion. -/
theorem future_after_dead_anchor_not_applicable :
    ¬ applicable futureAfterDeadAnchor (finiteState deadAnchorState) := by
  intro issued
  simp only [futureAfterDeadAnchor, applicable] at issued
  rcases issued.1 with root | ⟨live, _⟩
  · omega
  · simp [finiteState, deadAnchorState] at live

/-- Negative control: erasing the retained anchor also rejects the operation,
but for lack of allocation history rather than because it is tombstoned. -/
theorem erase_dead_anchor_rejects_future_issuance :
    ¬ applicable futureAfterDeadAnchor
      (finiteState (eraseId 1 deadAnchorState)) := by
  intro issued
  simp only [futureAfterDeadAnchor, applicable] at issued
  rcases issued.1 with root | ⟨_, earlier, parent, present⟩
  · omega
  · simp [finiteState, eraseId, deadAnchorState] at present

#print axioms certificate
#print axioms future_after_dead_anchor_not_applicable
#print axioms erase_dead_anchor_rejects_future_issuance

end Sal.MRDTs.Instances.RGA.GC
