import Sal.MRDTs.Instances.NotionCoreInvariant
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! Derive source-origin safety from semantic address uniqueness and accepted
source ownership. The inactive empty title root cannot alias an active origin.
No manual observation or transition equality is a premise. JavaScript extraction
and source-allocation establishment of freshness remain separate obligations.
-/
namespace Sal.MRDTs.Instances.NotionCoreSourceGuards
open NotionCoreSpec (Address Slot)
open NotionCoreSource (Atom Block)
open NotionCoreSourceDocument (Document project owner OriginSafe)
open NotionCoreInvariant (addresses)

private theorem active_project_member (block : Block) (origin : Address)
    (member : origin ∈ block.active.traversal) :
    origin ∈ block.project.slots.map Slot.address := by
  cases shape : block.shape <;>
    simp [Block.project, shape, NotionCoreSourceDocument.active_addresses, member]

private theorem attached_root_not_active (block : Block) (inst : Nat)
    (unique : (block.project.slots.map Slot.address).Nodup)
    (attached : block.shape = .attached inst) :
    (NotionCoreSpec.root inst).address ∉ block.active.traversal := by
  have shape : ((NotionCoreSpec.root inst).address :: block.active.traversal).Nodup := by
    simpa only [Block.project, attached, List.map_cons,
      NotionCoreSourceDocument.active_addresses] using unique
  exact (List.nodup_cons.mp shape).1

/-- Global retained-address uniqueness gives a unique active block owner,
including when the origin is a tombstone or an interval anchor. -/
theorem active_owner_unique {doc : Document} {left right : Block} {origin : Address}
    (unique : (addresses (project doc)).Nodup)
    (leftMember : left ∈ doc) (rightMember : right ∈ doc)
    (leftActive : origin ∈ left.active.traversal)
    (rightActive : origin ∈ right.active.traversal) : left = right := by
  obtain ⟨pre, post, shape⟩ := List.append_of_mem leftMember
  subst doc
  have focused := NotionCoreSpec.address_focus (project pre) (project post)
    left.project origin
    (by simpa only [addresses, project, List.map_append, List.map_cons] using unique)
    (active_project_member left origin leftActive)
  by_contra different
  have outside : right ∈ pre ++ post := by
    rcases List.mem_append.mp rightMember with member | member
    · exact List.mem_append_left _ member
    · rcases List.mem_cons.mp member with equal | member
      · exact False.elim (different equal.symm)
      · exact List.mem_append_right _ member
  have projectedOutside : right.project ∈ project pre ++ project post := by
    simpa only [project, ← List.map_append] using List.mem_map.mpr ⟨right,outside,rfl⟩
  exact focused.2 right.project projectedOutside (active_project_member right origin rightActive)

/-- An active origin cannot be the otherwise unused title root of any attached
block. The proof handles its own block separately from all other blocks;
global address uniqueness excludes both collisions. -/
theorem originSafe_of_active {doc : Document} {source : Block} {origin : Address}
    (unique : (addresses (project doc)).Nodup)
    (sourceMember : source ∈ doc) (active : origin ∈ source.active.traversal) :
    OriginSafe doc origin := by
  obtain ⟨pre, post, shape⟩ := List.append_of_mem sourceMember
  subst doc
  have present := active_project_member source origin active
  have structural := NotionCoreSpec.address_focus (project pre) (project post)
    source.project origin
    (by simpa only [addresses, project, List.map_append, List.map_cons] using unique) present
  intro block member inst attached collision
  by_cases same : block = source
  · subst block
    have absent := attached_root_not_active source inst structural.1 attached
    exact absent (collision ▸ active)
  · have outside : block ∈ pre ++ post := by
      rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ member
      · rcases List.mem_cons.mp member with same' | member
        · exact False.elim (same same')
        · exact List.mem_append_right _ member
    have projectedOutside : block.project ∈ project pre ++ project post := by
      simpa only [project, ← List.map_append] using
        List.mem_map.mpr ⟨block, outside, rfl⟩
    have rootPresent : (NotionCoreSpec.root inst).address ∈ block.project.slots.map Slot.address := by
      simp [Block.project, attached]
    exact structural.2 block.project projectedOutside (collision ▸ rootPresent)

/-- `owner = some` supplies the active membership needed by the safety proof;
it does not require a live character, so tombstones and boundary anchors work. -/
theorem originSafe_of_owner {doc : Document} {source : Block} {origin : Address}
    (unique : (addresses (project doc)).Nodup)
    (owned : owner doc origin = some source) : OriginSafe doc origin := by
  apply originSafe_of_active unique (List.mem_of_find?_eq_some owned)
  simpa only [NotionCoreSourceDocument.owns, decide_eq_true_eq] using List.find?_some owned

/-- Projection guards require unique block names and retained addresses;
accepted source ownership supplies the origin premise. -/
theorem accepted_guard_of_unique {doc next : Document} (command : NotionCoreSourceDocument.Command)
    (names : (doc.map Block.id).Nodup)
    (unique : (addresses (project doc)).Nodup)
    (accepted : NotionCoreSourceDocument.step doc command = some next) :
    NotionCoreSourceDocument.Guard doc command := by
  refine ⟨names, ?_⟩
  cases command with
  | create id inst after => trivial
  | delete targets => trivial
  | insert origin fresh =>
      cases owned : owner doc origin with
      | none => simp [NotionCoreSourceDocument.step, owned] at accepted
      | some source => exact originSafe_of_owner unique owned
  | split origin marker target =>
      cases owned : owner doc origin with
      | none => simp [NotionCoreSourceDocument.step, owned] at accepted
      | some source => exact originSafe_of_owner unique owned

/-- Accepted insert/split commands derive their source address guard from the
projected invariant. Creation/deletion require no address-origin guard. -/
theorem accepted_guard {doc next : Document} (command : NotionCoreSourceDocument.Command)
    (wf : NotionCoreSpec.WellFormed (project doc))
    (accepted : NotionCoreSourceDocument.step doc command = some next) :
    NotionCoreSourceDocument.Guard doc command :=
  accepted_guard_of_unique command
    (by simpa only [NotionCoreSourceDocument.project_ids] using wf.1) wf.2.1 accepted

/-- The materialized source's step projection needs no manually supplied
`OriginSafe` premise on invariant inputs. Acceptance derives origin membership
and global address uniqueness proves the required separation. -/
theorem step_sound {doc next : Document} (command : NotionCoreSourceDocument.Command)
    (wf : NotionCoreSpec.WellFormed (project doc))
    (accepted : NotionCoreSourceDocument.step doc command = some next) :
    NotionCoreSpec.step (project doc) command.semantic = some (project next) := by
  have guard := accepted_guard command wf accepted
  exact NotionCoreSourceDocument.step_sound command guard.1 guard.2 accepted

/-- Source reachability with semantic freshness/shape admission and actual
accepted source transitions. No `OriginSafe` or next-state invariant is a
guard. Establishing semantic admission from the published issuer remains open. -/
inductive Reach : Document → Prop where
  | init : Reach []
  | step {doc next : Document} {command : NotionCoreSourceDocument.Command} :
      Reach doc → NotionCoreInvariant.Admissible (project doc) command.semantic →
      NotionCoreSourceDocument.step doc command = some next → Reach next

theorem reachable_invariants {doc : Document} (reachable : Reach doc) :
    NotionCoreInvariant.Reach (project doc) ∧ NotionCoreSpec.WellFormed (project doc) := by
  induction reachable with
  | init => exact ⟨.init, NotionCoreInvariant.reachable_wellFormed .init⟩
  | @step doc next command _ guard accepted ih =>
      have projected := step_sound command ih.2 accepted
      have nextReach := NotionCoreInvariant.Reach.step ih.1 guard projected
      exact ⟨nextReach, NotionCoreInvariant.reachable_wellFormed nextReach⟩

theorem reachable_wellFormed {doc : Document} (reachable : Reach doc) :
    NotionCoreSpec.WellFormed (project doc) := (reachable_invariants reachable).2

theorem reachable_step_sound {doc next : Document} (command : NotionCoreSourceDocument.Command)
    (reachable : Reach doc)
    (accepted : NotionCoreSourceDocument.step doc command = some next) :
    NotionCoreSpec.step (project doc) command.semantic = some (project next) :=
  step_sound command (reachable_wellFormed reachable) accepted

private def hiddenAtom : Atom := ⟨(0, .event (0, 1)), .text 97 true⟩
private def liveAtom : Atom := ⟨(0, .event (0, 2)), .text 98 false⟩
private def attachedBlock : Block :=
  ⟨10, .attached 99, ⟨(0, .event (1, 10)), [hiddenAtom, liveAtom]⟩⟩

private theorem attached_unique : (addresses (project [attachedBlock])).Nodup := by decide

/-- PASS+FAIL: hidden character ownership derives source safety, whereas the
inactive own-title root is not a valid active origin and violates that guard. -/
theorem hidden_origin_safety_control :
    OriginSafe [attachedBlock] hiddenAtom.address ∧
    ¬ OriginSafe [attachedBlock] (NotionCoreSpec.root 99).address := by
  refine ⟨originSafe_of_owner (source := attachedBlock) attached_unique (by decide), ?_⟩
  intro safe
  exact safe attachedBlock (by simp) 99 rfl rfl

/-- The derived condition is sensitive to active ownership, not visibility or
mere membership among projected slots. -/
theorem owner_control :
    owner [attachedBlock] hiddenAtom.address = some attachedBlock ∧
    owner [attachedBlock] (NotionCoreSpec.root 99).address = none ∧
    owner [attachedBlock] hiddenAtom.address ≠ none := by decide

/-- A source insertion after the hidden character is effective and places X
before b. Attempting the inactive own-root origin is rejected. Expectations
are hand-derived from ordinary after-origin editing. -/
theorem hidden_insert_control :
    ((NotionCoreSourceDocument.step [attachedBlock]
      (.insert hiddenAtom.address [⟨(0, .event (2, 10)), .text 88 false⟩])).map
        (fun doc => NotionCoreSpec.view (project doc))) = some [(10, [88, 98])] ∧
    ((NotionCoreSourceDocument.step [attachedBlock]
      (.insert hiddenAtom.address [⟨(0, .event (2, 10)), .text 88 false⟩])).map
        (fun doc => NotionCoreSpec.view (project doc))) ≠ some [(10, [98, 88])] ∧
    NotionCoreSourceDocument.step [attachedBlock]
      (.insert (NotionCoreSpec.root 99).address [⟨(0, .event (2, 10)), .text 88 false⟩]) = none := by decide

/-- The source reach relation has a concrete allocated-root execution; its
projection is an ordinary block and is distinct from the empty document. -/
theorem reachable_create_control :
    Reach [NotionCoreSourceDocument.freshBlock 10 0] ∧
    NotionCoreSpec.view (project [NotionCoreSourceDocument.freshBlock 10 0]) = [(10, [])] ∧
    NotionCoreSpec.view (project [NotionCoreSourceDocument.freshBlock 10 0]) ≠ [] := by
  have run : Reach [NotionCoreSourceDocument.freshBlock 10 0] :=
    .step (command := .create 10 0 none) .init
      (.create_front [] 10 0 (by decide) (by decide)) (by decide)
  exact ⟨run, by decide, by decide⟩

#print axioms reachable_invariants
#print axioms originSafe_of_active
#print axioms step_sound
end Sal.MRDTs.Instances.NotionCoreSourceGuards
