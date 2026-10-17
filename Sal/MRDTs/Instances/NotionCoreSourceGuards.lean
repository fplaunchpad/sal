import Sal.MRDTs.Instances.NotionCoreInvariant
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! Derive the source projection guards from semantic address uniqueness.
Every slice address of a block, dead title roots included, is owned by that
block, so ownership agrees with the specification without a separate origin
condition. No manual observation or transition equality is a premise.
JavaScript extraction and source-allocation establishment of freshness remain
separate obligations.
-/
namespace Sal.MRDTs.Instances.NotionCoreSourceGuards
open NotionCoreSpec (Address Slot)
open NotionCoreSource (Atom Slice Block)
open NotionCoreSourceDocument (Document project owner)
open NotionCoreInvariant (addresses)

theorem project_member (block : Block) (origin : Address)
    (member : origin ∈ block.traversal) :
    origin ∈ block.project.slots.map Slot.address := by
  simpa [Block.project] using member

/-- Global retained-address uniqueness gives a unique owning block,
including when the origin is a tombstone, a dead title root or an interval
anchor. -/
theorem owner_unique {doc : Document} {left right : Block} {origin : Address}
    (unique : (addresses (project doc)).Nodup)
    (leftMember : left ∈ doc) (rightMember : right ∈ doc)
    (leftHeld : origin ∈ left.traversal)
    (rightHeld : origin ∈ right.traversal) : left = right := by
  obtain ⟨pre, post, shape⟩ := List.append_of_mem leftMember
  subst doc
  have focused := NotionCoreSpec.address_focus (project pre) (project post)
    left.project origin
    (by simpa only [addresses, project, List.map_append, List.map_cons] using unique)
    (project_member left origin leftHeld)
  by_contra different
  have outside : right ∈ pre ++ post := by
    rcases List.mem_append.mp rightMember with member | member
    · exact List.mem_append_left _ member
    · rcases List.mem_cons.mp member with equal | member
      · exact False.elim (different equal.symm)
      · exact List.mem_append_right _ member
  have projectedOutside : right.project ∈ project pre ++ project post := by
    simpa only [project, ← List.map_append] using List.mem_map.mpr ⟨right,outside,rfl⟩
  exact focused.2 right.project projectedOutside (project_member right origin rightHeld)

/-- Global address uniqueness gives address uniqueness within each block. -/
theorem block_unique {doc : Document} (unique : (addresses (project doc)).Nodup)
    {block : Block} (member : block ∈ doc) : block.traversal.Nodup := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have whole : (((project pre).flatMap fun b => b.slots.map Slot.address) ++
      (block.traversal ++
        (project post).flatMap fun b => b.slots.map Slot.address)).Nodup := by
    simpa [addresses, project, List.flatMap_append] using unique
  have middle := (List.nodup_append.mp (List.nodup_append.mp whole).2.1).1
  simpa using middle

/-- Projection guards require unique block names and retained addresses. -/
theorem accepted_guard_of_unique {doc next : Document} (command : NotionCoreSourceDocument.Command)
    (names : (doc.map Block.id).Nodup)
    (unique : (addresses (project doc)).Nodup)
    (_accepted : NotionCoreSourceDocument.step doc command = some next) :
    NotionCoreSourceDocument.Guard doc command := by
  refine ⟨names, ?_⟩
  cases command with
  | insert origin fresh => exact fun block member => block_unique unique member
  | _ => trivial

/-- Accepted commands derive their source guards from the projected
invariant. -/
theorem accepted_guard {doc next : Document} (command : NotionCoreSourceDocument.Command)
    (wf : NotionCoreSpec.WellFormed (project doc))
    (accepted : NotionCoreSourceDocument.step doc command = some next) :
    NotionCoreSourceDocument.Guard doc command :=
  accepted_guard_of_unique command
    (by simpa only [NotionCoreSourceDocument.project_ids] using wf.1) wf.2.1 accepted

/-- The materialized source's step projection needs no manually supplied
guard on invariant inputs. -/
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
private def splitBlock : Block :=
  ⟨10, 99, [⟨(99, .start), []⟩, ⟨(0, .event (1, 10)), [hiddenAtom, liveAtom]⟩]⟩

/-- PASS+FAIL: a hidden character and the dead title root are both owned by
their block; an address held by no slice has no owner. -/
theorem owner_control :
    owner [splitBlock] hiddenAtom.address = some splitBlock ∧
    owner [splitBlock] (NotionCoreSpec.root 99).address = some splitBlock ∧
    owner [splitBlock] (0, .event (5, 5)) = none ∧
    owner [splitBlock] hiddenAtom.address ≠ none := by decide

/-- A source insertion after the hidden character is effective and places X
before b; an insertion at the dead title root also lands before b, in the
dead title, and an absent origin is rejected. Expectations are hand-derived
from ordinary after-origin editing. -/
theorem hidden_insert_control :
    ((NotionCoreSourceDocument.step [splitBlock]
      (.insert hiddenAtom.address [⟨(0, .event (2, 10)), .text 88 false⟩])).map
        (fun doc => NotionCoreSpec.view (project doc))) = some [(10, [88, 98])] ∧
    ((NotionCoreSourceDocument.step [splitBlock]
      (.insert hiddenAtom.address [⟨(0, .event (2, 10)), .text 88 false⟩])).map
        (fun doc => NotionCoreSpec.view (project doc))) ≠ some [(10, [98, 88])] ∧
    ((NotionCoreSourceDocument.step [splitBlock]
      (.insert (NotionCoreSpec.root 99).address [⟨(99, .event (2, 10)), .text 88 false⟩])).map
        (fun doc => NotionCoreSpec.view (project doc))) = some [(10, [88, 98])] ∧
    NotionCoreSourceDocument.step [splitBlock]
      (.insert (0, .event (5, 5)) [⟨(0, .event (2, 10)), .text 88 false⟩]) = none := by decide

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
#print axioms owner_unique
#print axioms step_sound
end Sal.MRDTs.Instances.NotionCoreSourceGuards
