import Sal.MRDTs.Instances.NotionCoreHistory
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! History refinement of the guarded materialized source machine.
Updates remain atomic groups; queries may occur between any two groups.
This consumes physical transition projection, not an assumed answer equation.
It neither derives the guards from the published issuer nor constructs an RA
event enumeration. Extraction of this source model from JavaScript is separate.
-/
namespace Sal.MRDTs.Instances.NotionCoreSourceHistory
open Sal.MRDTs.Paper1
open NotionCoreSource (Atom Block)

/-- The physical renderer hides deleted text and split markers directly. -/
def renderedAtom (atom : Atom) : List Nat := match atom.kind with
  | .text value false => [value]
  | _ => []

/-- The rendered view lists the alive blocks, each with the visible text of
its chain's slices in order. -/
def render (doc : NotionCoreSourceDocument.Document) : NotionCoreHistory.View :=
  (doc.filter Block.alive).map fun block =>
    (block.id, block.slices.flatMap fun slice => slice.atoms.flatMap renderedAtom)

theorem atom_projection (atom : Atom) :
    NotionCoreSpec.text [atom.slot] = renderedAtom atom := by
  cases atom with
  | mk address kind => cases kind with
    | text value deleted => cases deleted <;> rfl
    | split => rfl

theorem atoms_projection (atoms : List Atom) :
    NotionCoreSpec.text (atoms.map Atom.slot) = atoms.flatMap renderedAtom := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
    change NotionCoreSpec.text ([atom.slot] ++ atoms.map Atom.slot) = _
    rw [NotionCoreSpec.text_append, atom_projection, ih]
    rfl

theorem slice_projection (slice : NotionCoreSource.Slice) :
    NotionCoreSpec.text slice.slots = slice.atoms.flatMap renderedAtom := by
  simp only [NotionCoreSource.Slice.slots, NotionCoreSpec.text_cons,
    NotionCoreSource.Slice.anchor, Bool.false_eq_true, ↓reduceIte, NotionCoreSpec.text_append,
    atoms_projection, NotionCoreSource.Slice.close, NotionCoreSpec.closeOf_visible,
    NotionCoreSpec.text_nil, List.append_nil]

theorem render_projection (doc : NotionCoreSourceDocument.Document) :
    NotionCoreSpec.view (NotionCoreSourceDocument.project doc) = render doc := by
  simp only [NotionCoreSpec.view, NotionCoreSourceDocument.project, render, List.filter_map,
    List.map_map]
  apply List.map_congr_left
  intro block _
  simp only [Function.comp_apply, NotionCoreSourceDocument.project_id,
    NotionCoreSourceDocument.project_slots, NotionCoreSource.Block.slots]
  congr 1
  induction block.slices with
  | nil => rfl
  | cons slice rest ih => simp [ih, slice_projection]

abbrev Label := SeqLabel (List NotionCoreSourceDocument.Command) Unit NotionCoreHistory.View

def semanticLabel : Label → SeqLabel NotionCoreHistory.Update Unit NotionCoreHistory.View
  | .update commands => .update (commands.map NotionCoreSourceDocument.Command.semantic)
  | .query request answer => .query request answer

def machine : HistoryMachine (List NotionCoreSourceDocument.Command) Unit NotionCoreHistory.View where
  State := NotionCoreSourceDocument.Document
  initial := []
  transition before label after := match label with
    | .update commands => NotionCoreSourceDocument.Execution before commands after
    | .query _ answer => after = before ∧ answer = render before

/-- Every intermediate answer, as well as the terminal answer, is preserved
on exactly the same ordered sequence of atomic updates and queries. -/
theorem runs_sound {before after : NotionCoreSourceDocument.Document} {labels : List Label}
    (executed : Runs machine.transition before labels after) :
    Runs NotionCoreHistory.machine.transition (NotionCoreSourceDocument.project before)
      (labels.map semanticLabel) (NotionCoreSourceDocument.project after) := by
  induction executed with
  | nil before => exact .nil _
  | @cons before mid after label labels one rest ih =>
    apply Runs.cons (t := NotionCoreSourceDocument.project after) (m := NotionCoreSourceDocument.project mid) _ ih
    cases label with
    | update commands => exact NotionCoreSourceDocument.execution_sound one
    | query request answer =>
      change mid = before ∧ answer = render before at one
      change NotionCoreSourceDocument.project mid = NotionCoreSourceDocument.project before ∧
        answer = NotionCoreSpec.view (NotionCoreSourceDocument.project before)
      exact ⟨congrArg NotionCoreSourceDocument.project one.1, one.2.trans (render_projection before).symm⟩

theorem history_sound {labels : List Label}
    (accepted : machine.toSpec.admits labels) :
    NotionCoreHistory.spec.admits (labels.map semanticLabel) := by
  obtain ⟨final, executed⟩ := accepted
  exact ⟨NotionCoreSourceDocument.project final, runs_sound executed⟩

/-- An initially empty source block accepts an atomic creation/insertion
followed by its nonempty answer. The rival empty answer is impossible. -/
def exampleCommands : List NotionCoreSourceDocument.Command :=
  [.create 0 0 none,
   .insert (0, .start) [⟨(0, .event (0, 1)), .text 97 false⟩]]

theorem source_history_control :
    machine.toSpec.admits [.update exampleCommands, .query () [(0, [97])]] ∧
    ¬ machine.toSpec.admits [.update exampleCommands, .query () [(0, [])]] := by
  have executed : NotionCoreSourceDocument.Execution [] exampleCommands
      [⟨0, 0, [⟨(0, .start), [⟨(0, .event (0, 1)), .text 97 false⟩], none⟩]⟩] := by
    apply NotionCoreSourceDocument.Execution.cons (next := [NotionCoreSourceDocument.freshBlock 0 0])
    · simp [NotionCoreSourceDocument.Guard]
    · decide
    · apply NotionCoreSourceDocument.Execution.cons (next :=
          [⟨0, 0, [⟨(0, .start), [⟨(0, .event (0, 1)), .text 97 false⟩], none⟩]⟩])
      · refine ⟨by decide, ?_⟩
        simp [NotionCoreSourceDocument.freshBlock, NotionCoreSource.Block.traversal,
          NotionCoreSource.Slice.traversal, NotionCoreSource.Slice.close,
          NotionCoreSource.stopKey, NotionCoreSpec.closeOf, NotionCoreSpec.finishSlot]
      · decide
      · exact .nil _
  constructor
  · exact ⟨_, .cons executed (.cons ⟨rfl, rfl⟩ (.nil _))⟩
  · intro accepted
    have semantic := history_sound accepted
    change NotionCoreHistory.spec.admits (NotionCoreHistory.labels [exampleCommands.map NotionCoreSourceDocument.Command.semantic] ++
      [.query () [(0, [])]]) at semantic
    obtain ⟨final, run, wrong⟩ := NotionCoreHistory.updates_query_iff _ _ |>.mp semantic
    have computed : NotionCoreHistory.run [] [exampleCommands.map NotionCoreSourceDocument.Command.semantic] =
        some [⟨0, 0, [NotionCoreSpec.root 0, NotionCoreSpec.character 0 (0, 1) 97,
          NotionCoreSpec.finishSlot 0], true⟩] := by decide
    rw [computed] at run
    cases run
    revert wrong
    decide

#print axioms history_sound
#print axioms source_history_control
end Sal.MRDTs.Instances.NotionCoreSourceHistory
