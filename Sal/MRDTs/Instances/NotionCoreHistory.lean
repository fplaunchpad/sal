import Sal.MRDTs.Instances.NotionCoreSpec
import Sal.MRDTs.Paper1.HistorySpec

/-! Independent prefix-closed history language for the core editor.
A semantic update is an atomic group of ordinary identity-addressed commands.
Grouping preserves a split request's create/split atomicity; the document state
contains neither transactions nor replay order. There is no clock-order guard
in this language. Source message decoding and witness selection are separate.
-/
namespace Sal.MRDTs.Instances.NotionCoreHistory
open Sal.MRDTs.Paper1 NotionCoreSpec

abbrev Update := List Command
abbrev View := List (Nat × List Nat)

def machine : HistoryMachine Update Unit View where
  State := Document
  initial := []
  transition before label after := match label with
    | .update commands => execute before commands = some after
    | .query _ answer => after = before ∧ answer = view before

def spec : HistorySpec Update Unit View := machine.toSpec

def run (before : Document) : List Update → Option Document
  | [] => some before
  | commands :: rest => (execute before commands).bind fun next => run next rest

def labels (updates : List Update) : List (SeqLabel Update Unit View) :=
  updates.map SeqLabel.update

/-- Accepted update groups execute exactly the independent partial machine.
An invalid origin or target cannot be repaired by a history acceptance witness. -/
theorem update_runs_iff (before after : Document) (updates : List Update) :
    Runs machine.transition before (labels updates) after ↔ run before updates = some after := by
  induction updates generalizing before with
  | nil =>
      constructor
      · intro h; cases h; rfl
      · intro h
        simp only [run, Option.some.injEq] at h
        subst after
        exact .nil _
  | cons commands updates ih =>
      constructor
      · intro h
        cases h with
        | cons one rest =>
            change execute before commands = some _ at one
            simp only [run, one, Option.bind_some]
            exact (ih _).mp rest
      · intro h
        simp only [run] at h
        cases one : execute before commands with
        | none => simp [one] at h
        | some next =>
            simp only [one, Option.bind_some] at h
            exact .cons one ((ih next).mpr h)

/-- The terminal query has the document view produced by those same groups.
This theorem relates two presentations of the independent spec only. It does
not relate implementation replay or choose an RA witness. -/
theorem updates_query_iff (updates : List Update) (answer : View) :
    spec.admits (labels updates ++ [.query () answer]) ↔
      ∃ final, run [] updates = some final ∧ answer = view final := by
  constructor
  · rintro ⟨final, history⟩
    obtain ⟨mid, before, query⟩ := history.split (labels updates) [.query () answer]
    cases query with
    | cons observed endRun =>
        change _ = mid ∧ answer = view mid at observed
        exact ⟨mid, (update_runs_iff [] mid updates).mp before, observed.2⟩
  · rintro ⟨final, executed, answer⟩
    exact ⟨final, ((update_runs_iff [] final updates).mpr executed).append
      (.cons ⟨rfl, answer⟩ (.nil _))⟩

/-- PASS+FAIL: a valid grouped split is visible atomically at its final query;
the same history cannot claim that all text remained in the original block. -/
def splitExample : List Update :=
  [[.create 0 0 none],
   [.insert (0, .start) [character 0 (0, 1) 97, character 0 (0, 2) 98]],
   [.create 1 1 (some 0), .split (0, .event (0, 1)) (0, 3) 1]]

theorem split_history_control :
    spec.admits (labels splitExample ++ [.query () [(0, [97]), (1, [98])]]) ∧
    ¬ spec.admits (labels splitExample ++ [.query () [(0, [97, 98]), (1, [])]]) := by
  simp only [updates_query_iff]
  constructor
  · exact ⟨[⟨0, 0, [root 0, character 0 (0, 1) 97, closeSlot 0 (0, 3)], true⟩,
      ⟨1, 1, [root 1, finishSlot 1, boundary 0 (0, 3), character 0 (0, 2) 98, finishSlot 0], true⟩], by decide, by decide⟩
  · rintro ⟨final, accepted, answer⟩
    have executed : run [] splitExample = some
        [⟨0, 0, [root 0, character 0 (0, 1) 97, closeSlot 0 (0, 3)], true⟩,
         ⟨1, 1, [root 1, finishSlot 1, boundary 0 (0, 3), character 0 (0, 2) 98, finishSlot 0],
           true⟩] := by decide
    rw [executed] at accepted
    cases accepted
    revert answer
    decide

#print axioms updates_query_iff
#print axioms split_history_control
end Sal.MRDTs.Instances.NotionCoreHistory
