import Mathlib.Data.List.Basic

/-!
# Sequential specifications as prefix-closed history languages

The trusted specification sees explicitly chosen update and query/answer labels.
The alphabet may retain complete timestamp/replica/operation inputs, or use an
explicit projection. The choice is a semantic interface decision.
An abstract transition system is one way to define such a language; acceptance
requires only a finite run, with no final-state acceptance condition.
-/

namespace Sal.MRDTs.Paper1

inductive SeqLabel (Update Query Value : Type) where
  | update : Update → SeqLabel Update Query Value
  | query : Query → Value → SeqLabel Update Query Value
  deriving DecidableEq

structure HistorySpec (Update Query Value : Type) where
  admits : List (SeqLabel Update Query Value) → Prop
  empty : admits []
  prefix_closed : ∀ pre suf, admits (pre ++ suf) → admits pre

/-- Every finite path is accepting. No determinism or totality is assumed. -/
structure HistoryMachine (Update Query Value : Type) where
  State : Type
  initial : State
  transition : State → SeqLabel Update Query Value → State → Prop

inductive Runs {State Label : Type} (step : State → Label → State → Prop) :
    State → List Label → State → Prop where
  | nil (s) : Runs step s [] s
  | cons {s m t l ls} : step s l m → Runs step m ls t → Runs step s (l :: ls) t

namespace Runs

theorem append {State Label : Type} {step : State → Label → State → Prop}
    {s m t : State} {pre suf : List Label}
    (hp : Runs step s pre m) (hs : Runs step m suf t) :
    Runs step s (pre ++ suf) t := by
  induction hp with
  | nil => exact hs
  | cons h _ ih => exact .cons h (ih hs)

theorem split {State Label : Type} {step : State → Label → State → Prop}
    {s t : State} (pre suf : List Label)
    (h : Runs step s (pre ++ suf) t) :
    ∃ m, Runs step s pre m ∧ Runs step m suf t := by
  induction pre generalizing s with
  | nil => exact ⟨s, .nil s, h⟩
  | cons l pre ih =>
      cases h with
      | cons hl hr =>
          obtain ⟨m, hp, hs⟩ := ih hr
          exact ⟨m, .cons hl hp, hs⟩

end Runs

namespace HistoryMachine

def toSpec {U Q V : Type} (M : HistoryMachine U Q V) : HistorySpec U Q V where
  admits history := ∃ final, Runs M.transition M.initial history final
  empty := ⟨M.initial, .nil _⟩
  prefix_closed pre suf h := by
    obtain ⟨final, run⟩ := h
    obtain ⟨mid, preRun, _⟩ := run.split pre suf
    exact ⟨mid, preRun⟩

end HistoryMachine

/-- Optional deterministic presentation of an independent specification. -/
structure DeterministicSpec (Update Query Value : Type) where
  State : Type
  initial : State
  update : State → Update → State
  query : State → Query → Value

namespace DeterministicSpec

def machine {U Q V : Type} (M : DeterministicSpec U Q V) : HistoryMachine U Q V where
  State := M.State
  initial := M.initial
  transition s label t := match label with
    | .update op => t = M.update s op
    | .query q answer => t = s ∧ answer = M.query s q

def toSpec {U Q V : Type} (M : DeterministicSpec U Q V) : HistorySpec U Q V :=
  M.machine.toSpec

def updateLabels {U Q V : Type} (ops : List U) : List (SeqLabel U Q V) :=
  ops.map SeqLabel.update

theorem updates_run {U Q V : Type} (M : DeterministicSpec U Q V)
    (s : M.State) (ops : List U) :
    Runs M.machine.transition s (updateLabels ops) (ops.foldl M.update s) := by
  induction ops generalizing s with
  | nil => exact .nil _
  | cons op ops ih => exact .cons rfl (ih _)

theorem updates_query_iff {U Q V : Type} (M : DeterministicSpec U Q V)
    (ops : List U) (q : Q) (answer : V) :
    M.toSpec.admits (updateLabels ops ++ [.query q answer]) ↔
      answer = M.query (ops.foldl M.update M.initial) q := by
  constructor
  · rintro ⟨final, run⟩
    have go : ∀ (ops : List U) (s : M.State),
        Runs M.machine.transition s (updateLabels ops ++ [.query q answer]) final →
        answer = M.query (ops.foldl M.update s) q := by
      intro ops
      induction ops with
      | nil =>
          intro s h
          cases h with
          | cons hq _ => exact hq.2
      | cons op ops ih =>
          intro s h
          cases h with
          | cons hu rest =>
              change _ = M.update s op at hu
              subst hu
              exact ih _ rest
    exact go ops M.initial run
  · intro h
    exact ⟨_, (M.updates_run M.initial ops).append
      (.cons ⟨rfl, h⟩ (.nil _))⟩

end DeterministicSpec
end Sal.MRDTs.Paper1
