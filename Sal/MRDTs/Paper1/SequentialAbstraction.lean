import Sal.MRDTs.Paper1.HistorySpec

/-! An exact observation-preserving abstraction of deterministic sequential
machines preserves their complete history languages, including interspersed
queries. This permits replacing proof-oriented state with a natural ADT state
without weakening the sequential contract. -/
namespace Sal.MRDTs.Paper1
namespace DeterministicSpec

structure Abstraction {U Q V : Type} (M N : DeterministicSpec U Q V) where
  map : M.State → N.State
  initial : map M.initial = N.initial
  update : ∀ s u, map (M.update s u) = N.update (map s) u
  query : ∀ s q, M.query s q = N.query (map s) q

namespace Abstraction
variable {U Q V : Type} {M N : DeterministicSpec U Q V} (a : Abstraction M N)

theorem map_run {s t : M.State} {labels : List (SeqLabel U Q V)}
    (run : Runs M.machine.transition s labels t) :
    Runs N.machine.transition (a.map s) labels (a.map t) := by
  induction run with
  | nil => exact .nil _
  | @cons s m t label labels step rest ih =>
    apply Runs.cons (m := a.map m) ?_ ih
    cases label with
    | update u =>
      change m = M.update s u at step
      change a.map m = N.update (a.map s) u
      rw [step, a.update]
    | query q v =>
      change m = s ∧ v = M.query s q at step
      change a.map m = a.map s ∧ v = N.query (a.map s) q
      exact ⟨congrArg a.map step.1, step.2.trans (a.query s q)⟩

theorem lift_run {s : M.State} {t : N.State} {labels : List (SeqLabel U Q V)}
    (run : Runs N.machine.transition (a.map s) labels t) :
    ∃ final, Runs M.machine.transition s labels final ∧ a.map final = t := by
  generalize hs : a.map s = start at run
  induction run generalizing s with
  | nil => exact ⟨s, .nil _, hs⟩
  | @cons start mid final label labels step rest ih =>
    subst start
    cases label with
    | update u =>
      change mid = N.update (a.map s) u at step
      obtain ⟨last, run, eq⟩ := ih (s := M.update s u) ((a.update s u).trans step.symm)
      exact ⟨last, .cons rfl run, eq⟩
    | query q v =>
      change mid = a.map s ∧ v = N.query (a.map s) q at step
      obtain ⟨last, run, eq⟩ := ih (s := s) step.1.symm
      exact ⟨last, .cons ⟨rfl, step.2.trans (a.query s q).symm⟩ run, eq⟩

include a in
theorem admits_iff (labels : List (SeqLabel U Q V)) :
    M.toSpec.admits labels ↔ N.toSpec.admits labels := by
  constructor
  · rintro ⟨last, run⟩
    exact ⟨a.map last, by simpa only [machine, a.initial] using a.map_run run⟩
  · rintro ⟨last, run⟩
    have run' : Runs N.machine.transition (a.map M.initial) labels last := by
      simpa only [a.initial] using run
    obtain ⟨s, proof, _⟩ := a.lift_run run'
    exact ⟨s, proof⟩

end Abstraction
end DeterministicSpec
end Sal.MRDTs.Paper1
