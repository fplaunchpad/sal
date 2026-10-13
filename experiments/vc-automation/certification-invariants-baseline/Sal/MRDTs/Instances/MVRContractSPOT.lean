import Sal.MRDTs.Instances.MVRContract
import Plausible

namespace Sal.MRDTs.Instances.MVR.ContractSPOT
open Sal.MRDTs.Foundation

abbrev Raw := ((ℕ × ℕ) → Bool) × (ℕ → Bool)
def empty : Raw := (fun _ => false, fun _ => false)
abbrev Record := Op MVROp × List ℕ

def visibleTags (s : Raw) (history : List Record) : List ℕ :=
  history.filterMap fun (e, _) => if s.1 (e.1, writeValue e) && !s.2 e.1 then some e.1 else none

def branch (r : ℕ) (start : ℕ) (s : Raw) (history : List Record)
    (values : List ℕ) : Raw × List Record :=
  ((values.zipIdx start).foldl (fun (s, history) (v, t) =>
    let e : Op MVROp := (t, r, .write (v % 3) (visibleTags s history))
    (mvrUpdate s e, history ++ [(e, history.map (fun p => p.1.1))])) (s, history))

def fork (choices : List ℕ) : Raw × List Record :=
  let pre := branch 0 1 empty [] (choices.take 2)
  let left := branch 1 3 pre.1 pre.2 ((choices.drop 2).take 3)
  let right := branch 2 6 pre.1 pre.2 ((choices.drop 5).take 3)
  (mvrMerge pre.1 left.1 right.1, pre.2 ++ left.2.drop pre.2.length ++ right.2.drop pre.2.length)

def maximal (history : List Record) : Finset (ℕ × ℕ) :=
  (history.filter (fun p => !history.any (fun q => q.2.contains p.1.1))).map
    (fun p => (p.1.1, writeValue p.1)) |>.toFinset

def observed (s : Raw) (history : List Record) : Finset (ℕ × ℕ) :=
  (history.filter (fun p => s.1 (p.1.1, writeValue p.1) && !s.2 p.1.1)).map
    (fun p => (p.1.1, writeValue p.1)) |>.toFinset

def checkWith (mutate : Finset (ℕ × ℕ) → Finset (ℕ × ℕ)) (choices : List ℕ) : Bool :=
  let (s, history) := fork choices
  let expected := maximal history
  decide (mutate (observed s history) = expected) &&
    decide ((history.map Prod.fst).foldl clientStep ∅ = expected)

def check := checkWith id
def singleWinner (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  s.filter (fun p => p.1 = s.sup Prod.fst)

theorem concurrent_survive : maximal (fork [0, 0, 1, 1, 1, 2, 2, 2]).2 =
    {(5, 1), (8, 2)} := by decide
theorem single_winner_wrong :
    checkWith singleWinner [0, 0, 1, 1, 1, 2, 2, 2] = false := by decide
theorem shrunk_single_winner_wrong :
    checkWith singleWinner [0, 0, 0, 0, 0, 0] = false := by decide
theorem concurrent_same_value_distinct_ids :
    maximal (fork [0, 0, 1, 1, 1, 1, 1, 1]).2 = {(5, 1), (8, 1)} := by decide

theorem observed_both_superseded :
    clientStep {(1, 10), (2, 20)} (3, 0, .write 30 [1, 2]) = {(3, 30)} := by decide
theorem unseen_write_survives :
    clientStep {(1, 10), (2, 20)} (3, 0, .write 30 [1]) = {(2, 20), (3, 30)} := by decide
theorem query_exposes_values : MVR.query concurrentState () = ({10, 20} : Set ℕ) := by
  apply Set.ext
  intro v
  change mvrView concurrentState v ↔ v = 10 ∨ v = 20
  simp [mvrView, MVR, concurrentState, concurrentWrite₁, concurrentWrite₂,
    mvrMerge, mvrUpdate, exists_or]

/-- Apply the general fold-refinement theorem to two independent writes. -/
theorem concurrent_fold_refines :
    stateRel (applySeq MVR.toUpdateSig MVR.init [concurrentWrite₁, concurrentWrite₂])
      (clientSpec.run [concurrentWrite₁, concurrentWrite₂]) := by
  apply fold_refines
  · simp [concurrentWrite₁, concurrentWrite₂]
  · intro e he n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [overwrites, concurrentWrite₁, concurrentWrite₂] at hn
theorem fabricated_target_rejected :
    ¬ mvrApplicable (1, 0, .write 10 [9]) MVR.init := by
  simp [mvrApplicable, mvrVis, mvrTag, MVR_init_eq]
theorem omitted_target_rejected :
    ¬ mvrApplicable (2, 0, .write 20 []) (mvrUpdate empty (1, 0, .write 10 [])) := by
  intro h
  have := (h.2 20 [] rfl 1).mpr ⟨⟨10, by rfl⟩, by rfl⟩
  simp at this

open Plausible
#eval do
  match ← Testable.checkIO (NamedBinder "choices"
      (∀ choices : List ℕ, checkWith singleWinner choices = true))
      { numInst := 500, maxSize := 12, randomSeed := some 1 } with
  | .failure _ values shrinks =>
      IO.println s!"MVR single-winner mutation detected; shrinks={shrinks}, counterexample={values}"
  | _ => throw (IO.userError "MVR harness did not detect the single-winner mutation")

def campaign (seed : ℕ) : IO Unit := do
  match ← Testable.checkIO (NamedBinder "choices" (∀ choices : List ℕ, check choices = true))
      { numInst := 500, maxSize := 12, randomSeed := some seed } with
  | .success _ => IO.println s!"MVR seed={seed}: 500 passed; no gaveUp"
  | .gaveUp n => throw (IO.userError s!"MVR gaveUp {n}")
  | .failure _ values shrinks => throw (IO.userError s!"MVR failure {values}; shrinks={shrinks}")
#eval campaign 1
#eval campaign 37
#eval campaign 2026

def words : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun xs => [0, 1, 2].map (fun x => x :: xs))
#eval do
  let cases := words 8
  if cases.all check then IO.println s!"MVR exhaustive fork campaign: {cases.length} passed"
  else throw (IO.userError "MVR exhaustive fork campaign failed")

end Sal.MRDTs.Instances.MVR.ContractSPOT
