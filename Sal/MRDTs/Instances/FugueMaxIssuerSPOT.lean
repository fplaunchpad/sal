import Sal.MRDTs.Instances.FugueMaxImplementation
import Sal.MRDTs.Instances.FugueMaxContractSPOT
import Plausible

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.IssuerSPOT

open Sal.EmbedRGA (unaryCode)
open FugueMaxContractSPOT

theorem exact_guard_accepts_short :
    canIssue unaryCode (summarize unaryCode shortHistory)
      (mGenInsAt unaryCode shortHistory 0 4 1) = true := by decide

theorem exact_guard_accepts_deleted_child :
    canIssue unaryCode (summarize unaryCode deletedChild)
      (mGenInsAt unaryCode deletedChild 0 4 1) = true := by decide

/-- Unlike the weak coordinate guard, the repaired issuer distinguishes the
two histories even though their complete live states are equal. -/
theorem exact_guard_rejects_wrong :
    canIssue unaryCode (summarize unaryCode shortHistory)
      (mGenInsAt unaryCode deletedChild 0 4 1) = false := by decide

theorem dead_birth_retained :
    (summarize unaryCode deletedChild).births = mMinted withChild := by decide

theorem metadata_distinguishes_histories :
    summarize unaryCode shortHistory ≠ summarize unaryCode deletedChild := by decide

theorem finite_guard_rejects_wrong :
    ¬ applicable unaryCode (eventOf (mGenInsAt unaryCode deletedChild 0 4 1))
      (stateOf unaryCode shortHistory) := by
  have inv : KInv unaryCode shortHistory :=
    (maxReach_inv unaryCode short_reachable).each 0
  rw [applicable_exact inv, exact_guard_rejects_wrong]
  decide

theorem finite_guard_accepts_deleted_child :
    applicable unaryCode (eventOf (mGenInsAt unaryCode deletedChild 0 4 1))
      (stateOf unaryCode deletedChild) := by
  have inv : KInv unaryCode deletedChild :=
    (maxReach_inv unaryCode deleted_reachable).each 0
  exact (applicable_exact inv _).mpr exact_guard_accepts_deleted_child

/-- The approved repair does not keep deletion-event records. -/
theorem no_delete_history (Γ : Sal.EmbedRGA.OrderedPrefixCode) (K : KnowM) :
    ∀ g ∈ (summarize Γ K).births, mIsIns g = true := by
  intro g hg
  exact (List.mem_filter.mp hg).2

def discardDeadBirths (s : IssuerState) : IssuerState :=
  { s with births := s.births.filter (fun g => decide (g.ts ∈ sIds s.live)) }

theorem discarding_dead_birth_changes_mint :
    prepareInsert unaryCode (discardDeadBirths (summarize unaryCode deletedChild)) 0 4 1 ≠
      mGenInsAt unaryCode deletedChild 0 4 1 := by decide

/-! Generate local steps and a common-ancestor fork by construction. Compare
the incremental issuer with the existing full-history generator. The mutation
removes deleted births only on the implementation side. -/

def position (n length : ℕ) : ℕ :=
  match n % 4 with
  | 2 => length
  | 3 => length / 2
  | _ => 0

def branch (mutate : IssuerState → IssuerState) (r start : ℕ)
    (K : KnowM) (s : IssuerState) (choices : List ℕ) : KnowM × IssuerState × Bool :=
  (choices.zipIdx start).foldl (fun (K, s, ok) (n, t) =>
    let i := position n (mView unaryCode K).length
    let g := if n % 4 = 0 then mGenDelAt unaryCode K r t i
      else mGenInsAt unaryCode K r t i
    let prepared := if n % 4 = 0 then prepareDelete s r t i
      else prepareInsert unaryCode s r t i
    let nextK := K ++ [g]
    let nextS := mutate (update unaryCode s prepared)
    (nextK, nextS, ok && decide (g = prepared) && canIssue unaryCode s prepared &&
      decide (nextS = summarize unaryCode nextK) &&
      decide (rawUpdate unaryCode (toState s) (eventOf prepared) = toState nextS))) (K, s, true)

def checkWith (mutate : IssuerState → IssuerState) (choices : List ℕ) : Bool :=
  let (A, a, okA) := branch mutate 0 1 [] (summarize unaryCode []) (choices.take 2)
  let (K, k, okK) := branch mutate 1 3 A a ((choices.drop 2).take 2)
  let (L, l, okL) := branch mutate 2 5 A a ((choices.drop 4).take 2)
  let merged := merge a k l
  let history := syncM K L
  okA && okK && okL && decide (merged = summarize unaryCode history) &&
    decide (rawMerge (toState a) (toState k) (toState l) = stateOf unaryCode history) &&
    (List.range (merged.live.length + 2)).all (fun i =>
      let expected := mGenInsAt unaryCode history 0 7 i
      decide (prepareInsert unaryCode merged 0 7 i = expected) &&
      decide (prepareInsert unaryCode { merged with births := merged.births.reverse } 0 7 i = expected) &&
      decide (prepareInsert unaryCode
        { merged with births := merged.births ++ merged.births } 0 7 i = expected))

def check := checkWith id

/-- Literal positive control includes a deleted child and subsequent mint. -/
theorem deleted_child_continuation : check [1, 2, 0, 2, 3, 0] = true := by native_decide

theorem dead_birth_mutation_detected :
    checkWith discardDeadBirths [1, 2, 0, 2, 3, 0] = false := by native_decide

theorem shrunk_dead_birth_mutation :
    checkWith discardDeadBirths [1, 0] = false := by decide

open Plausible
#eval do
  match ← Testable.checkIO (NamedBinder "choices"
      (∀ choices : List ℕ, checkWith discardDeadBirths choices = true))
      { numInst := 500, maxSize := 10, randomSeed := some 1 } with
  | .failure _ values shrinks =>
      IO.println s!"FugueMax dead-birth mutation detected; shrinks={shrinks}, counterexample={values}"
  | _ => throw (IO.userError "FugueMax harness missed the dead-birth mutation")

def campaign (seed : ℕ) : IO Unit := do
  match ← Testable.checkIO (NamedBinder "choices" (∀ choices : List ℕ, check choices = true))
      { numInst := 500, maxSize := 10, randomSeed := some seed } with
  | .success _ => IO.println s!"FugueMax issuer seed={seed}: 500 passed; no gaveUp"
  | .gaveUp n => throw (IO.userError s!"FugueMax issuer gaveUp {n}")
  | .failure _ values shrinks =>
      throw (IO.userError s!"FugueMax issuer failure {values}; shrinks={shrinks}")
#eval campaign 1
#eval campaign 37
#eval campaign 2026

def words : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun xs => [0, 1, 2, 3].map (fun x => x :: xs))
#eval do
  let cases := words 6
  if cases.all check then IO.println s!"FugueMax issuer exhaustive forks: {cases.length} passed"
  else throw (IO.userError "FugueMax issuer exhaustive forks failed")

#print axioms exact_guard_rejects_wrong
#print axioms metadata_distinguishes_histories
#print axioms finite_guard_rejects_wrong

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax.IssuerSPOT
