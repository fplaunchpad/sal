import Sal.MRDTs.Instances.QueueCorrectness
import Plausible

/-! Executable fork/merge regression tests for the proved FIFO legalization.
The generator issues actual head dequeues, including duplicate concurrent
targets. Tests are bounded evidence, not a certified-execution theorem. -/
namespace Sal.MRDTs.Instances.Queue.ContractSPOT

open Sal.MRDTs.Foundation

def a : Op QOp := (1, 0, .enq 10)
def b : Op QOp := (2, 0, .enq 20)
def da : Op QOp := (3, 1, .deq 1)
def db : Op QOp := (4, 2, .deq 1)

/-- Concurrent duplicate targets remove only one element. -/
theorem duplicate_target_legal : clientSpec.Legal [a, da, db, b] := by
  change clientLegalAux [] [] [a, da, db, b] = true
  decide
theorem duplicate_target_contents : clientSpec.run [a, da, db, b] = [(2, 20)] := by rfl

/-- Distinct dequeue targets still perform two ordinary pops. -/
theorem distinct_targets_pop_twice :
    clientSpec.run [a, b, da, (4, 0, .deq 2)] = [] := by rfl

/-- Deleting a different live element is not FIFO and is rejected. -/
theorem nonhead_rejected : ¬ clientSpec.Legal [a, b, (3, 0, .deq 2)] := by
  change ¬ clientLegalAux [] [] [a, b, (3, 0, .deq 2)] = true
  decide
theorem never_enqueued_rejected : ¬ clientSpec.Legal [(1, 0, .deq 7)] := by
  change ¬ clientLegalAux [] [] [(1, 0, .deq 7)] = true
  decide

/-- A repeated origin dequeue is forbidden, even though the replay operation
is idempotent. This checks the actual issuer guard. -/
theorem repeated_origin_rejected :
    ¬ qApplicable db (qUpdate (qUpdate [] a) da) := by
  simp [qApplicable, qUpdate, qTags, a, da, db]

abbrev Record := Op QOp × List ℕ

structure Branch where
  state : QState := []
  history : List Record := []
  next : ℕ := 1

/-- Every generated dequeue takes the actual current head. Empty queues
enqueue instead, so the campaign cannot succeed through universal rejection. -/
def buildBranch (replica : ℕ) : List ℕ → Branch → Branch
  | [], branch => branch
  | choice :: rest, branch =>
    let op := if choice % 3 = 0 then
      match branch.state with
      | [] => QOp.enq (choice % 7)
      | (tag, _) :: _ => QOp.deq tag
      else QOp.enq (choice % 7)
    let e : Op QOp := (branch.next, replica, op)
    buildBranch replica rest {
      state := qUpdate branch.state e
      history := branch.history ++ [(e, branch.history.map (fun r => r.1.1))]
      next := branch.next + 1 }

def fork (choices : List ℕ) : List Record × QState :=
  let base := buildBranch 0 (choices.take 2) {}
  let left := buildBranch 1 ((choices.drop 2).take 3) base
  let right := buildBranch 2 ((choices.drop 5).take 3) { base with next := left.next }
  (left.history ++ right.history.drop base.history.length,
    qMerge base.state left.state right.state)

def visible (history : List Record) (a b : Op QOp) : Bool :=
  history.any (fun r => r.1.1 == b.1 && r.2.contains a.1)

def directed (a b : Op QOp) : Bool := decide (qRcOrder a b = .Fst_then_snd)
def conflict (a b : Op QOp) : Bool := directed a b || directed b a

/-- Literal executable spelling of the public `loOn` definition. -/
def lo (history : List Record) (a b : Op QOp) : Bool :=
  (visible history a b && conflict a b) ||
    (!visible history a b && !visible history b a && directed a b &&
      !history.any (fun r => visible history b r.1 && conflict b r.1))

/-- The executable test uses precisely the framework relation, not a second
ordering policy. The hypothesis only supplies an executable visibility view. -/
theorem lo_eq_loOn (history : List Record) (R : ReplayContext Q.toUpdateSig)
    (hv : ∀ a b, R.vis a b ↔ visible history a b = true) (a b : Op QOp) :
    lo history a b = true ↔
      loOn R {e | e ∈ history.map Prod.fst} a b := by
  simp [lo, conflict, directed, loOn, UpdateSig.rc, ReplayPolicy.Before,
    QReplayPolicy, rc, hv, List.mem_map, and_assoc]
  rfl

def respectsB (history : List Record) : List (Op QOp) → Bool
  | [] => true
  | a :: rest => rest.all (fun b => !lo history b a) && respectsB history rest

/-- Instantiate the proved construction on the original duplicate-dequeue
example. The remaining element is derived through the general fold theorem. -/
theorem duplicate_legalization_fold :
    clientSpec.run (legalize [a, b, da, db]) = [(2, 20)] := by
  rw [legalize_fold]
  rfl

def checkWith (observe : QState → QState) (choices : List ℕ) : Bool :=
  let (history, merged) := fork choices
  let events := history.map Prod.fst
  let w := legalize events
  decide (w.Perm events) && respectsB history w && clientLegalAux [] [] w &&
    decide (w.foldl clientStep [] = observe merged)

def check : List ℕ → Bool := checkWith id

/-- Minimal permanent witness for the campaign's deliberately broken
extra-pop result. The legal enqueue must not disappear. -/
theorem extra_pop_rejected : checkWith List.tail [0] = false := by native_decide

/-- Actual shared-prefix merge: both branches delete the same head. -/
theorem fork_duplicate_contents :
    (fork [1, 2, 0, 4, 5, 0]).2 = [(2, 2), (4, 4), (5, 5)] := by native_decide

theorem fork_duplicate_witness : check [1, 2, 0, 4, 5, 0] = true := by native_decide

/-- FAIL companion: the same generated trace does not perform two distinct
head removals. In particular, the second shared element survives. -/
theorem fork_duplicate_not_two_pops :
    (fork [1, 2, 0, 4, 5, 0]).2 ≠ [(4, 4), (5, 5)] := by native_decide

open Plausible

/- The same harness must detect a spurious extra pop, before testing the
candidate. A failure to generate cases is not a passing negative control. -/
#eval do
  match ← Testable.checkIO (NamedBinder "choices" (∀ choices : List ℕ, checkWith List.tail choices = true))
      { numInst := 500, maxSize := 12, randomSeed := some 1 } with
  | .failure _ values shrinks =>
      IO.println s!"Extra-pop mutation detected; shrinks={shrinks}, counterexample={values}"
  | _ => throw (IO.userError "Queue harness failed to detect the extra-pop mutation")

def campaign (seed : ℕ) : IO Unit := do
  match ← Testable.checkIO (NamedBinder "choices" (∀ choices : List ℕ, check choices = true))
      { numInst := 500, maxSize := 12, randomSeed := some seed } with
  | .success _ => IO.println s!"Queue seed={seed}: 500 cases passed; no gaveUp"
  | .gaveUp n => throw (IO.userError s!"Queue seed={seed}: gaveUp {n}")
  | .failure _ values shrinks =>
      throw (IO.userError s!"Queue seed={seed}: failure {values}; shrinks={shrinks}")

#eval campaign 1
#eval campaign 37
#eval campaign 2026

def words : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun xs => [0, 1, 2].map (fun x => x :: xs))

#eval do
  let cases := words 8
  if cases.all check then
    IO.println s!"Queue exhaustive fork campaign: {cases.length} cases passed"
  else
    throw (IO.userError "Queue exhaustive fork campaign failed")

end Sal.MRDTs.Instances.Queue.ContractSPOT
