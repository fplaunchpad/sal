import Sal.MRDTs.Instances.MVRLiveContract
import Plausible

namespace Sal.MRDTs.Instances.MVRLive.SPOT

def x : Event := (1,0,.write 10 [])
def y : Event := (2,1,.write 20 [1])
def z : Event := (3,2,.write 30 [1])

theorem local_overwrite : update (update ∅ x) y = {(2,20)} := by decide
theorem updates_do_not_all_commute :
    update (update ∅ x) y ≠ update (update ∅ y) x := by decide
theorem concurrent_survive :
    merge {(1,10)} {(2,20)} {(3,30)} = {(2,20),(3,30)} := by decide
theorem ancestor_not_resurrected :
    merge {(1,10)} {(2,20)} {(1,10)} = {(2,20)} := by decide
theorem union_is_wrong :
    ({(2,20)} ∪ {(1,10)} : State) ≠ live {x,y} := by decide
theorem clear_all_replay_is_wrong :
    update (update (update ∅ x) y) z ≠ {(3,30)} := by decide
theorem equal_values_distinct_writes :
    merge ∅ {(1,10)} {(2,10)} = {(1,10),(2,10)} := by decide
theorem equal_values_query : query (merge ∅ {(1,10)} {(2,10)}) = {10} := by decide
theorem omission_rejected : ¬ canIssue (2,1,.write 20 []) {(1,10)} := by decide
theorem exact_targets_accepted : canIssue y {(1,10)} := by decide

structure Branch where
  state : State := ∅
  history : Finset Event := ∅
  next : Nat := 1

def build (r : Nat) : List Nat → Branch → Branch
  | [], b => b
  | v :: vs, b =>
    let e : Event := (b.next,r,.write (v % 3) ((b.state.image Prod.fst).sort (· ≤ ·)))
    build r vs {
      state := update b.state e
      history := insert e b.history
      next := b.next + 1 }

/-- Two forks separated by synchronization, with unique identities allocated
by construction. The second fork starts from a potentially multi-value state. -/
def checkWith (combine : State → State → State → State) (ns : List Nat) : Bool := Id.run do
  let l := build 0 (ns.take 2) {}
  let a := build 1 ((ns.drop 2).take 2) l
  let b := build 2 ((ns.drop 4).take 2) { l with next := a.next }
  let m := combine l.state a.state b.state
  let h := a.history ∪ b.history
  let common : Branch := { state := m, history := h, next := b.next }
  let c := build 1 ((ns.drop 6).take 2) common
  let d := build 2 ((ns.drop 8).take 2) { common with next := c.next }
  return decide (m = live h) &&
    decide (combine m c.state d.state = live (c.history ∪ d.history))

def check := checkWith merge

theorem harness_rejects_union : checkWith (fun _ a b => a ∪ b) [0,0,0] = false := by
  native_decide

def words : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (words n).flatMap (fun xs => [0 :: xs, 1 :: xs])

theorem deterministic_backstop : ((words 10).all check) = true := by native_decide

theorem known_bad_union_detected :
    ({(2,20)} ∪ {(1,10)} : State) ≠ merge {(1,10)} {(2,20)} {(1,10)} := by decide

open Plausible
#eval do
  match ← Testable.checkIO (NamedBinder "choices"
      (∀ ns : List Nat, checkWith (fun _ a b => a ∪ b) ns = true))
      {numInst := 500, maxSize := 20, randomSeed := some 17} with
  | .failure _ values shrinks =>
    IO.println s!"MVR live union mutation detected: {values}; shrinks={shrinks}"
  | _ => throw (IO.userError "MVR live harness failed to detect union mutation")

def campaign (seed : Nat) : IO Unit := do
  match ← Testable.checkIO (NamedBinder "choices" (∀ ns : List Nat, check ns = true))
      {numInst := 500, maxSize := 20, randomSeed := some seed} with
  | .success _ => IO.println s!"MVR live seed={seed}: 500 passed; no gaveUp"
  | .gaveUp n => throw (IO.userError s!"MVR live gaveUp {n}")
  | .failure _ values shrinks =>
    throw (IO.userError s!"MVR live failure {values}; shrinks={shrinks}")
#eval campaign 17
#eval campaign 91
#eval campaign 2026

end Sal.MRDTs.Instances.MVRLive.SPOT
