import Sal.MRDTs.Instances.TransferableBoundedCounter
import Sal.MRDTs.Paper1.HistorySpec

/-! Independent escrow balance contract and source-specific obstructions.
The contract allows ordinary nonnegative transfers only; the Aegis source
accepts negative transfers, so it is not certified against this contract. -/
namespace Sal.MRDTs.Paper1.TransferableBoundedCounterEvent
open Foundation Instances.TransferableBoundedCounter.BismuthSource

structure AccountState where
  balance : Nat → Int
  consumed : Nat → Int
  members : Finset Nat

def initialAccounts (capacity owner : Nat) : AccountState :=
  ⟨fun r => if r = owner then capacity else 0, fun _ => 0, {owner}⟩

/-- Independent mathematical account update: transfer changes two balances,
allocation consumes available rights. Failed requests have no effect. -/
def accountTransfer (s : AccountState) (source target : Nat) (n : Int) : AccountState :=
  if n < 0 ∨ s.balance source < n then s
  else { s with balance := fun r => s.balance r +
    (if r = target then n else 0) - (if r = source then n else 0) }

noncomputable def accountExtremes (s : AccountState) : Option ((Int × Nat) × (Int × Nat)) :=
  s.members.toList.foldl (fun acc r =>
    let p := (s.balance r,r)
    match acc with
    | none => some (p,p)
    | some (lo,hi) => some ((if pairLE p lo then p else lo),
                           (if pairLE hi p then p else hi))) none

noncomputable def accountUpdate (s : AccountState) (e : Op Action) : AccountState :=
  match e.op with
  | .addParticipants ids => { s with members := s.members ∪ ids }
  | .allocate n => if n < 0 ∨ s.balance e.2.1 < n then s
    else { s with balance := fun r => s.balance r - if r = e.2.1 then n else 0,
                  consumed := fun r => s.consumed r + if r = e.2.1 then n else 0 }
  | .transfer n target => accountTransfer s e.2.1 target n
  | .rebalance => match accountExtremes s with
    | none => s
    | some (lo,hi) => if hi.2 = e.2.1 then
        accountTransfer s e.2.1 lo.2 ((hi.1 - lo.1) / 2) else s

def accountQuery (s : AccountState) : Query → Int
  | .available r => s.balance r
  | .reserved r => s.balance r + s.consumed r
  | .allocated r => s.consumed r

noncomputable def client (capacity owner : Nat) : DeterministicSpec (Op Action) Query Int where
  State := AccountState
  initial := initialAccounts capacity owner
  update := accountUpdate
  query := accountQuery

/-- Owner distributes half its ten rights to replica 1. Both then issue a
transfer of three to replica 2 from their common state. -/
def forkBase : State := transfer (initial 10 0) 0 1 5
def donor0 : State := transfer forkBase 0 2 3
def donor1 : State := transfer forkBase 1 2 3
def reunited : State := merge forkBase donor0 donor1

/-- PASS+FAIL: both guarded transfers succeed locally; max join credits only
three at the shared destination, instead of the hand-derived six. -/
theorem concurrent_credit_loss :
    available donor0 0 = 2 ∧ available donor1 1 = 2 ∧
    available reunited 2 = 3 ∧ available reunited 2 ≠ 6 ∧
    (reserved reunited 0 + reserved reunited 1 + reserved reunited 2) = 7 ∧
    (reserved reunited 0 + reserved reunited 1 + reserved reunited 2) ≠ 10 := by
  norm_num [donor0, donor1, reunited, forkBase, transfer, initial,
    available, reserved, bump, merge]

/-- Every full-input sequential order credits six. This compares concrete replay with concrete merge; it does not
claim an execution-level RA refutation. -/
theorem both_serial_orders :
    available (transfer donor0 1 2 3) 2 = 6 ∧
    available (transfer donor1 0 2 3) 2 = 6 ∧
    available reunited 2 ≠ available (transfer donor0 1 2 3) 2 ∧
    available reunited 2 ≠ available (transfer donor1 0 2 3) 2 := by
  norm_num [donor0, donor1, reunited, forkBase, transfer, initial,
    available, reserved, bump, merge]

/-- The independent mathematical balance machine credits six in either
serial order; this expected amount is not computed by concrete replay. -/
theorem independent_serial_credit :
    (accountTransfer (accountTransfer
      (accountTransfer (initialAccounts 10 0) 0 1 5) 0 2 3) 1 2 3).balance 2 = 6 ∧
    (accountTransfer (accountTransfer
      (accountTransfer (initialAccounts 10 0) 0 1 5) 1 2 3) 0 2 3).balance 2 = 6 ∧
    available reunited 2 ≠ 6 := by
  norm_num [accountTransfer, initialAccounts, reunited, donor0, donor1,
    forkBase, transfer, initial, available, reserved, bump, merge]

/-- PASS+FAIL: negative transfer is accepted by the source and can debit an
empty target. The independent nonnegative escrow contract leaves it alone. -/
theorem negative_transfer_obstruction :
    available (transfer (initial 10 0) 0 1 (-3)) 0 = 13 ∧
    available (transfer (initial 10 0) 0 1 (-3)) 1 = -3 ∧
    available (transfer (initial 10 0) 0 1 (-3)) 1 ≠ 0 ∧
    (accountTransfer (initialAccounts 10 0) 0 1 (-3)).balance 1 = 0 := by
  norm_num [transfer, initial, available, reserved, bump, accountTransfer, initialAccounts]

/-- Even with positive transfer requests, the empty-past causal seed equation
needed by the unrestricted empty-past commuting adapter fails.
The right-branch request is not legally issued, so this is NOT a failure of
an eligible guarded causal VC. The target guard is evaluated
at init on the right branch and at the funded state during sequential replay. -/
theorem causal_seed_obstruction :
    available (merge (initial 10 0) forkBase
      (update (initial 10 0) (2,1,.transfer 3 2))) 2 = 0 ∧
    available (update forkBase (2,1,.transfer 3 2)) 2 = 3 ∧
    merge (initial 10 0) forkBase (update (initial 10 0) (2,1,.transfer 3 2)) ≠
      update forkBase (2,1,.transfer 3 2) := by
  have lhs : available (merge (initial 10 0) forkBase
      (update (initial 10 0) (2,1,.transfer 3 2))) 2 = 0 := by
    norm_num [update, Op.op, transfer, forkBase, initial, available, reserved, bump, merge]
  have rhs : available (update forkBase (2,1,.transfer 3 2)) 2 = 3 := by
    norm_num [update, Op.op, transfer, forkBase, initial, available, reserved, bump]
  exact ⟨lhs,rhs,fun h => by rw [h, rhs] at lhs; omega⟩

#print axioms concurrent_credit_loss
#print axioms both_serial_orders
#print axioms negative_transfer_obstruction
#print axioms causal_seed_obstruction
end Sal.MRDTs.Paper1.TransferableBoundedCounterEvent
