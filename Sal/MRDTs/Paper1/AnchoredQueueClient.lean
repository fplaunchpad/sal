import Sal.MRDTs.Paper1.AnchoredQueueCoordinates

/-! Client requests contain values only. Preparation selects the current tail
or head and supplies the replication metadata. These are local request
refinements; concurrent delivery retains the existing named-head language. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.Client
open Foundation Instances.EmbedRGA Sal.EmbedRGA

inductive Request where
  | enqueue (value : Nat)
  | dequeue
  deriving DecidableEq, Repr

def view (s : State) : List Nat := s.map (fun r => r.2.1)

def step (s : List Nat) : Request → List Nat
  | .enqueue value => s ++ [value]
  | .dequeue => s.tail

/-- Empty dequeue produces no message. Enqueue requires the supplied fresh
clock to follow its observed anchor, exactly as the existing issuer does. -/
def prepare (s : State) (time replica : Nat) : Request → Option Event
  | .enqueue value =>
      let tail := (s.getLast?.map (fun r => (r.1,r.2.2))).getD (0,[])
      if tail.1 < time then some (time,replica,enq value tail.1 tail.2) else none
  | .dequeue => s.head?.map (fun r => (time,replica,deq r.1))

theorem prepared_canIssue {s : State} {time replica : Nat} {request : Request}
    {event : Event} (prepared : prepare s time replica request = some event) :
    CanIssue event s := by
  cases request with
  | enqueue value =>
    simp only [prepare] at prepared
    split at prepared
    next positive =>
      cases prepared
      refine ⟨positive, ?_⟩
      cases h : s.getLast? with
      | none =>
        left
        have empty : s = [] := List.getLast?_eq_none_iff.mp h
        simp [empty]
      | some last => right; simp
    next => simp at prepared
  | dequeue =>
    obtain ⟨head, observed, same⟩ := Option.map_eq_some_iff.mp prepared
    subst event
    change s.head?.map Prod.fst = some head.1
    simp [observed]

/-- The generated message performs the requested ordinary queue edit in the
issuing view. Freshness and the representation invariant are supplied by
certified execution, not by client arguments. -/
theorem prepared_refines {s : State} (sorted : ESorted s)
    (unique : (eIds s).Nodup) {time replica : Nat} (fresh : time ∉ eIds s)
    {request : Request} {event : Event}
    (prepared : prepare s time replica request = some event) :
    view (Q.update s event) = step (view s) request := by
  have issued := prepared_canIssue prepared
  cases request with
  | enqueue value =>
    simp only [prepare] at prepared
    split at prepared
    next =>
      cases prepared
      rw [issued_enqueue_appends sorted issued fresh]
      simp [view,step]
    next => simp at prepared
  | dequeue =>
    obtain ⟨head, observed, same⟩ := Option.map_eq_some_iff.mp prepared
    subst event
    rw [issued_dequeue_pops unique issued]
    cases s <;> rfl

theorem empty_dequeue (time replica : Nat) :
    prepare [] time replica .dequeue = none := rfl

/-- Every message admitted by the original issuer is the preparation of a
value-only client request. Introducing the adapter excludes no old issuance. -/
theorem canIssue_iff_prepared (event : Event) (s : State) :
    CanIssue event s ↔ ∃ request,
      prepare s event.time event.2.1 request = some event := by
  constructor
  · rcases event with ⟨time,replica,op⟩
    cases op with
    | ins value pref anchor =>
      rintro ⟨positive,empty | last⟩
      · refine ⟨.enqueue value, ?_⟩
        rcases empty with ⟨rfl,rfl,rfl⟩
        simp [prepare,positive,enq,Op.time]
      · refine ⟨.enqueue value, ?_⟩
        simp [prepare,last,positive,enq,Op.time]
    | del target =>
      intro observed
      refine ⟨.dequeue, ?_⟩
      obtain ⟨head,atHead,eq⟩ := Option.map_eq_some_iff.mp observed
      simp [prepare,atHead,eq,deq,Op.time]
  · rintro ⟨request,prepared⟩
    exact prepared_canIssue prepared

theorem client_controls :
    prepare [] 1 0 (.enqueue 7) = some (1,0,enq 7 0 []) ∧
    view (Q.update [] (1,0,enq 7 0 [])) = [7] ∧
    view (Q.update [] (1,0,enq 7 0 [])) ≠ [] ∧
    prepare [] 1 0 .dequeue = none ∧
    prepare [] 1 0 .dequeue ≠ some (1,0,deq 0) := by decide

/-- The client supplies no target; preparation names the head, and the local
effect removes exactly that head rather than returning a constant empty list. -/
theorem dequeue_controls :
    let s := Q.update (Q.update [] (1,0,enq 7 0 []))
      (2,0,enq 9 1 (unaryCode.enc 1))
    prepare s 3 0 .dequeue = some (3,0,deq 1) ∧
    prepare s 3 0 .dequeue ≠ some (3,0,deq 2) ∧
    view (Q.update s (3,0,deq 1)) = [9] ∧
    view (Q.update s (3,0,deq 1)) ≠ [] ∧
    view (Q.update s (3,0,deq 1)) ≠ [7,9] := by decide

#print axioms prepared_canIssue
#print axioms prepared_refines
#print axioms canIssue_iff_prepared
end Sal.MRDTs.Paper1.AnchoredQueue.Client
