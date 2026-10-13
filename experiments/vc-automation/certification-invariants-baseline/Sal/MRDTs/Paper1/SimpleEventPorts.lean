import Sal.MRDTs.Paper1.EventBridge
import Sal.MRDTs.Instances.GSet
import Sal.MRDTs.Instances.FinsetStore
import Sal.MRDTs.Instances.FlatCounters
import Sal.MRDTs.Instances.FlatGrowOnly

/-! Independent full-input history languages for the eight production
instances built from grow-only stores and integer deltas. Abstract lists record
application entries; their queries use set membership or a mathematical sum.
They do not call concrete update, merge, or replay to define acceptance. -/
namespace Sal.MRDTs.Paper1.SimpleEventPorts
open Foundation

variable {A : Type} [DecidableEq A]

def emptyPolicy (A : Type) : OperationPolicy A := ⟨fun _ _ => False⟩

def emptyLaws {D : UpdateSig} (comm : ∀ a b, D.commutes a b) :
    RestrictedLaws D (emptyPolicy D.AppOp) where
  noncomm_exact := fun a b => by simp [emptyPolicy, comm a b]
  no_chain := by simp [emptyPolicy]
  conditional_commutation := by intro _ _ _ _ _ h; exact h.elim

/-- A list remembers applications, including duplicate adds; observation
forgets multiplicity. -/
def setMachine : DeterministicSpec (Op A) Unit (Set A) where
  State := List A
  initial := []
  update xs e := e.op :: xs
  query xs _ := {x | x ∈ xs}

def finiteMachine : DeterministicSpec (Op A) Unit (Finset A) where
  State := List A
  initial := []
  update xs e := e.op :: xs
  query xs _ := xs.toFinset

def booleanMachine : DeterministicSpec (Op A) Unit (A → Bool) where
  State := List A
  initial := []
  update xs e := e.op :: xs
  query xs _ x := decide (x ∈ xs)

def deltaMachine (delta : A → Int) : DeterministicSpec (Op A) Unit Int where
  State := List A
  initial := []
  update xs e := e.op :: xs
  query xs _ := (xs.map delta).sum

namespace Add
noncomputable abbrev D := Instances.AddStore.D A
abbrev generation : Issuance (D (A := A)) := Instances.AddStore.generation
abbrev laws : RestrictedLaws (D (A := A)).toUpdateSig (emptyPolicy A) :=
  emptyLaws Instances.AddStore.all_comm

def simulation : EventSequentialSimulation (D (A := A)) setMachine where
  Rel (s : Set A) (xs : List A) := s = {x | x ∈ xs}
  initial := by apply Set.ext; intro x; simp [D, Instances.AddStore.D, setMachine]
  update := by
    intro s xs hs e
    subst s
    apply Set.ext; intro x
    simp [D, Instances.AddStore.D, setMachine, Op.op]
  observes := by intro s xs hs q; exact hs

end Add

private theorem related_run {U Q V : Type} (M : DeterministicSpec U Q V)
    (R : M.State → M.State → Prop)
    (step : ∀ s t, R s t → ∀ e, R (M.update s e) (M.update t e))
    (obs : ∀ s t, R s t → ∀ q, M.query s q = M.query t q)
    {s t final : M.State} {ls : List (SeqLabel U Q V)} (rel : R s t)
    (run : Runs M.machine.transition s ls final) :
    ∃ final', Runs M.machine.transition t ls final' ∧ R final final' := by
  induction run generalizing t with
  | nil => exact ⟨t, .nil _, rel⟩
  | @cons s m final l ls h rest ih =>
      cases l with
      | update e =>
          change m = M.update s e at h
          subst m
          obtain ⟨last, hr, hrel⟩ := ih (step s t rel e)
          exact ⟨last, .cons rfl hr, hrel⟩
      | query q answer =>
          change m = s ∧ answer = M.query s q at h
          have ha := h.2.trans (obs s t rel q)
          have hm := h.1
          subst m
          obtain ⟨last, hr, hrel⟩ := ih rel
          exact ⟨last, .cons ⟨rfl, ha⟩ hr, hrel⟩

private theorem language_commutes_related {U Q V : Type}
    (M : DeterministicSpec U Q V) (R : M.State → M.State → Prop)
    (step : ∀ s t, R s t → ∀ e, R (M.update s e) (M.update t e))
    (obs : ∀ s t, R s t → ∀ q, M.query s q = M.query t q)
    (symm : Symmetric R) (a b : U)
    (swap : ∀ s, R (M.update (M.update s a) b) (M.update (M.update s b) a)) :
    M.toSpec.Commutes a b := by
  intro pre suf
  have exchange (x y : U)
      (hs : ∀ s, R (M.update (M.update s x) y) (M.update (M.update s y) x)) :
      M.toSpec.admits (pre ++ [.update x, .update y] ++ suf) →
      M.toSpec.admits (pre ++ [.update y, .update x] ++ suf) := by
    rintro ⟨final, run⟩
    have run' : Runs M.machine.transition M.initial
        (pre ++ ([.update x, .update y] ++ suf)) final := by
      simpa only [List.append_assoc] using run
    obtain ⟨mid, hp, pairSuffix⟩ := run'.split pre ([.update x, .update y] ++ suf)
    obtain ⟨afterPair, pair, suffix⟩ := pairSuffix.split [.update x, .update y] suf
    cases pair with
    | cons hx rest =>
      cases rest with
      | cons hy rest =>
        cases rest
        change _ = M.update mid x at hx
        subst hx
        change _ = M.update (M.update mid x) y at hy
        subst hy
        obtain ⟨last, hlast, _⟩ := related_run M R step obs (hs mid) suffix
        have swapped : Runs M.machine.transition mid
            ([.update y, .update x] ++ suf) last := by
          exact .cons (l := .update y) (m := M.update mid y) rfl
            (.cons (l := .update x) rfl hlast)
        exact ⟨last, by simpa only [List.append_assoc] using hp.append swapped⟩
  exact ⟨exchange a b swap, exchange b a (fun s => symm (swap s))⟩

private theorem list_commutes {V : Type}
    (query : List A → Unit → V)
    (obs : ∀ xs ys : List A, xs.Perm ys → ∀ q, query xs q = query ys q)
    (a b : Op A) :
    (show DeterministicSpec (Op A) Unit V from
      { State := List A, initial := [], update := fun xs e => e.op :: xs,
        query := query }).toSpec.Commutes a b := by
  apply language_commutes_related _ List.Perm
  · intro xs ys hp e; exact hp.cons e.op
  · exact obs
  · intro xs ys hp; exact hp.symm
  · intro xs; exact List.Perm.swap _ _ _

namespace Add

theorem commutes (a b : Op A) : setMachine.toSpec.Commutes a b := by
  apply list_commutes
  intro xs ys hp q
  ext x
  exact hp.mem_iff

theorem compatible : CommutationCompatibility (D (A := A)) id setMachine.toSpec :=
  fun a b _ => commutes a b

theorem certifiedV : EventCertifiedSpecificationRAV (D (A := A)) (emptyPolicy A)
    setMachine.toSpec generation := by
  apply event_certified_of_join_total laws _ compatible simulation.sound
  intro C _
  simpa [emptyPolicy, OperationPolicy.lift, ReplayPolicy.default,
    ReplayPolicy.unconstrained] using Instances.AddStore.join C.replayContext

theorem certified : EventCertifiedSpecificationRA (D (A := A)) (emptyPolicy A)
    setMachine.toSpec generation := certifiedV.ordinary

end Add

namespace Finite
abbrev D := Instances.FinsetStore.D A
abbrev generation : Issuance (D (A := A)) := Instances.FinsetStore.generation
abbrev laws : RestrictedLaws (D (A := A)).toUpdateSig (emptyPolicy A) :=
  emptyLaws Instances.FinsetStore.all_comm

def simulation : EventSequentialSimulation (D (A := A)) finiteMachine where
  Rel (s : Finset A) (xs : List A) := s = xs.toFinset
  initial := rfl
  update := by intro s xs hs e; subst s; simp [D, Instances.FinsetStore.D, finiteMachine, Op.op]
  observes := by intro s xs hs q; exact hs

theorem commutes (a b : Op A) : finiteMachine.toSpec.Commutes a b := by
  apply list_commutes
  intro xs ys hp q
  ext x
  simp only [List.mem_toFinset, hp.mem_iff]

theorem compatible : CommutationCompatibility (D (A := A)) id finiteMachine.toSpec :=
  fun a b _ => commutes a b

theorem certifiedV : EventCertifiedSpecificationRAV (D (A := A)) (emptyPolicy A)
    finiteMachine.toSpec generation := by
  apply event_certified_of_join_total laws _ compatible simulation.sound
  intro C _
  simpa [emptyPolicy, OperationPolicy.lift, ReplayPolicy.default,
    ReplayPolicy.unconstrained] using Instances.FinsetStore.join C.replayContext

theorem certified : EventCertifiedSpecificationRA (D (A := A)) (emptyPolicy A)
    finiteMachine.toSpec generation := certifiedV.ordinary
end Finite

namespace Boolean
noncomputable abbrev D := Instances.FlatGrowOnly.D A
abbrev generation : Issuance (D (A := A)) := Instances.FlatGrowOnly.generation
abbrev laws : RestrictedLaws (D (A := A)).toUpdateSig (emptyPolicy A) :=
  emptyLaws Instances.FlatGrowOnly.all_comm

def simulation : EventSequentialSimulation (D (A := A)) booleanMachine where
  Rel (s : A → Bool) (xs : List A) := ∀ x, s x = decide (x ∈ xs)
  initial := by intro x; rfl
  update := by
    intro s xs hs e x
    simp [D, Instances.FlatGrowOnly.D, booleanMachine, hs x, Op.op, Bool.or_comm]
  observes := by intro s xs hs q; exact funext hs

theorem commutes (a b : Op A) : booleanMachine.toSpec.Commutes a b := by
  apply list_commutes
  intro xs ys hp q
  funext x
  simp only [hp.mem_iff]

theorem compatible : CommutationCompatibility (D (A := A)) id booleanMachine.toSpec :=
  fun a b _ => commutes a b

theorem certifiedV : EventCertifiedSpecificationRAV (D (A := A)) (emptyPolicy A)
    booleanMachine.toSpec generation := by
  apply event_certified_of_join_total laws _ compatible simulation.sound
  intro C _
  simpa [emptyPolicy, OperationPolicy.lift, ReplayPolicy.default,
    ReplayPolicy.unconstrained] using Instances.FlatGrowOnly.join C.replayContext

theorem certified : EventCertifiedSpecificationRA (D (A := A)) (emptyPolicy A)
    booleanMachine.toSpec generation := certifiedV.ordinary
end Boolean

namespace Delta
variable (delta : A → Int)
abbrev D := Instances.FlatCounters.D A delta
abbrev generation : Issuance (D delta) := Instances.FlatCounters.generation delta
abbrev laws : RestrictedLaws (D delta).toUpdateSig (emptyPolicy A) :=
  emptyLaws (Instances.FlatCounters.all_comm delta)

def simulation : EventSequentialSimulation (D delta) (deltaMachine delta) where
  Rel (s : Int) (xs : List A) := s = (xs.map delta).sum
  initial := rfl
  update := by
    intro s xs hs e
    change Int at s
    change List A at xs
    change s + delta e.op = delta e.op + (xs.map delta).sum
    rw [hs, Int.add_comm]
  observes := by intro s xs hs q; exact hs

theorem commutes (a b : Op A) : (deltaMachine delta).toSpec.Commutes a b := by
  apply list_commutes
  intro xs ys hp q
  exact (hp.map delta).sum_eq

theorem compatible : CommutationCompatibility (D delta) id (deltaMachine delta).toSpec :=
  fun a b _ => commutes delta a b

theorem certifiedV : EventCertifiedSpecificationRAV (D delta) (emptyPolicy A)
    (deltaMachine delta).toSpec (generation delta) := by
  apply event_certified_of_join_total (laws delta) _ (compatible delta) (simulation delta).sound
  intro C _
  simpa [emptyPolicy, OperationPolicy.lift, ReplayPolicy.default,
    ReplayPolicy.unconstrained] using Instances.FlatCounters.join delta C.replayContext

theorem certified : EventCertifiedSpecificationRA (D delta) (emptyPolicy A)
    (deltaMachine delta).toSpec (generation delta) := (certifiedV delta).ordinary
end Delta

/-- Named ports of the production registry's concrete specializations. -/
abbrev gsetCertified := Add.certified (A := Nat)
abbrev gsetCertifiedV := Add.certifiedV (A := Nat)
abbrev finiteAddCertified := Finite.certified (A := Nat)
abbrev finiteAddCertifiedV := Finite.certifiedV (A := Nat)
abbrev counterCertified := Delta.certified (A := Unit) (fun _ => 1)
abbrev counterCertifiedV := Delta.certifiedV (A := Unit) (fun _ => 1)
abbrev iocCertified := Delta.certified (A := Instances.FlatCounters.IOCOp) (fun _ => 1)
abbrev iocCertifiedV := Delta.certifiedV (A := Instances.FlatCounters.IOCOp) (fun _ => 1)
abbrev pnCertified := Delta.certified Instances.FlatCounters.pnDelta
abbrev pnCertifiedV := Delta.certifiedV Instances.FlatCounters.pnDelta
abbrev booleanSetCertified := Boolean.certified (A := Nat)
abbrev booleanSetCertifiedV := Boolean.certifiedV (A := Nat)
abbrev booleanMapCertified := Boolean.certified (A := Nat × Nat)
abbrev booleanMapCertifiedV := Boolean.certifiedV (A := Nat × Nat)

/-- PASS+FAIL: duplicated adds are idempotent at the independent observation,
while constantly empty observation is rejected. -/
theorem finite_add_control :
    (finiteMachine (A := Nat)).toSpec.admits
      [.update (1,0,7), .update (2,1,7), .query () {7}] ∧
    ¬ (finiteMachine (A := Nat)).toSpec.admits
      [.update (1,0,7), .update (2,1,7), .query () ∅] := by
  constructor
  · exact ⟨_, .cons rfl (.cons rfl (.cons ⟨rfl, rfl⟩ (.nil _)))⟩
  · intro h
    have hx := (finiteMachine (A := Nat)).updates_query_iff [(1,0,7),(2,1,7)] () ∅ |>.mp h
    have : (∅ : Finset Nat) = {7} := hx
    simpa using congrArg (fun s : Finset Nat => 7 ∈ s) this

/-- PASS+FAIL: two increments and one decrement observe1, including updates
from different replicas; constant0 and treating decrement as a no-op fail. -/
theorem pn_control :
    (deltaMachine Instances.FlatCounters.pnDelta).toSpec.admits
      [.update (1,0,.inc), .update (2,1,.inc), .update (3,0,.dec), .query () 1] ∧
    ¬ (deltaMachine Instances.FlatCounters.pnDelta).toSpec.admits
      [.update (1,0,.inc), .update (2,1,.inc), .update (3,0,.dec), .query () 2] := by
  constructor
  · exact ⟨_, .cons rfl (.cons rfl (.cons rfl (.cons ⟨rfl,rfl⟩ (.nil _))))⟩
  · intro h
    have hx := (deltaMachine Instances.FlatCounters.pnDelta).updates_query_iff
      [(1,0,.inc),(2,1,.inc),(3,0,.dec)] () 2 |>.mp h
    change (2 : Int) = 1 at hx
    omega

/-- PASS+FAIL: the ordinary set records both application entries; an always
empty observer cannot satisfy this language. -/
theorem add_control :
    (setMachine (A := Nat)).toSpec.admits
      [.update (1,0,7), .update (2,1,8), .query () {7,8}] ∧
    ¬ (setMachine (A := Nat)).toSpec.admits
      [.update (1,0,7), .update (2,1,8), .query () ∅] := by
  constructor
  · refine ⟨_, .cons rfl (.cons rfl (.cons ⟨rfl,?_⟩ (.nil _)))⟩
    ext x; simp [setMachine, DeterministicSpec.machine, Op.op, or_comm]
  · intro h
    have hx := (setMachine (A := Nat)).updates_query_iff [(1,0,7),(2,1,8)] () ∅ |>.mp h
    have hm := congrArg (fun s : Set Nat => 7 ∈ s) hx
    simpa [setMachine, Op.op] using hm

/-- PASS+FAIL: the Boolean grow-only observer reports both added elements. -/
theorem boolean_control :
    (booleanMachine (A := Nat)).toSpec.admits
      [.update (1,0,7), .update (2,1,8), .query () (fun x => decide (x = 7 ∨ x = 8))] ∧
    ¬ (booleanMachine (A := Nat)).toSpec.admits
      [.update (1,0,7), .update (2,1,8), .query () (fun _ => false)] := by
  constructor
  · refine ⟨_, .cons rfl (.cons rfl (.cons ⟨rfl,?_⟩ (.nil _)))⟩
    funext x; simp [booleanMachine, DeterministicSpec.machine, Op.op, or_comm, Bool.or_comm]
  · intro h
    have hx := (booleanMachine (A := Nat)).updates_query_iff [(1,0,7),(2,1,8)] ()
      (fun _ => false) |>.mp h
    have hm := congrArg (fun f : Nat → Bool => f 7) hx
    simp [booleanMachine, Op.op] at hm

/-- PASS+FAIL: immutable key/value entries sharing a key both remain visible;
interpreting the grow-only map as last-write overwrite is rejected. -/
theorem immutable_map_control :
    (booleanMachine (A := Nat × Nat)).toSpec.admits
      [.update (1,0,(7,10)), .update (2,1,(7,20)),
       .query () (fun p => decide (p = (7,10) ∨ p = (7,20)))] ∧
    ¬ (booleanMachine (A := Nat × Nat)).toSpec.admits
      [.update (1,0,(7,10)), .update (2,1,(7,20)),
       .query () (fun p => decide (p = (7,20)))] := by
  constructor
  · refine ⟨_, .cons rfl (.cons rfl (.cons ⟨rfl,?_⟩ (.nil _)))⟩
    funext p; simp [booleanMachine, DeterministicSpec.machine, Op.op, or_comm, Bool.or_comm]
  · intro h
    have hx := (booleanMachine (A := Nat × Nat)).updates_query_iff
      [(1,0,(7,10)),(2,1,(7,20))] () (fun p => decide (p = (7,20))) |>.mp h
    have hm := congrArg (fun f : (Nat × Nat) → Bool => f (7,10)) hx
    simp [booleanMachine, Op.op] at hm

/-- PASS+FAIL for increment-only members of the delta family. -/
theorem increment_control :
    (deltaMachine (A := Unit) (fun _ => 1)).toSpec.admits
      [.update (1,0,()), .update (2,1,()), .query () 2] ∧
    ¬ (deltaMachine (A := Unit) (fun _ => 1)).toSpec.admits
      [.update (1,0,()), .update (2,1,()), .query () 1] := by
  constructor
  · exact ⟨_, .cons rfl (.cons rfl (.cons ⟨rfl,rfl⟩ (.nil _)))⟩
  · intro h
    have hx := (deltaMachine (A := Unit) (fun _ => 1)).updates_query_iff
      [(1,0,()),(2,1,())] () 1 |>.mp h
    change (1 : Int) = 2 at hx
    omega

#print axioms gsetCertifiedV
#print axioms pnCertifiedV
#print axioms booleanMapCertifiedV
end Sal.MRDTs.Paper1.SimpleEventPorts
