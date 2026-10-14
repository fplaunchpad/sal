import Sal.MRDTs.Instances.AddWinsPriorityQueueReadSide
import Sal.MRDTs.Paper1.Automation.GenericQueryLift
import Mathlib.Data.Finset.Option

/-! Complete query interface for the archived natural-number element IDs.
Maximum priority ties choose the greatest element ID. `rmvMax` is a derived
client action, retaining the observed pair and issuing the existing Remove. -/
namespace Sal.MRDTs.Instances.AddWinsPriorityQueue
open Foundation

inductive FullQuery where
  | empty
  | lookup (element : Nat)
  | getPri (element : Nat)
  | getMax
  deriving DecidableEq, Repr

inductive Answer where
  | boolean (answer : Bool)
  | priority (answer : Option Int)
  | maximum (answer : Option (Nat × Int))
  deriving DecidableEq, Repr

def elements (s : State Nat) : Finset Nat := s.1.image Prod.fst

/-- Rank by signed priority, then by element ID. Only finite live support is
searched; a priority absent from the partial map supplies no candidate. -/
def entries (support : Finset Nat) (priority : Nat → Option Int) : Finset (Lex (Int × Nat)) :=
  support.biUnion (fun x => ((priority x).map (fun p => toLex (p,x))).toFinset)

def selectMax (support : Finset Nat) (priority : Nat → Option Int) : Option (Nat × Int) :=
  Option.map (fun p => ((ofLex p).2,(ofLex p).1)) (entries support priority).max

def getMax (s : State Nat) : Option (Nat × Int) := selectMax (elements s) (query s)

def read (s : State Nat) : FullQuery → Answer
  | .empty => .boolean (decide (elements s = ∅))
  | .lookup x => .boolean (decide (x ∈ elements s))
  | .getPri x => .priority (query s x)
  | .getMax => .maximum (getMax s)

def FullD : MRDTSig := Paper1.Automation.QueryLift.withQuery (D Nat) FullQuery Answer read

instance fullValueDecidableEq : DecidableEq FullD.Value :=
  inferInstanceAs (DecidableEq Answer)

@[simp] theorem full_update_sig : FullD.toUpdateSig = (D Nat).toUpdateSig := rfl

/-- The returned pair is the local observed maximum, not an atomic global
extraction result. Empty input emits no event; otherwise preparation emits
only Remove(selected element), with no replay-time maximum assumption. -/
def prepareRmvMax (s : State Nat) (timestamp replica : Nat) :
    Option (Op (Update Nat) × (Nat × Int)) :=
  (getMax s).map (fun selected => ((timestamp,replica,.remove selected.1),selected))

/-- The local client result and local effect of the prepared ordinary Remove. -/
def rmvMax (s : State Nat) (timestamp replica : Nat) : Option ((Nat × Int) × State Nat) :=
  (prepareRmvMax s timestamp replica).map (fun prepared => (prepared.2,step s prepared.1))

@[simp] theorem mem_entries (support : Finset Nat) (priority : Nat → Option Int)
    (p : Lex (Int × Nat)) : p ∈ entries support priority ↔
      (ofLex p).2 ∈ support ∧ priority (ofLex p).2 = some (ofLex p).1 := by
  simp only [entries,Finset.mem_biUnion,Option.mem_toFinset,Option.mem_def]
  constructor
  · rintro ⟨x,hx,equal⟩
    cases hp : priority x with
    | none => simp [hp] at equal
    | some amount =>
      simp only [hp,Option.map_some,Option.some.injEq] at equal
      have pair := congrArg ofLex equal
      change (amount,x) = ofLex p at pair
      have first := congrArg Prod.fst pair
      have second := congrArg Prod.snd pair
      exact ⟨second ▸ hx,by simpa only [← second,← first] using hp⟩
  · rintro ⟨member,amount⟩
    exact ⟨(ofLex p).2,member,by simp [amount]⟩

/-- Selection returns an actual present pair and no smaller priority than any
present candidate. This rules out a projection of a supplied candidate list. -/
theorem selectMax_sound (support : Finset Nat) (priority : Nat → Option Int)
    (x : Nat) (p : Int) (selected : selectMax support priority = some (x,p)) :
    x ∈ support ∧ priority x = some p ∧
      ∀ y q, y ∈ support → priority y = some q → q ≤ p := by
  cases h : (entries support priority).max with
  | bot =>
    have impossible : (none : Option (Nat × Int)) = some (x,p) := by
      simpa only [selectMax,h] using selected
    cases impossible
  | coe best =>
    have equal : ((ofLex best).2,(ofLex best).1) = (x,p) := by
      change Option.map _ _ = some (x,p) at selected
      rw [h] at selected
      exact Option.some.inj selected
    have member := (mem_entries support priority best).mp (Finset.mem_of_max h)
    have bx : (ofLex best).2 = x := congrArg Prod.fst equal
    have bp : (ofLex best).1 = p := congrArg Prod.snd equal
    refine ⟨bx ▸ member.1,by simpa only [bx,bp] using member.2,?_⟩
    intro y q hy hq
    have ym : toLex (q,y) ∈ entries support priority := by
      exact (mem_entries support priority (toLex (q,y))).mpr ⟨hy,hq⟩
    have ordered := Finset.le_max_of_eq ym h
    have lex : q < (ofLex best).1 ∨ q = (ofLex best).1 ∧ y ≤ (ofLex best).2 := by
      exact Prod.Lex.le_iff.mp ordered
    rcases lex with lt | eq
    · exact bp ▸ le_of_lt lt
    · exact le_of_eq (eq.1.trans bp)

theorem selectMax_none_iff (support : Finset Nat) (priority : Nat → Option Int) :
    selectMax support priority = none ↔ ∀ x ∈ support, priority x = none := by
  simp only [selectMax,Option.map_eq_none_iff]
  change (entries support priority).max = ⊥ ↔ _
  rw [Finset.max_eq_bot]
  constructor
  · intro empty x hx
    cases hp : priority x with
    | none => rfl
    | some amount =>
      have member := (mem_entries support priority (toLex (amount,x))).mpr ⟨hx,hp⟩
      rw [empty] at member
      exact False.elim (Finset.notMem_empty _ member)
  · intro absent
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨member,amount⟩ := (mem_entries support priority p).mp hp
    rw [absent _ member] at amount
    cases amount

theorem priority_none_iff (s : State Nat) (x : Nat) :
    query s x = none ↔ x ∉ elements s := by
  constructor
  · intro absent member
    obtain ⟨⟨y,t,v⟩,hp,heq⟩ := Finset.mem_image.mp member
    change y = x at heq
    subst y
    exact query_present s x t v hp absent
  · intro absent
    have empty : s.1.filter (fun p => p.1 = x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨member,equal⟩ := Finset.mem_filter.mp hp
      exact absent (Finset.mem_image.mpr ⟨p,member,equal⟩)
    simp only [query,winner,empty,Finset.image_empty,Finset.max_empty]
    rfl

theorem getMax_none_iff (s : State Nat) : getMax s = none ↔ elements s = ∅ := by
  rw [getMax,selectMax_none_iff]
  constructor
  · intro absent
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (priority_none_iff s x).mp (absent x hx) hx
  · intro empty x hx
    rw [empty] at hx
    exact False.elim (Finset.notMem_empty _ hx)

theorem getMax_sound (s : State Nat) (x : Nat) (p : Int)
    (selected : getMax s = some (x,p)) :
    x ∈ elements s ∧ query s x = some p ∧
      ∀ y q, y ∈ elements s → query s y = some q → q ≤ p :=
  selectMax_sound (elements s) (query s) x p selected

#print axioms selectMax_sound
#print axioms getMax_none_iff
#print axioms getMax_sound
end Sal.MRDTs.Instances.AddWinsPriorityQueue
