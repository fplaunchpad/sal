import Sal.MRDTs.Paper1.PriorityQueueSameRecordSpec

/-! Stable partition of explaining histories, and ordinary priority-map replay.
These lemmas do not assume that a requested concrete observation is correct. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord

/-- Keep each class's internal order, placing the selected final class last. -/
def stablePartition {α : Type} (p : α → Bool) (events : List α) : List α :=
  events.filter (fun e => !p e) ++ events.filter p

theorem stablePartition_perm {α : Type} (p : α → Bool) (events : List α) :
    (stablePartition p events).Perm events := by
  simpa only [stablePartition,Bool.not_not] using
    List.filter_append_perm (fun e => !p e) events

/-- Moving a forward-closed class to the end cannot reverse a required edge. -/
theorem respects_stablePartition {α : Type} (p : α → Bool) (events : List α)
    (R : α → α → Prop) (ordered : respects events R)
    (closed : ∀ a ∈ events, ∀ b ∈ events, p a = true → R a b → p b = true) :
    respects (stablePartition p events) R := by
  apply List.pairwise_append.mpr
  refine ⟨ordered.filter _,ordered.filter _,?_⟩
  intro a ha b hb backwards
  obtain ⟨ha,pa⟩ := List.mem_filter.mp ha
  obtain ⟨hb,pb⟩ := List.mem_filter.mp hb
  have yes := closed b hb a ha pb backwards
  simp [yes] at pa

theorem stablePartition_enumerates {α : Type} (p : α → Bool) (events : List α)
    (E : Set α) (enumerates : listPermOf events E) :
    listPermOf (stablePartition p events) E := by
  have perm := stablePartition_perm p events
  exact ⟨perm.symm.nodup enumerates.1,fun a => perm.mem_iff.trans (enumerates.2 a)⟩

/-- If every selected event other than the distinguished event follows it,
the selected suffix starts with that event. No acyclicity premise is hidden. -/
theorem selected_starts_with {α : Type} (p : α → Bool) (events : List α)
    (R : α → α → Prop) (ordered : respects events R) (first : α)
    (member : first ∈ events) (selected : p first = true)
    (before : ∀ e ∈ events, p e = true → e ≠ first → R first e) :
    ∃ rest, events.filter p = first :: rest := by
  have present : first ∈ events.filter p := List.mem_filter.mpr ⟨member,selected⟩
  have respectsSelected := ordered.filter p
  cases eq : events.filter p with
  | nil => simp [eq] at present
  | cons a rest =>
    have equal : a = first := by
      by_contra different
      have inRest : first ∈ rest := by simpa [eq,Ne.symm different] using present
      have aMember := List.mem_filter.mp (show a ∈ events.filter p by simp [eq])
      have filteredOrder : respects (a :: rest) R := by
        rw [← eq]
        exact respectsSelected
      have backwards : ¬ R first a := (List.pairwise_cons.mp filteredOrder).1 first inRest
      exact backwards (before a aMember.1 aMember.2 different)
    subst a
    exact ⟨rest,rfl⟩

/-- Combined interface for a live birth (or a final remover) followed by its
selected successors. The complement remains in its original causal order. -/
theorem exists_partitioned_order {α : Type} (p : α → Bool) (events : List α)
    (R : α → α → Prop) (ordered : respects events R) (first : α)
    (member : first ∈ events) (selected : p first = true)
    (closed : ∀ a ∈ events, ∀ b ∈ events, p a = true → R a b → p b = true)
    (before : ∀ e ∈ events, p e = true → e ≠ first → R first e) :
    ∃ rest, (events.filter (fun e => !p e) ++ first :: rest).Perm events ∧
      respects (events.filter (fun e => !p e) ++ first :: rest) R ∧
      events.filter p = first :: rest := by
  obtain ⟨rest,eq⟩ := selected_starts_with p events R ordered first member selected before
  refine ⟨rest,?_,?_,eq⟩
  · simpa only [stablePartition,eq] using stablePartition_perm p events
  · simpa only [stablePartition,eq] using respects_stablePartition p events R ordered closed

/-- The ordinary single-cell machine; attachment snapshots play no role. -/
def cellUpdate (x : Nat) (cell : Option Int) (e : Event) : Option Int :=
  match e.op with
  | .add y value => if x = y then some value else cell
  | .inc y amount _ => if x = y then cell.map (fun p => p + amount) else cell
  | .remove y _ => if x = y then none else cell

def incrementAmount (e : Event) : Int :=
  match e.op with | .inc _ n _ => n | _ => 0

theorem seqStep_cell (s : SeqState) (e : Event) (x : Nat) :
    (seqStep s e).2 x = cellUpdate x (s.2 x) e := by
  rcases e with ⟨t,r,op⟩
  cases op <;> rfl

theorem cellUpdate_other (x : Nat) (cell : Option Int) (e : Event)
    (different : elementOf e.op ≠ x) : cellUpdate x cell e = cell := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp_all [cellUpdate,elementOf,Op.op,eq_comm]

theorem seqFold_cell (events : List Event) (s : SeqState) (x : Nat) :
    (events.foldl seqStep s).2 x = events.foldl (cellUpdate x) (s.2 x) := by
  induction events generalizing s with
  | nil => rfl
  | cons e events ih =>
    simp only [List.foldl_cons,ih,seqStep_cell]

theorem cellFold_filter_key (events : List Event) (cell : Option Int) (x : Nat) :
    events.foldl (cellUpdate x) cell =
      (events.filter (fun e => elementOf e.op = x)).foldl (cellUpdate x) cell := by
  induction events generalizing cell with
  | nil => rfl
  | cons e events ih =>
    by_cases same : elementOf e.op = x
    · simp only [List.foldl_cons,List.filter_cons,decide_eq_true same,ite_true]
      exact ih _
    · simp only [List.foldl_cons,List.filter_cons,decide_eq_false same,ite_false]
      rw [cellUpdate_other x cell e same]
      exact ih _

/-- Per-key replay may discard all other keys, including through arbitrary
Add/Remove operations on those keys. -/
theorem seqFold_filter_cell (events : List Event) (s : SeqState) (x : Nat) :
    (events.foldl seqStep s).2 x =
      ((events.filter (fun e => elementOf e.op = x)).foldl seqStep s).2 x := by
  rw [seqFold_cell,seqFold_cell,cellFold_filter_key]

/-- The support is exactly the domain of the ordinary priority map. -/
def SeqConsistent (s : SeqState) : Prop := ∀ x, x ∈ s.1 ↔ s.2 x ≠ none

theorem seqConsistent_initial : SeqConsistent model.initial := by
  simp [SeqConsistent,model]

theorem seqConsistent_step (s : SeqState) (consistent : SeqConsistent s) (e : Event) :
    SeqConsistent (seqStep s e) := by
  intro x
  rcases e with ⟨t,r,op⟩
  cases op <;>
    simp only [seqStep,supportStep,cellStep,Instances.PublishedAddWinsPriorityQueue.requestOf,
      Op.op]
  all_goals split_ifs <;> simp_all [SeqConsistent,Option.map_eq_none_iff]

theorem seqConsistent_fold (events : List Event) (s : SeqState)
    (consistent : SeqConsistent s) : SeqConsistent (events.foldl seqStep s) := by
  induction events generalizing s with
  | nil => exact consistent
  | cons e events ih => exact ih _ (seqConsistent_step s consistent e)

theorem seqFold_filter_support (events : List Event) (s : SeqState) (x : Nat)
    (consistent : SeqConsistent s) :
    x ∈ (events.foldl seqStep s).1 ↔
      x ∈ ((events.filter (fun e => elementOf e.op = x)).foldl seqStep s).1 := by
  rw [seqConsistent_fold events s consistent x,
    seqConsistent_fold (events.filter (fun e => elementOf e.op = x)) s consistent x,
    seqFold_filter_cell]

/-- Equal cells determine the whole ordinary map, including empty/max support. -/
theorem seqState_ext {s t : SeqState} (hs : SeqConsistent s) (ht : SeqConsistent t)
    (cells : ∀ x, s.2 x = t.2 x) : s = t := by
  apply Prod.ext
  · ext x
    rw [hs x,ht x,cells x]
  · exact funext cells

/-- An increment-only suffix adds exactly its signed amounts, and an absent
cell remains absent. -/
theorem cellFold_increments (events : List Event) (cell : Option Int) (x : Nat)
    (increments : ∀ e ∈ events, ∃ amount observed, e.op = .inc x amount observed) :
    events.foldl (cellUpdate x) cell =
      cell.map (fun value => value + (events.map incrementAmount).sum) := by
  induction events generalizing cell with
  | nil => simp
  | cons e events ih =>
    obtain ⟨amount,observed,op⟩ := increments e (by simp)
    simp only [List.foldl_cons]
    rw [ih _ (fun e he => increments e (by simp [he]))]
    simp only [cellUpdate,op,ite_true,List.map_cons,incrementAmount,List.sum_cons,Option.map_map]
    cases cell <;> simp [Function.comp_def,add_assoc]

theorem cellUpdate_absent (x : Nat) (e : Event)
    (noAdd : ∀ value, e.op ≠ .add x value) : cellUpdate x none e = none := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | add y value =>
    by_cases same : x = y
    · subst y
      exact False.elim (noAdd value rfl)
    · simp [cellUpdate,Op.op,same]
  | inc y amount observed => simp [cellUpdate,Op.op]
  | remove y observed => simp [cellUpdate,Op.op]

/-- After a final Remove, every Inc/Remove (including absent operations) keeps
the cell absent, provided no later Add for this key occurs. -/
theorem cellFold_absent (events : List Event) (x : Nat)
    (noAdd : ∀ e ∈ events, ∀ value, e.op ≠ .add x value) :
    events.foldl (cellUpdate x) none = none := by
  induction events with
  | nil => rfl
  | cons e events ih =>
    simp only [List.foldl_cons]
    rw [cellUpdate_absent x e (noAdd e (by simp))]
    exact ih (fun e member => noAdd e (by simp [member]))

/-- An ordinary Add resets all effects of its prefix; its increment suffix
uses the same signed amount sum as the concrete selected-record calculation. -/
theorem cellFold_birth_increments (pre suffix : List Event) (cell : Option Int)
    (x : Nat) (value : Int) (birth : Event) (born : birth.op = .add x value)
    (increments : ∀ e ∈ suffix, ∃ amount observed, e.op = .inc x amount observed) :
    (pre ++ birth :: suffix).foldl (cellUpdate x) cell =
      some (value + (suffix.map incrementAmount).sum) := by
  simp only [List.foldl_append,List.foldl_cons,cellUpdate,born,ite_true]
  exact cellFold_increments suffix (some value) x increments

#print axioms respects_stablePartition
#print axioms exists_partitioned_order
#print axioms seqFold_filter_cell
#print axioms cellFold_increments
#print axioms seqConsistent_fold
#print axioms seqState_ext
#print axioms cellFold_absent
end Sal.MRDTs.Paper1.PriorityQueueSameRecord
