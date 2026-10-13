import Sal.MRDTs.Paper1.Automation.GenericOrderedRecords

/-! Generic canonical-list algorithms. Their laws depend only on a strict
key order, independently of record payloads, issuance, and replay evidence. -/
namespace Sal.MRDTs.Paper1.Automation.OrderedLists

variable {Record Key : Type}

structure Order (key : Record → Key) (lt : Record → Record → Bool) where
  trans : ∀ {a b c}, lt a b = true → lt b c = true → lt a c = true
  irrefl : ∀ a, lt a a = false
  asymm : ∀ {a b}, lt a b = true → lt b a = false
  total : ∀ {a b}, key a ≠ key b → lt a b = true ∨ lt b a = true

def Sorted (lt : Record → Record → Bool) (xs : List Record) : Prop :=
  xs.Pairwise (fun a b => lt b a = true)

def insert (lt : Record → Record → Bool) (r : Record) : List Record → List Record
  | [] => [r]
  | x :: xs => if lt x r then r :: x :: xs else x :: insert lt r xs

def merge2 (lt : Record → Record → Bool) : List Record → List Record → List Record
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if lt y x then x :: merge2 lt xs (y :: ys)
      else y :: merge2 lt (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Recursive equations are a complete certificate for sorted insertion.
The certificate is discharged by unfolding the original definition. -/
theorem insert_eq (lt : Record → Record → Bool) (f : Record → List Record → List Record)
    (nil : ∀ r, f r [] = [r])
    (cons : ∀ r x xs, f r (x :: xs) = if lt x r then r :: x :: xs else x :: f r xs)
    (r : Record) (xs : List Record) : f r xs = insert lt r xs := by
  induction xs with
  | nil => exact nil r
  | cons x xs ih => rw [cons, insert, ih]

/-- Recursive equations characterize two-list merge without exposing its
termination implementation or requiring datatype-specific induction proofs. -/
theorem merge2_eq (lt : Record → Record → Bool) (f : List Record → List Record → List Record)
    (nil_left : ∀ ys, f [] ys = ys)
    (nil_right : ∀ xs, f xs [] = xs)
    (cons : ∀ x xs y ys, f (x :: xs) (y :: ys) =
      if lt y x then x :: f xs (y :: ys) else y :: f (x :: xs) ys)
    (xs ys : List Record) : f xs ys = merge2 lt xs ys := by
  induction xs, ys using merge2.induct lt with
  | case1 ys => rw [nil_left, merge2]
  | case2 xs => cases xs <;> simp [nil_left, nil_right, merge2]
  | case3 x xs y ys h ih => rw [cons, merge2]; simp [h, ih]
  | case4 x xs y ys h ih => rw [cons, merge2]; simp [h, ih]

theorem mem_insert (lt : Record → Record → Bool) (r z : Record) : ∀ xs,
    z ∈ insert lt r xs ↔ z ∈ xs ∨ z = r
  | [] => by simp [insert]
  | x :: xs => by
    by_cases h : lt x r = true
    · simp [insert, h]; tauto
    · simp only [insert, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rw [mem_insert lt r z xs]
      tauto

theorem insert_sorted {key : Record → Key} {lt : Record → Record → Bool}
    (O : Order key lt) (r : Record) : ∀ xs, Sorted lt xs →
    (∀ x ∈ xs, key x ≠ key r) → Sorted lt (insert lt r xs)
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, hs, hne => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hs
    by_cases h : lt y r = true
    · simp only [insert, h, ↓reduceIte]
      refine List.pairwise_cons.mpr ⟨?_, hs⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h
      · exact O.trans (hy z hz) h
    · simp only [insert, h, ↓reduceIte]
      refine List.pairwise_cons.mpr ⟨?_, insert_sorted O r ys hys
        (fun x hx => hne x (List.mem_cons_of_mem _ hx))⟩
      intro z hz
      rcases (mem_insert lt r z ys).mp hz with hz | rfl
      · exact hy z hz
      · exact (O.total (hne y List.mem_cons_self)).resolve_left h

theorem mem_merge2 (lt : Record → Record → Bool) (z : Record) (xs ys : List Record) :
    z ∈ merge2 lt xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  induction xs, ys using merge2.induct lt with
  | case1 ys => simp [merge2]
  | case2 xs => cases xs <;> simp [merge2]
  | case3 a as b bs h ih => rw [merge2]; simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]; tauto
  | case4 a as b bs h ih => rw [merge2]; simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]; tauto

theorem merge2_sorted {key : Record → Key} {lt : Record → Record → Bool}
    (O : Order key lt) (xs ys : List Record) (hx : Sorted lt xs) (hy : Sorted lt ys)
    (hne : ∀ a ∈ xs, ∀ b ∈ ys, key a ≠ key b) : Sorted lt (merge2 lt xs ys) := by
  induction xs, ys using merge2.induct lt with
  | case1 ys => simpa [merge2] using hy
  | case2 xs => cases xs <;> simpa [merge2] using hx
  | case3 a as b bs h ih =>
    rw [merge2]; simp only [h, ↓reduceIte]
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp hx
    refine List.pairwise_cons.mpr ⟨?_, ih has hy (fun x hx => hne x (List.mem_cons_of_mem _ hx))⟩
    intro z hz
    rcases (mem_merge2 lt z as (b :: bs)).mp hz with hz | hz
    · exact ha z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact h
      · exact O.trans ((List.pairwise_cons.mp hy).1 z hz) h
  | case4 a as b bs h ih =>
    rw [merge2]; simp only [h, ↓reduceIte]
    obtain ⟨hb, hbs⟩ := List.pairwise_cons.mp hy
    have hab := (O.total (Ne.symm (hne a List.mem_cons_self b List.mem_cons_self))).resolve_left h
    refine List.pairwise_cons.mpr ⟨?_, ih hx hbs (fun x hx y hy => hne x hx y (List.mem_cons_of_mem _ hy))⟩
    intro z hz
    rcases (mem_merge2 lt z (a :: as) bs).mp hz with hz | hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hab
      · exact O.trans ((List.pairwise_cons.mp hx).1 z hz) hab
    · exact hb z hz

theorem sorted_ext {key : Record → Key} {lt : Record → Record → Bool}
    (O : Order key lt) : ∀ (xs ys : List Record), Sorted lt xs → Sorted lt ys →
    (∀ z, z ∈ xs ↔ z ∈ ys) → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, hm => False.elim (by simpa using (hm y).mpr List.mem_cons_self)
  | x :: xs, [], _, _, hm => False.elim (by simpa using (hm x).mp List.mem_cons_self)
  | x :: xs, y :: ys, hx, hy, hm => by
    obtain ⟨hxx, hxs⟩ := List.pairwise_cons.mp hx
    obtain ⟨hyy, hys⟩ := List.pairwise_cons.mp hy
    have heads : x = y := by
      rcases List.mem_cons.mp ((hm x).mp List.mem_cons_self) with h | h
      · exact h
      · rcases List.mem_cons.mp ((hm y).mpr List.mem_cons_self) with h' | h'
        · exact h'.symm
        · have hh := hxx y h'
          rw [O.asymm (hyy x h)] at hh
          contradiction
    subst y
    have tails : ∀ z, z ∈ xs ↔ z ∈ ys := by
      intro z
      constructor
      · intro hz
        rcases List.mem_cons.mp ((hm z).mp (List.mem_cons_of_mem _ hz)) with rfl | h
        · have hh := hxx z hz; rw [O.irrefl] at hh; contradiction
        · exact h
      · intro hz
        rcases List.mem_cons.mp ((hm z).mpr (List.mem_cons_of_mem _ hz)) with rfl | h
        · have hh := hyy z hz; rw [O.irrefl] at hh; contradiction
        · exact h
    rw [sorted_ext O xs ys hxs hys tails]

/-- Identifier membership agrees with record membership when the two carriers
have immutable records for each shared identifier. -/
theorem id_mem_iff {Id : Type} (id : Record → Id) (p : Record)
    (xs ys : List Record) (hp : p ∈ xs)
    (coherent : ∀ p ∈ xs, ∀ q ∈ ys, id p = id q → p = q) :
    id p ∈ ys.map id ↔ p ∈ ys := by
  constructor
  · intro h
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp h
    exact coherent p hp q hq eq.symm ▸ hq
  · intro h
    exact List.mem_map.mpr ⟨p, h, rfl⟩

/-- Immutable identifier records turn the executable survivor predicates
into the ordinary three-way set-membership formula. -/
theorem survivor_mem {Id : Type} [DecidableEq Id]
    (id : Record → Id) (lt : Record → Record → Bool) (l a b : List Record)
    (al : ∀ p ∈ a, ∀ q ∈ l, id p = id q → p = q)
    (bl : ∀ p ∈ b, ∀ q ∈ l, id p = id q → p = q)
    (ab : ∀ p ∈ a, ∀ q ∈ b, id p = id q → p = q)
    (ba : ∀ p ∈ b, ∀ q ∈ a, id p = id q → p = q) (p : Record) :
    p ∈ merge2 lt
      (a.filter (fun r => decide (id r ∈ b.map id ∨ id r ∉ l.map id)))
      (b.filter (fun r => decide (id r ∉ l.map id ∧ id r ∉ a.map id))) ↔
      (p ∈ a ∧ (p ∈ b ∨ p ∉ l)) ∨ (p ∈ b ∧ p ∉ l ∧ p ∉ a) := by
  rw [mem_merge2]
  simp only [List.mem_filter, decide_eq_true_eq]
  by_cases ha : p ∈ a <;> by_cases hb : p ∈ b
  · simp only [ha, hb, true_and, true_or, not_true_eq_false, and_false, or_false]
    simp [List.mem_map.mpr ⟨p, hb, rfl⟩]
  · rw [id_mem_iff id p a b ha ab, id_mem_iff id p a l ha al]
    simp [ha, hb]
  · rw [id_mem_iff id p b l hb bl, id_mem_iff id p b a hb ba]
    simp [ha, hb]
  · simp [ha, hb]

/-- Canonicality of a filtered two-way merge needs only the semantic
separation of its two survivor partitions. -/
theorem filtered_merge_sorted {key : Record → Key} {lt : Record → Record → Bool}
    (O : Order key lt) (a b : List Record) (keepA keepB : Record → Bool)
    (ha : Sorted lt a) (hb : Sorted lt b)
    (compatible : ∀ x ∈ a, ∀ y ∈ b, key x = key y → x = y)
    (separate : ∀ x ∈ a, keepB x ≠ true) :
    Sorted lt (merge2 lt (a.filter keepA) (b.filter keepB)) := by
  apply merge2_sorted O _ _ (List.Pairwise.filter _ ha) (List.Pairwise.filter _ hb)
  intro x hx y hy eq
  have same := compatible x (List.mem_of_mem_filter hx) y (List.mem_of_mem_filter hy) eq
  subst y
  exact separate x (List.mem_of_mem_filter hx) (List.of_mem_filter hy)


/-- Pairwise-facing rules keep bounded automation indexed by the normalized
carrier representation, rather than by a reducible sortedness wrapper. -/
theorem insert_pairwise {key : Record → Key} {lt : Record → Record → Bool}
    (O : Order key lt) (r : Record) (xs : List Record)
    (sorted : xs.Pairwise (fun a b => lt b a = true))
    (fresh : ∀ x ∈ xs, key x ≠ key r) :
    (insert lt r xs).Pairwise (fun a b => lt b a = true) :=
  insert_sorted O r xs sorted fresh

theorem filtered_merge_pairwise {key : Record → Key} {lt : Record → Record → Bool}
    (O : Order key lt) (a b : List Record) (keepA keepB : Record → Bool)
    (ha : a.Pairwise (fun x y => lt y x = true))
    (hb : b.Pairwise (fun x y => lt y x = true))
    (compatible : ∀ x ∈ a, ∀ y ∈ b, key x = key y → x = y)
    (separate : ∀ x ∈ a, keepB x ≠ true) :
    (merge2 lt (a.filter keepA) (b.filter keepB)).Pairwise (fun x y => lt y x = true) :=
  filtered_merge_sorted O a b keepA keepB ha hb compatible separate

theorem pairwise_ext {key : Record → Key} {lt : Record → Record → Bool}
    (O : Order key lt) (xs ys : List Record)
    (hx : xs.Pairwise (fun a b => lt b a = true))
    (hy : ys.Pairwise (fun a b => lt b a = true))
    (same : ∀ z, z ∈ xs ↔ z ∈ ys) : xs = ys := sorted_ext O xs ys hx hy same

end Sal.MRDTs.Paper1.Automation.OrderedLists
