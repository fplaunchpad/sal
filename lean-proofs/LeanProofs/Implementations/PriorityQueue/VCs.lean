import LeanProofs1.Implementations.PriorityQueue.Definition
import LeanProofs1.Interface.VCRoute

/-!
# The priority queue: `Laws(D_type)` and VC1 to VC5

All three stores are grow-only and each effect inserts into exactly one of
them, so every pair of events commutes and `rc` is empty. `Laws(D_type)` is
then immediate, and the five conditions are identities among finite unions.
-/

namespace LeanProofs1.Implementations.PriorityQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

theorem do_eq (s : St) (e : D.Event) : D.do_ s e = step s e := rfl
theorem merge_eq (l a b : D.Sigma) : D.merge l a b = mergeState l a b := rfl
theorem sigma0_eq : D.sigma0 = ({} : St) := rfl

/-! ## Every pair of events commutes -/

theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro s
  simp only [do_eq]
  rcases h₁ : e₁.op with ⟨x₁, v₁⟩ | ⟨x₁, n₁, W₁⟩ | ⟨x₁, W₁⟩ <;>
    rcases h₂ : e₂.op with ⟨x₂, v₂⟩ | ⟨x₂, n₂, W₂⟩ | ⟨x₂, W₂⟩ <;>
    simp only [step, h₁, h₂] <;>
    refine St.ext ?_ ?_ ?_ <;>
    simp [Finset.insert_comm, Finset.union_assoc, Finset.union_comm,
      Finset.union_left_comm]

/-! ## `Laws(D_type)` -/

theorem no_rc_edge (e₁ e₂ : D.Event) : ¬ D.EventRcBefore e₁ e₂ := by
  simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOf]

theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) := by
  rintro ⟨h, -⟩
  simp [Impl.RcBefore, D, rcOf] at h

theorem rc_non_comm (e₁ e₂ : D.Event)
    (_ht : D.time e₁ ≠ D.time e₂) (_hr : D.rep e₁ ≠ D.rep e₂) :
    ((¬ D.Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
      D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁) := by
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h.1
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

theorem cond_comm (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event)
    (_ht : D.time e ≠ D.time e') (_hr : D.rep e ≠ D.rep e')
    (hrc : D.EventRcBefore e e') (_hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e'' :=
  absurd hrc (no_rc_edge e e')

theorem laws : Laws D := ⟨rc_non_comm, no_rc_chain, cond_comm⟩

/-- The unguarded reading, which clause 1 needs to see that `lo^C_E` has no
edges at all. -/
theorem rc_non_comm_uniform : UniformRcNonComm D := by
  intro e₁ e₂
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

/-! ## VC1 to VC5

`merge l a b` is a componentwise union of the two branches, and `do m e`
adds one more element to one store, so every condition is an identity among
finite unions. -/

theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  simp only [merge_eq, mergeState]
  exact St.ext (Finset.union_comm _ _) (Finset.union_comm _ _) (Finset.union_comm _ _)

theorem vc2_merge_init :
    ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s → D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  simp only [merge_eq, mergeState, sigma0_eq]
  exact St.ext (by simp) (by simp) (by simp)

theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l m x y : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C (E₁ ∩ E₂) l →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x →
      IsCanOn D C E₂ y →
      D.merge l (D.merge m x (D.do_ m e)) y
        = D.merge m (D.merge l x y) (D.do_ m e) := by
  intro _ _ _ l m x y e _ _ _ _ _ _ _ _ _ _ _ _
  rcases hop : e.op with ⟨z, v⟩ | ⟨z, n, W⟩ | ⟨z, W⟩ <;>
    simp only [merge_eq, mergeState, do_eq, step, hop] <;>
    refine St.ext ?_ ?_ ?_ <;>
    simp [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm,
      Finset.insert_union, Finset.union_insert]

/-- **VC4** CAUSAL-DELTA.

Every pair of events commutes, so `lo^C_E` has no edges, `down(e) \ {e}` is
empty and `B` is forced to `sigma0`. The condition is then the row's own
merge identity at the initial state. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C U → WeaklyClosed D C U →
      e ∈ U → MaximalOn D C U e →
      IsCanOn D C (U \ {e}) A →
      IsCanOn D C (downset C e \ {e}) B →
      D.merge B A (D.do_ B e) = D.do_ A e := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := Interface.rcOrder D
  intro C U A B e _ _ _ _ _ _ hB
  rw [isCanonicalState_empty (downset_diff_self_of_commuting all_commute C e) hB]
  show D.merge D.sigma0 A (D.do_ D.sigma0 e) = D.do_ A e
  rcases hop : e.op with ⟨x, v⟩ | ⟨x, n, W⟩ | ⟨x, W⟩ <;>
    simp only [merge_eq, mergeState, do_eq, step, sigma0_eq, hop] <;>
    refine St.ext ?_ ?_ ?_ <;>
    simp [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm,
      Finset.union_insert]

theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x₁ →
      IsCanOn D C (E₂ \ {e}) x₂ →
      D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
          (D.merge m x₂ (D.do_ m e))
        = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e) := by
  intro _ _ _ x₀ x₁ x₂ m e _ _ _ _ _ _ _ _ _ _ _ _
  rcases hop : e.op with ⟨z, v⟩ | ⟨z, n, W⟩ | ⟨z, W⟩ <;>
    simp only [merge_eq, mergeState, do_eq, step, hop] <;>
    refine St.ext ?_ ?_ ?_ <;>
    simp [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm,
      Finset.insert_union, Finset.union_insert]

theorem joinLaws : CanonicalJoinLawsOn D (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

theorem obligations : Obligations D :=
  Obligations.ofCommuting laws all_commute joinLaws

/-! ## What a replay leaves in each store

All three stores are grow-only, so a replay's state is read off the list:
each `add` contributes one birth, each `inc` one attachment per observed
insertion, each `remove` one disabled tag per observed insertion. -/

/-- The element an event names. -/
def elemOf (e : D.Event) : Nat :=
  match e.op with
  | .add x _ => x
  | .inc x _ _ => x
  | .remove x _ => x

/-- The births a list contributes. -/
def birthList (pi : List D.Event) : List Birth :=
  pi.filterMap (fun e => match e.op with
    | .add x v => some ((x, e.time), v)
    | _ => none)

/-- The attachments a list contributes. -/
noncomputable def incList (pi : List D.Event) : List Attachment :=
  pi.flatMap (fun e => match e.op with
    | .inc x n W => W.toList.map (fun u => ((x, u), e.time, n))
    | _ => [])

/-- The disabled tags a list contributes. -/
noncomputable def remList (pi : List D.Event) : List Tag :=
  pi.flatMap (fun e => match e.op with
    | .remove x W => W.toList.map (fun u => (x, u))
    | _ => [])

/-- Mapping a `Finset`'s elements through a list and back is its image. -/
theorem toFinset_image {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (W : Finset α) : (W.toList.map f).toFinset = W.image f := by
  ext b; simp

theorem state_applyList : ∀ (s : St) (pi : List D.Event),
    D.applyList s pi
      = ⟨s.births ∪ (birthList pi).toFinset,
         s.increments ∪ (incList pi).toFinset,
         s.removed ∪ (remList pi).toFinset⟩
  | s, [] => by
      refine St.ext ?_ ?_ ?_ <;> simp [birthList, incList, remList, Impl.applyList]
  | s, e :: rest => by
      show D.applyList (D.do_ s e) rest = _
      rw [state_applyList (D.do_ s e) rest]
      rcases hop : e.op with ⟨x, v⟩ | ⟨x, n, W⟩ | ⟨x, W⟩ <;>
        refine St.ext ?_ ?_ ?_ <;>
        simp [do_eq, step, hop, birthList, incList, remList, List.filterMap_cons,
          List.flatMap_cons, List.toFinset_append, toFinset_image,
          Finset.union_assoc, Finset.insert_union,
          Finset.union_comm, Finset.union_left_comm]

theorem state_replay (pi : List D.Event) :
    D.applyList D.sigma0 pi
      = ⟨(birthList pi).toFinset, (incList pi).toFinset, (remList pi).toFinset⟩ := by
  rw [state_applyList]
  refine St.ext ?_ ?_ ?_ <;> simp [sigma0_eq]

/-! ## The specification is local to one element

Every operation names one element, and the specification's transitions at
different elements do not interfere. So the cell an element ends with
depends only on the operations naming it. -/

/-- The element an operation names. -/
def opElem : type.OType → Nat
  | .add x _ => x
  | .inc x _ _ => x
  | .remove x _ => x

theorem opElem_elemOf (e : D.Event) : opElem e.op = elemOf e := by
  rcases h : e.op with ⟨x, v⟩ | ⟨x, n, W⟩ | ⟨x, W⟩ <;> simp [opElem, elemOf, h]

/-- One step of the specification. -/
noncomputable def supd (m : SpecState) (o : type.OType) : SpecState :=
  specMachine.update m o

/-- What one element sees of the specification's state. -/
def cell (m : SpecState) (x : Nat) : Bool × Option Int := (decide (x ∈ m.1), m.2 x)

theorem supd_add (m : SpecState) (x : Nat) (v : Int) :
    supd m (.add x v) = (insert x m.1, fun y => if y = x then some v else m.2 y) := rfl

theorem supd_rem (m : SpecState) (x : Nat) (W : Finset Nat) :
    supd m (.remove x W) = (m.1.erase x, fun y => if y = x then none else m.2 y) := rfl

/-- An operation of another element leaves this cell alone. -/
theorem cell_supd_other {m : SpecState} {o : type.OType} {x : Nat}
    (h : opElem o ≠ x) : cell (supd m o) x = cell m x := by
  rcases ho : o with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
    rw [ho] at h <;> simp only [opElem] at h
  · simp [cell, supd_add, Finset.mem_insert, h, Ne.symm h]
  · show cell (match m.2 y with
      | some v => (m.1, fun z => if z = y then some (v + n) else m.2 z)
      | none => m) x = cell m x
    cases hy : m.2 y <;> simp [cell, Ne.symm h]
  · simp [cell, supd_rem, Finset.mem_erase, Ne.symm h]

/-- An operation of this element moves the cell by a function of the cell
alone, so two states agreeing here stay agreeing. -/
theorem cell_supd_self {m₁ m₂ : SpecState} {o : type.OType} {x : Nat}
    (h : opElem o = x) (hc : cell m₁ x = cell m₂ x) :
    cell (supd m₁ o) x = cell (supd m₂ o) x := by
  rcases ho : o with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
    rw [ho] at h <;> simp only [opElem] at h <;> subst h
  · simp [cell, supd_add]
  · have h2 : m₁.2 y = m₂.2 y := congrArg Prod.snd hc
    have h1 : decide (y ∈ m₁.1) = decide (y ∈ m₂.1) := congrArg Prod.fst hc
    show cell (match m₁.2 y with
        | some v => (m₁.1, fun z => if z = y then some (v + n) else m₁.2 z)
        | none => m₁) y
      = cell (match m₂.2 y with
        | some v => (m₂.1, fun z => if z = y then some (v + n) else m₂.2 z)
        | none => m₂) y
    rw [h2]
    cases hy : m₂.2 y
    · exact hc
    · simp only [cell, Prod.mk.injEq]
      exact ⟨h1, rfl⟩
  · simp [cell, supd_rem]

/-- Folding operations of one element only depends on that element's cell. -/
theorem cell_fold_congr : ∀ (L : List type.OType) (x : Nat),
    (∀ o ∈ L, opElem o = x) → ∀ {m₁ m₂ : SpecState}, cell m₁ x = cell m₂ x →
    cell (L.foldl supd m₁) x = cell (L.foldl supd m₂) x
  | [], _, _, _, _, h => h
  | o :: L, x, hL, m₁, m₂, h => by
      exact cell_fold_congr L x (fun p hp => hL p (by simp [hp])) (m₁ := supd m₁ o)
        (m₂ := supd m₂ o) (cell_supd_self (hL o (by simp)) h)

/-- **Locality**: an element's cell is fixed by the operations naming it. -/
theorem cell_fold_filter : ∀ (L : List type.OType) (x : Nat) (m : SpecState),
    cell (L.foldl supd m) x
      = cell ((L.filter (fun o => decide (opElem o = x))).foldl supd m) x
  | [], _, _ => rfl
  | o :: L, x, m => by
      by_cases h : opElem o = x
      · simp only [List.filter_cons, decide_eq_true_eq, if_pos h, List.foldl_cons]
        exact cell_fold_filter L x (supd m o)
      · simp only [List.filter_cons, decide_eq_true_eq, if_neg h, List.foldl_cons]
        rw [cell_fold_filter L x (supd m o)]
        exact cell_fold_congr _ x (fun p hp => by
            simpa using (List.mem_filter.mp hp).2) (cell_supd_other h)

/-! ## The explaining order

Each event is ranked within its element. The winning insertion's addition
sits at rank 2, so it overwrites everything before it, and the increments
attached to that same insertion follow at rank 3. For an element with no
surviving insertion the removals come last and the key ends absent. -/

/-- The winning insertion of `x`: the lex-greatest live birth. -/
noncomputable def winner (pi : List D.Event) (x : Nat) : Option (Lex (Nat × Int)) :=
  (candidates (D.applyList D.sigma0 pi) x).max

/-- The rank of an event within its element. -/
noncomputable def rank (pi : List D.Event) (e : D.Event) : Nat :=
  match winner pi (elemOf e) with
  | none => match e.op with
      | .remove _ _ => 1
      | _ => 0
  | some b => match e.op with
      | .remove _ _ => 0
      | .add _ _ => if e.time = (ofLex b).1 then 2 else 1
      | .inc _ _ W => if (ofLex b).1 ∈ W then 3 else 1

theorem rank_le_three (pi : List D.Event) (e : D.Event) : rank pi e ≤ 3 := by
  unfold rank
  rcases winner pi (elemOf e) with _ | b <;>
    rcases e.op with ⟨x, v⟩ | ⟨x, n, W⟩ | ⟨x, W⟩ <;>
    simp only [] <;> first | omega | (split_ifs <;> omega)

/-- Order by element, then by rank. -/
def leKey (p q : Nat × Nat) : Bool :=
  decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2))

theorem leKey_trans {a b c : Nat × Nat} (hab : leKey a b = true) (hbc : leKey b c = true) :
    leKey a c = true := by
  simp only [leKey, decide_eq_true_eq] at *; omega

theorem leKey_total (a b : Nat × Nat) : (leKey a b || leKey b a) = true := by
  simp only [leKey, Bool.or_eq_true, decide_eq_true_eq]; omega

/-- The comparator: element first, then rank. -/
noncomputable def cmp (pi : List D.Event) (a b : D.Event) : Bool :=
  leKey (elemOf a, rank pi a) (elemOf b, rank pi b)

/-- The explaining replay. -/
noncomputable def arrange (pi : List D.Event) : List D.Event :=
  pi.mergeSort (cmp pi)

theorem arrange_perm (pi : List D.Event) : (arrange pi).Perm pi :=
  List.mergeSort_perm _ _

theorem arrange_sorted (pi : List D.Event) :
    (arrange pi).Pairwise (fun a b => cmp pi a b = true) :=
  List.pairwise_mergeSort (le := cmp pi)
    (fun _ _ _ hab hbc => leKey_trans hab hbc) (fun _ _ => leKey_total _ _) pi

/-- Restricted to one element, the replay is sorted by rank. -/
theorem arrange_filter_sorted (pi : List D.Event) (x : Nat) :
    ((arrange pi).filter (fun e => decide (elemOf e = x))).Pairwise
      (fun a b => rank pi a ≤ rank pi b) := by
  refine ((arrange_sorted pi).filter _).imp_of_mem ?_
  intro a b ha hb h
  have hax : elemOf a = x := by simpa using (List.mem_filter.mp ha).2
  have hbx : elemOf b = x := by simpa using (List.mem_filter.mp hb).2
  simp only [cmp, leKey, decide_eq_true_eq] at h
  rw [hax, hbx] at h
  omega

/-! ## Splitting a sorted list at a rank -/

theorem split_sorted {α : Type} (f : α → Nat) (k : Nat) : ∀ (L : List α),
    L.Pairwise (fun a b => f a ≤ f b) →
    ∃ A B, L = A ++ B ∧ (∀ a ∈ A, f a ≤ k) ∧ (∀ b ∈ B, k < f b)
  | [], _ => ⟨[], [], rfl, by simp, by simp⟩
  | c :: L, h => by
      by_cases hc : f c ≤ k
      · obtain ⟨A, B, hAB, hA, hB⟩ := split_sorted f k L (List.pairwise_cons.mp h).2
        exact ⟨c :: A, B, by rw [hAB]; rfl,
          by rintro a ha; rcases List.mem_cons.mp ha with rfl | ha
             · exact hc
             · exact hA a ha,
          hB⟩
      · refine ⟨[], c :: L, rfl, by simp, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · have := (List.pairwise_cons.mp h).1 b hb
          omega

/-! ## The four rank blocks

A rank-sorted list splits into its four blocks, and the fold over the
concatenation is the fold over each in turn. -/

theorem split_four {α : Type} (f : α → Nat) (hle : ∀ a, f a ≤ 3) : ∀ (L : List α),
    L.Pairwise (fun a b => f a ≤ f b) →
    ∃ L0 L1 L2 L3, L = L0 ++ L1 ++ L2 ++ L3
      ∧ (∀ a ∈ L0, f a = 0) ∧ (∀ a ∈ L1, f a = 1)
      ∧ (∀ a ∈ L2, f a = 2) ∧ (∀ a ∈ L3, f a = 3) := by
  intro L h
  obtain ⟨L0, R1, hL0, h0, h0'⟩ := split_sorted f 0 L h
  have hR1 : R1.Pairwise (fun a b => f a ≤ f b) := by
    rw [hL0] at h; exact (List.pairwise_append.mp h).2.1
  obtain ⟨L1, R2, hL1, h1, h1'⟩ := split_sorted f 1 R1 hR1
  have hR2 : R2.Pairwise (fun a b => f a ≤ f b) := by
    rw [hL1] at hR1; exact (List.pairwise_append.mp hR1).2.1
  obtain ⟨L2, L3, hL2, h2, h2'⟩ := split_sorted f 2 R2 hR2
  refine ⟨L0, L1, L2, L3, by rw [hL0, hL1, hL2]; simp, ?_, ?_, ?_, ?_⟩
  · intro a ha; have := h0 a ha; omega
  · intro a ha
    have hlo := h0' a (by rw [hL1]; simp [ha])
    have := h1 a ha; omega
  · intro a ha
    have hlo := h1' a (by rw [hL2]; simp [ha])
    have := h2 a ha; omega
  · intro a ha
    have hlo := h2' a ha
    have := hle a; omega

/-! ## What each block does to the cell

Rank 0 and rank 1 are wiped out by the rank-2 addition, which sets the cell
outright, and rank 3 then adds the winning insertion's increments. For an
element with no surviving insertion the cell never becomes present. -/

/-- A removal clears the cell. -/
theorem cell_remove (m : SpecState) (x : Nat) (W : Finset Nat) :
    cell (supd m (.remove x W)) x = (false, none) := by
  simp [cell, supd_rem]

/-- An addition sets the cell outright, whatever was there. -/
theorem cell_add (m : SpecState) (x : Nat) (v : Int) :
    cell (supd m (.add x v)) x = (true, some v) := by
  simp [cell, supd_add]

/-- An increment on an absent cell is a no-op. -/
theorem cell_inc_absent {m : SpecState} {x : Nat} (n : Int) (W : Finset Nat)
    (h : (cell m x).2 = none) : cell (supd m (.inc x n W)) x = cell m x := by
  show cell (match m.2 x with
      | some v => (m.1, fun z => if z = x then some (v + n) else m.2 z)
      | none => m) x = cell m x
  have hx : m.2 x = none := h
  rw [hx]

/-- An increment on a present cell adds its amount. -/
theorem cell_inc_present {m : SpecState} {x : Nat} {b : Bool} {v : Int} (n : Int)
    (W : Finset Nat) (h : cell m x = (b, some v)) :
    cell (supd m (.inc x n W)) x = (b, some (v + n)) := by
  have hx : m.2 x = some v := congrArg Prod.snd h
  have hb : decide (x ∈ m.1) = b := congrArg Prod.fst h
  show cell (match m.2 x with
      | some v => (m.1, fun z => if z = x then some (v + n) else m.2 z)
      | none => m) x = (b, some (v + n))
  rw [hx]
  simp only [cell, hb, if_true]

/-- Folding increments of one element over an absent cell leaves it absent. -/
theorem fold_incs_absent {x : Nat} : ∀ (L : List type.OType),
    (∀ o ∈ L, ∃ n W, o = .inc x n W) → ∀ {m : SpecState}, (cell m x).2 = none →
    cell (L.foldl supd m) x = cell m x
  | [], _, _, _ => rfl
  | o :: L, h, m, hm => by
      obtain ⟨n, W, rfl⟩ := h o (by simp)
      have hstep := cell_inc_absent (m := m) n W hm
      rw [List.foldl_cons,
        fold_incs_absent L (fun p hp => h p (by simp [hp])) (by rw [hstep]; exact hm),
        hstep]

/-- Folding the winning insertion's increments adds each amount. -/
theorem fold_incs_present {x : Nat} : ∀ (L : List type.OType),
    (∀ o ∈ L, ∃ n W, o = .inc x n W) → ∀ {m : SpecState} {b : Bool} {v : Int},
    cell m x = (b, some v) →
    cell (L.foldl supd m) x
      = (b, some (v + (L.map (fun o => match o with | .inc _ n _ => n | _ => 0)).sum))
  | [], _, _, _, _, hm => by simpa using hm
  | o :: L, h, m, b, v, hm => by
      obtain ⟨n, W, rfl⟩ := h o (by simp)
      rw [List.foldl_cons,
        fold_incs_present L (fun p hp => h p (by simp [hp]))
          (cell_inc_present (m := m) n W hm)]
      simp [add_assoc]

/-! ## The winner is an event of the replay -/

theorem mem_birthList (pi : List D.Event) (b : Birth) :
    b ∈ birthList pi ↔ ∃ e ∈ pi, e.op = .add b.1.1 b.2 ∧ b.1.2 = e.time := by
  simp only [birthList, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hb⟩
    rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;> rw [hop] at hb
    · simp only [Option.some.injEq] at hb
      subst hb; exact ⟨e, he, by rw [hop], rfl⟩
    · exact absurd hb (by simp)
    · exact absurd hb (by simp)
  · rintro ⟨e, he, hop, ht⟩
    refine ⟨e, he, ?_⟩
    rw [hop]
    rcases b with ⟨⟨y, u⟩, v⟩
    simp only at ht ⊢
    rw [ht]

/-- The winning insertion is carried by an `add` of the replay. -/
theorem winner_event {pi : List D.Event} {x : Nat} {w : Lex (Nat × Int)}
    (h : winner pi x = some w) :
    ∃ e ∈ pi, e.op = .add x (ofLex w).2 ∧ e.time = (ofLex w).1 := by
  have hmem : w ∈ candidates (D.applyList D.sigma0 pi) x := Finset.mem_of_max h
  simp only [candidates, Finset.mem_image, Finset.mem_filter] at hmem
  obtain ⟨b, ⟨hbB, hbx, -⟩, hbw⟩ := hmem
  rw [state_replay] at hbB
  have hb : b ∈ birthList pi := by simpa using hbB
  obtain ⟨e, he, hop, ht⟩ := (mem_birthList pi b).mp hb
  have hw1 : (ofLex w).1 = b.1.2 := by rw [← hbw]; rfl
  have hw2 : (ofLex w).2 = b.2 := by rw [← hbw]; rfl
  exact ⟨e, he, by rw [hop, hbx, hw2], by rw [hw1, ht]⟩

/-! ## The rank-two block is the winner's own addition -/

theorem eq_singleton_of_all_eq {α : Type} {L : List α} {e : α}
    (hnd : L.Nodup) (hmem : e ∈ L) (hall : ∀ a ∈ L, a = e) : L = [e] := by
  cases L with
  | nil => exact absurd hmem (by simp)
  | cons a L' =>
      have ha : a = e := hall a (by simp)
      subst ha
      cases L' with
      | nil => rfl
      | cons b L'' =>
          have hb : b = a := hall b (by simp)
          exact absurd (by simp [hb] : a ∈ b :: L'') (List.nodup_cons.mp hnd).1

/-- An event has rank `2` exactly when it is an `add` of its element at the
winning timestamp. -/
theorem rank_eq_two {pi : List D.Event} {e : D.Event} {w : Lex (Nat × Int)}
    (hw : winner pi (elemOf e) = some w) :
    rank pi e = 2 ↔ (∃ v, e.op = .add (elemOf e) v) ∧ e.time = (ofLex w).1 := by
  unfold rank
  rw [hw]
  rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩
  · have hy : elemOf e = y := by simp [elemOf, hop]
    simp only []
    constructor
    · intro h
      by_cases ht : e.time = (ofLex w).1
      · exact ⟨⟨v, by rw [hy]⟩, ht⟩
      · rw [if_neg ht] at h; exact absurd h (by omega)
    · rintro ⟨-, ht⟩
      exact if_pos ht
  · simp only []
    constructor
    · intro h
      split at h <;> omega
    · rintro ⟨⟨v, hv⟩, -⟩
      exact absurd hv (by simp)
  · simp only []
    constructor
    · intro h; omega
    · rintro ⟨⟨v, hv⟩, -⟩
      exact absurd hv (by simp)

/-! ## The rank-three block sums to the winner's acquired value -/

/-- The amount an increment carries. -/
def incAmount (e : D.Event) : Int :=
  match e.op with
  | .inc _ n _ => n
  | _ => 0

/-- `e` is an increment of `x` attached to the insertion `u`. -/
def incAt (x u : Nat) (e : D.Event) : Bool :=
  match e.op with
  | .inc y _ W => decide (y = x ∧ u ∈ W)
  | _ => false

theorem mem_incList (pi : List D.Event) (a : Attachment) :
    a ∈ incList pi ↔ ∃ e ∈ pi, incAt a.1.1 a.1.2 e = true
      ∧ a = (a.1, e.time, incAmount e) := by
  simp only [incList, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, ha⟩
    rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;> rw [hop] at ha <;>
      simp only [List.mem_map, Finset.mem_toList] at ha
    · exact absurd ha (by simp)
    · obtain ⟨u, hu, rfl⟩ := ha
      exact ⟨e, he, by simp [incAt, hop, hu], by simp [incAmount, hop]⟩
    · exact absurd ha (by simp)
  · rintro ⟨e, he, hat, ha⟩
    refine ⟨e, he, ?_⟩
    rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
      simp only [incAt, hop] at hat
    · exact absurd hat (by simp)
    · simp only [hop, List.mem_map, Finset.mem_toList]
      simp only [decide_eq_true_eq] at hat
      refine ⟨a.1.2, hat.2, ?_⟩
      have h1 : ((y, a.1.2) : Tag) = a.1 := by rw [hat.1]
      have h2 : Op.time e = a.2.1 := (congrArg (fun z : Attachment => z.2.1) ha).symm
      have h3 : n = a.2.2 := by
        have h := (congrArg (fun z : Attachment => z.2.2) ha).symm
        simpa [incAmount, hop] using h
      rw [h1, h2, h3]
    · exact absurd hat (by simp)

/-- The attachments on one insertion are the increments naming it. -/
theorem increments_filter (pi : List D.Event) (x u : Nat) :
    (D.applyList D.sigma0 pi).increments.filter (fun a => a.1 = (x, u))
      = ((pi.filter (incAt x u)).map
          (fun e => (((x, u) : Tag), e.time, incAmount e))).toFinset := by
  ext a
  rw [state_replay]
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨ha, htag⟩
    obtain ⟨e, he, hat, haeq⟩ := (mem_incList pi a).mp ha
    refine ⟨e, ⟨he, ?_⟩, ?_⟩
    · rw [htag] at hat; exact hat
    · rw [← htag]; exact haeq.symm
  · rintro ⟨e, ⟨he, hat⟩, rfl⟩
    exact ⟨(mem_incList pi _).mpr ⟨e, he, hat, rfl⟩, rfl⟩

/-! ## The replayed state depends only on the event set -/

theorem toFinset_perm {α : Type} [DecidableEq α] {l l' : List α} (h : l.Perm l') :
    l.toFinset = l'.toFinset := by
  ext a; simp [h.mem_iff]

theorem state_perm {pi pi' : List D.Event} (h : pi.Perm pi') :
    D.applyList D.sigma0 pi = D.applyList D.sigma0 pi' := by
  rw [state_replay, state_replay]
  refine St.ext ?_ ?_ ?_
  · exact toFinset_perm (h.filterMap _)
  · exact toFinset_perm (List.Perm.flatMap_right _ h)
  · exact toFinset_perm (List.Perm.flatMap_right _ h)

/-! ## Context facts -/

theorem time_ne {C : Ctx D} {a b : D.Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hne : a ≠ b) : a.time ≠ b.time := by
  obtain ⟨p, t, hL, ht⟩ := ha
  obtain ⟨p', t', hL', ht'⟩ := hb
  exact C.timestamps_distinct hL ht hL' ht' hne

/-! ## A removal at the end clears the cell -/

theorem fold_removes {x : Nat} : ∀ (L : List type.OType),
    (∀ o ∈ L, ∃ W, o = .remove x W) → L ≠ [] →
    ∀ m : SpecState, cell (L.foldl supd m) x = (false, none)
  | [], _, hne, _ => absurd rfl hne
  | [o], h, _, m => by
      obtain ⟨W, rfl⟩ := h o (by simp)
      simpa using cell_remove m x W
  | o :: p :: L, h, _, m => by
      exact fold_removes (p :: L) (fun q hq => h q (by simp [hq])) (by simp) (supd m o)

/-! ## Liveness and the winner -/

theorem mem_elements_iff (s : St) (x : Nat) :
    x ∈ elements s ↔ (candidates s x).Nonempty := by
  constructor
  · intro hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
    obtain ⟨hbB, hbr⟩ := Finset.mem_filter.mp hb
    exact ⟨toLex (b.1.2, b.2), Finset.mem_image.mpr
      ⟨b, Finset.mem_filter.mpr ⟨hbB, hbx, hbr⟩, rfl⟩⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb, -⟩ := Finset.mem_image.mp hc
    obtain ⟨hbB, hbx, hbr⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hbB, hbr⟩, hbx⟩

theorem winner_none_iff (pi : List D.Event) (x : Nat) :
    winner pi x = none ↔ x ∉ elements (D.applyList D.sigma0 pi) := by
  rw [mem_elements_iff, winner]
  constructor
  · intro h hne
    obtain ⟨c, hc⟩ := Finset.max_of_nonempty hne
    rw [h] at hc
    cases hc
  · intro h
    by_contra hw
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hw
    exact h ⟨c, Finset.mem_of_max hc⟩

/-! ## The winner's acquired value is the rank-three sum -/

theorem acquired_eq {pi : List D.Event} (hnd : pi.Nodup)
    (hdist : ∀ a ∈ pi, ∀ b ∈ pi, a ≠ b → a.time ≠ b.time) (x u : Nat) :
    acquired (D.applyList D.sigma0 pi) (x, u)
      = ((pi.filter (incAt x u)).map incAmount).sum := by
  have hnd' : (pi.filter (incAt x u)).Nodup := hnd.filter _
  have hinj : ∀ a ∈ pi.filter (incAt x u), ∀ b ∈ pi.filter (incAt x u),
      (((x, u) : Tag), a.time, incAmount a) = (((x, u) : Tag), b.time, incAmount b) →
      a = b := by
    intro a ha b hb heq
    by_contra hne
    exact hdist a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 hne
      (congrArg (fun z : Attachment => z.2.1) heq)
  have hmapnd := hnd'.map_on hinj
  unfold acquired
  rw [increments_filter, List.sum_toFinset _ hmapnd, List.map_map]
  rfl

theorem rank_eq_three {pi : List D.Event} {e : D.Event} {w : Lex (Nat × Int)}
    (hw : winner pi (elemOf e) = some w) :
    rank pi e = 3 ↔ incAt (elemOf e) (ofLex w).1 e = true := by
  unfold rank
  rw [hw]
  rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩
  · simp only []
    constructor
    · intro h; split at h <;> omega
    · intro h; simp [incAt, hop] at h
  · have hy : elemOf e = y := by simp [elemOf, hop]
    simp only [incAt, hop, hy, decide_eq_true_eq]
    constructor
    · intro h
      by_cases hm : (ofLex w).1 ∈ W
      · exact ⟨trivial, hm⟩
      · rw [if_neg hm] at h; exact absurd h (by omega)
    · rintro ⟨-, hm⟩
      exact if_pos hm
  · simp only []
    constructor
    · intro h; omega
    · intro h; simp [incAt, hop] at h

/-! ## Ranks when the element has no surviving insertion -/

theorem rank_le_one_of_dead {pi : List D.Event} {e : D.Event}
    (hw : winner pi (elemOf e) = none) : rank pi e ≤ 1 := by
  unfold rank
  rw [hw]
  rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;> simp only [] <;> omega

theorem rank_eq_one_of_dead {pi : List D.Event} {e : D.Event}
    (hw : winner pi (elemOf e) = none) :
    rank pi e = 1 ↔ ∃ y W, e.op = .remove y W := by
  unfold rank
  rw [hw]
  rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;> simp only []
  · exact ⟨fun h => absurd h (by omega), fun ⟨z, V, hv⟩ => absurd hv (by simp)⟩
  · exact ⟨fun h => absurd h (by omega), fun ⟨z, V, hv⟩ => absurd hv (by simp)⟩
  · exact ⟨fun _ => ⟨y, W, rfl⟩, fun _ => trivial⟩

/-- A removal of `x` in the replay disables one of `x`'s tags. -/
theorem removed_of_remove {pi : List D.Event} {x u : Nat} {e : D.Event}
    (he : e ∈ pi) {W : Finset Nat} (hop : e.op = .remove x W) (hu : u ∈ W) :
    (x, u) ∈ (D.applyList D.sigma0 pi).removed := by
  rw [state_replay]
  simp only [List.mem_toFinset, remList, List.mem_flatMap]
  refine ⟨e, he, ?_⟩
  rw [hop]
  simp only [List.mem_map, Finset.mem_toList]
  exact ⟨u, hu, rfl⟩

/-- Conversely, a disabled tag of `x` comes from a removal of `x`. -/
theorem remove_of_removed {pi : List D.Event} {x u : Nat}
    (h : (x, u) ∈ (D.applyList D.sigma0 pi).removed) :
    ∃ e ∈ pi, ∃ W, e.op = .remove x W := by
  rw [state_replay] at h
  simp only [List.mem_toFinset, remList, List.mem_flatMap] at h
  obtain ⟨e, he, hmem⟩ := h
  rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;> rw [hop] at hmem <;>
    simp only [List.mem_map, Finset.mem_toList] at hmem
  · exact absurd hmem (by simp)
  · exact absurd hmem (by simp)
  · obtain ⟨u', -, hu'⟩ := hmem
    refine ⟨e, he, W, ?_⟩
    rw [hop]
    have : y = x := congrArg Prod.fst hu'
    rw [this]

/-- An `add` of `x` whose tag is not disabled makes `x` live. -/
theorem elements_of_add {pi : List D.Event} {x : Nat} {e : D.Event} (he : e ∈ pi)
    {v : Int} (hop : e.op = .add x v)
    (hr : (x, e.time) ∉ (D.applyList D.sigma0 pi).removed) :
    x ∈ elements (D.applyList D.sigma0 pi) := by
  refine Finset.mem_image.mpr ⟨((x, e.time), v), Finset.mem_filter.mpr ⟨?_, hr⟩, rfl⟩
  rw [state_replay]
  exact List.mem_toFinset.mpr ((mem_birthList pi _).mpr ⟨e, he, by rw [hop], rfl⟩)

/-! ## The arranged replay explains the query -/

theorem filter_map_op (x : Nat) : ∀ l : List D.Event,
    (l.map Op.op).filter (fun o => decide (opElem o = x))
      = (l.filter (fun e => decide (elemOf e = x))).map Op.op
  | [] => rfl
  | e :: l => by
      by_cases h : elemOf e = x
      · have ho : opElem e.op = x := by rw [opElem_elemOf]; exact h
        simp [List.filter_cons, h, ho, filter_map_op x l]
      · have ho : ¬ opElem e.op = x := by rw [opElem_elemOf]; exact h
        simp [List.filter_cons, h, ho, filter_map_op x l]

/-- **The explaining replay gives every element the cell the implementation
reports.** -/
theorem cell_arrange {pi : List D.Event} (hnd : pi.Nodup)
    (hdist : ∀ a ∈ pi, ∀ b ∈ pi, a ≠ b → a.time ≠ b.time) (x : Nat) :
    cell (((arrange pi).map Op.op).foldl supd ((∅ : Finset Nat), fun _ => none)) x
      = (decide (x ∈ elements (D.applyList D.sigma0 pi)),
         priority (D.applyList D.sigma0 pi) x) := by
  have hperm := arrange_perm pi
  have hndA : (arrange pi).Nodup := hperm.nodup_iff.mpr hnd
  rw [cell_fold_filter, filter_map_op]
  set Lx := (arrange pi).filter (fun e => decide (elemOf e = x)) with hLx
  have hndLx : Lx.Nodup := hndA.filter _
  have hsub : ∀ a ∈ Lx, a ∈ pi := fun a ha =>
    hperm.subset (List.mem_filter.mp ha).1
  have helem : ∀ a ∈ Lx, elemOf a = x := fun a ha => by
    simpa using (List.mem_filter.mp ha).2
  obtain ⟨L0, L1, L2, L3, hsplit, h0, h1, h2, h3⟩ :=
    split_four (rank pi) (rank_le_three pi) Lx (arrange_filter_sorted pi x)
  have hmemLx : ∀ a, a ∈ L0 ∨ a ∈ L1 ∨ a ∈ L2 ∨ a ∈ L3 → a ∈ Lx := by
    intro a ha; rw [hsplit]; simp only [List.mem_append]; tauto
  have hsplitOps : (Lx.map Op.op)
      = ((L0.map Op.op ++ L1.map Op.op) ++ L2.map Op.op) ++ L3.map Op.op := by
    rw [hsplit]; simp
  rw [hsplitOps, List.foldl_append, List.foldl_append, List.foldl_append]
  rcases hw : winner pi x with _ | w
  · -- no surviving insertion
    have hdead : ∀ a ∈ Lx, winner pi (elemOf a) = none := fun a ha => by
      rw [helem a ha]; exact hw
    have hL2 : L2 = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr (fun a ha => ?_)
      have haLx : a ∈ Lx := hmemLx a (Or.inr (Or.inr (Or.inl ha)))
      have hle := rank_le_one_of_dead (hdead a haLx)
      have := h2 a ha
      omega
    have hL3 : L3 = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr (fun a ha => ?_)
      have haLx : a ∈ Lx := hmemLx a (Or.inr (Or.inr (Or.inr ha)))
      have hle := rank_le_one_of_dead (hdead a haLx)
      have := h3 a ha
      omega
    have hnotmem : x ∉ elements (D.applyList D.sigma0 pi) :=
      (winner_none_iff pi x).mp hw
    have hpri : priority (D.applyList D.sigma0 pi) x = none := by
      simp only [priority, winner] at hw ⊢; rw [hw]; rfl
    have hnorem : ∀ a ∈ Lx, (∃ y W, a.op = .remove y W) → a ∈ L1 := by
      intro a ha hrem
      have hr1 : rank pi a = 1 := (rank_eq_one_of_dead (hdead a ha)).mpr hrem
      rw [hsplit] at ha
      simp only [List.mem_append] at ha
      rcases ha with ((ha | ha) | ha) | ha
      · exact absurd (h0 a ha) (by omega)
      · exact ha
      · exact absurd (h2 a ha) (by omega)
      · exact absurd (h3 a ha) (by omega)
    rw [hL2, hL3, hpri]
    simp only [List.map_nil, List.foldl_nil,
      decide_eq_false_iff_not.mpr hnotmem]
    by_cases hL1 : L1 = []
    · have hnoremAll : ∀ a ∈ Lx, ¬ ∃ y W, a.op = .remove y W := by
        intro a ha hrem
        have := hnorem a ha hrem
        rw [hL1] at this
        exact absurd this (by simp)
      have hnoadd : ∀ a ∈ L0, ¬ ∃ v, a.op = .add x v := by
        rintro a ha ⟨v, hav⟩
        have haLx : a ∈ Lx := hmemLx a (Or.inl ha)
        refine hnotmem (elements_of_add (hsub a haLx) hav ?_)
        intro hrm
        obtain ⟨f, hf, W, hfop⟩ := remove_of_removed hrm
        have hfLx : f ∈ Lx :=
          List.mem_filter.mpr ⟨hperm.mem_iff.mpr hf, by simp [elemOf, hfop]⟩
        exact hnoremAll f hfLx ⟨x, W, hfop⟩
      have hincs : ∀ o ∈ L0.map Op.op, ∃ n W, o = .inc x n W := by
        intro o ho
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
        have haLx : a ∈ Lx := hmemLx a (Or.inl ha)
        rcases hop : a.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩
        · have hy : y = x := by rw [← helem a haLx]; simp [elemOf, hop]
          exact absurd ⟨v, by rw [hop, hy]⟩ (hnoadd a ha)
        · have hy : y = x := by rw [← helem a haLx]; simp [elemOf, hop]
          exact ⟨n, W, by rw [hy]⟩
        · exact absurd ⟨y, W, hop⟩ (hnoremAll a haLx)
      rw [hL1]
      simp only [List.map_nil, List.foldl_nil]
      rw [fold_incs_absent _ hincs rfl]
      rfl
    · have hrems : ∀ o ∈ L1.map Op.op, ∃ W, o = .remove x W := by
        intro o ho
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
        have haLx : a ∈ Lx := hmemLx a (Or.inr (Or.inl ha))
        obtain ⟨y, W, hyW⟩ := (rank_eq_one_of_dead (hdead a haLx)).mp (h1 a ha)
        have hy : y = x := by rw [← helem a haLx]; simp [elemOf, hyW]
        exact ⟨W, by rw [hyW, hy]⟩
      exact fold_removes _ hrems (by simpa using hL1) _
  · -- a surviving insertion
    obtain ⟨es, hesPi, hesOp, hesTime⟩ := winner_event hw
    have hesElem : elemOf es = x := by simp [elemOf, hesOp]
    have hesLx : es ∈ Lx :=
      List.mem_filter.mpr ⟨hperm.mem_iff.mpr hesPi, by simpa using hesElem⟩
    have hwElem : ∀ a ∈ Lx, winner pi (elemOf a) = some w := fun a ha => by
      rw [helem a ha]; exact hw
    have hesRank : rank pi es = 2 :=
      (rank_eq_two (hwElem es hesLx)).mpr ⟨⟨_, by rw [hesOp, hesElem]⟩, hesTime⟩
    have hesL2 : es ∈ L2 := by
      rw [hsplit] at hesLx
      simp only [List.mem_append] at hesLx
      rcases hesLx with ((ha | ha) | ha) | ha
      · exact absurd (h0 es ha) (by omega)
      · exact absurd (h1 es ha) (by omega)
      · exact ha
      · exact absurd (h3 es ha) (by omega)
    have hL2single : L2 = [es] := by
      refine eq_singleton_of_all_eq ?_ hesL2 ?_
      · rw [hsplit] at hndLx
        simp only [List.nodup_append] at hndLx
        tauto
      · intro a ha
        have haLx : a ∈ Lx := hmemLx a (Or.inr (Or.inr (Or.inl ha)))
        obtain ⟨⟨v, hav⟩, hat⟩ := (rank_eq_two (hwElem a haLx)).mp (h2 a ha)
        by_contra hne
        exact hdist a (hsub a haLx) es hesPi hne (by rw [hat, hesTime])
    have hincs : ∀ o ∈ L3.map Op.op, ∃ n W, o = .inc x n W := by
      intro o ho
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
      have haLx : a ∈ Lx := hmemLx a (Or.inr (Or.inr (Or.inr ha)))
      have hinc := (rank_eq_three (hwElem a haLx)).mp (h3 a ha)
      rcases hop : a.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
        simp only [incAt, hop, helem a haLx, decide_eq_true_eq] at hinc
      · exact absurd hinc (by simp)
      · exact ⟨n, W, by rw [hinc.1]⟩
      · exact absurd hinc (by simp)
    rw [hL2single]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [hesOp]
    rw [fold_incs_present _ hincs (cell_add _ x (ofLex w).2)]
    have hmem : x ∈ elements (D.applyList D.sigma0 pi) := by
      by_contra hc
      rw [(winner_none_iff pi x).mpr hc] at hw
      cases hw
    have hsum : (List.map (fun o => match o with | .inc _ n _ => n | _ => 0)
        (L3.map Op.op)).sum = acquired (D.applyList D.sigma0 pi) (x, (ofLex w).1) := by
      rw [acquired_eq hnd hdist]
      rw [List.map_map]
      refine List.Perm.sum_eq ?_
      refine (List.Perm.map _ ?_)
      have hL3eq : L3 = Lx.filter (fun a => decide (rank pi a = 3)) := by
        rw [hsplit]
        simp only [List.filter_append]
        rw [List.filter_eq_nil_iff.mpr (fun a ha => by simp [h0 a ha]),
          List.filter_eq_nil_iff.mpr (fun a ha => by simp [h1 a ha]),
          List.filter_eq_nil_iff.mpr (fun a ha => by simp [h2 a ha]),
          List.filter_eq_self.mpr (fun a ha => by simp [h3 a ha])]
        simp
      rw [hL3eq, hLx, List.filter_filter]
      refine ((hperm.filter _).trans ?_)
      refine List.Perm.of_eq ?_
      refine List.filter_congr (fun a ha => ?_)
      by_cases hinc : incAt x (ofLex w).1 a = true
      · have helemA : elemOf a = x := by
          rcases hop : a.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
            simp only [incAt, hop, decide_eq_true_eq] at hinc
          · exact absurd hinc (by simp)
          · simp [elemOf, hop, hinc.1]
          · exact absurd hinc (by simp)
        have hwa : winner pi (elemOf a) = some w := by rw [helemA]; exact hw
        have : rank pi a = 3 := (rank_eq_three hwa).mpr (by rw [helemA]; exact hinc)
        simp [hinc, helemA, this]
      · simp only [Bool.not_eq_true] at hinc
        by_cases helemA : elemOf a = x
        · have : rank pi a ≠ 3 := by
            intro hr
            have := (rank_eq_three (by rw [helemA]; exact hw)).mp hr
            rw [helemA] at this
            rw [this] at hinc
            exact absurd hinc (by simp)
          simp [hinc, helemA, this]
        · simp [hinc, helemA]
    rw [hsum]
    have hpri : priority (D.applyList D.sigma0 pi) x
        = some ((ofLex w).2 + acquired (D.applyList D.sigma0 pi) (x, (ofLex w).1)) := by
      simp only [priority, winner] at hw ⊢
      rw [hw]
      rfl
    rw [hpri, decide_eq_true_iff.mpr hmem]

/-! ## Clause 2 -/

theorem spec_state_eq {pi : List D.Event} (hnd : pi.Nodup)
    (hdist : ∀ a ∈ pi, ∀ b ∈ pi, a ≠ b → a.time ≠ b.time) :
    ((arrange pi).map Op.op).foldl supd ((∅ : Finset Nat), fun _ => none)
      = (elements (D.applyList D.sigma0 pi), priority (D.applyList D.sigma0 pi)) := by
  refine Prod.ext ?_ ?_
  · ext y
    have h := congrArg Prod.fst (cell_arrange hnd hdist y)
    simpa [cell] using h
  · funext y
    exact congrArg Prod.snd (cell_arrange hnd hdist y)

/-- **The arranged replay answers every query as the implementation does.** -/
theorem query_agrees {pi : List D.Event} (hnd : pi.Nodup)
    (hdist : ∀ a ∈ pi, ∀ b ∈ pi, a ≠ b → a.time ≠ b.time) (q : type.QType) :
    D.query (D.applyList D.sigma0 (arrange pi)) q
      = specMachine.query
          (((arrange pi).map Op.op).foldl specMachine.update specMachine.initial) q := by
  rw [show specMachine.initial = ((∅ : Finset Nat), fun _ => none) from rfl,
    show specMachine.update = supd from rfl, spec_state_eq hnd hdist,
    state_perm (arrange_perm pi)]
  cases q <;> rfl

/-- **The sequential premise, execution-scoped.** The row chooses the
history that reconciles the two: each element's removals, then its losing
additions and increments, then the winning addition, then exactly that
insertion's increments. -/
theorem historySound : Soundness.HistorySound D historySpec issuance := by
  rintro C hmint E hsub hclosed ⟨pi, hpi⟩ q
  have hev : ∀ a ∈ pi, a ∈ C.replayContext.events := by
    intro a ha
    rw [Configuration.replayContext_events]
    exact hsub a ((hpi.2 a).mp ha)
  have hdist : ∀ a ∈ pi, ∀ b ∈ pi, a ≠ b → a.time ≠ b.time :=
    fun a ha b hb hne => time_ne (hev a ha) (hev b hb) hne
  refine ⟨arrange pi, ?_, ?_, ?_⟩
  · exact ⟨(arrange_perm pi).nodup_iff.mpr hpi.1,
      fun a => ((arrange_perm pi).mem_iff).trans (hpi.2 a)⟩
  · exact ((arrange_perm pi).nodup_iff.mpr hpi.1).imp
      (fun {_ _} _ => Soundness.paperOrder_false rc_non_comm_uniform all_commute _ _ _ _)
  · rw [show projectedUpdates (D := D.toMRDTSig) (arrange pi)
          = DeterministicSpec.updateLabels ((arrange pi).map Op.op) from by
        simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
          Function.comp],
      historySpec, specMachine.updates_query_iff]
    exact query_agrees hpi.1 hdist q

end LeanProofs1.Implementations.PriorityQueue
