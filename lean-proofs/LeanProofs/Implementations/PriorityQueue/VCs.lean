import LeanProofs_no_spec_non_comm.Implementations.PriorityQueue.Definition
import LeanProofs_no_spec_non_comm.Interface.VCRoute
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything up to the last section is
`Implementations/PriorityQueue/VCs.lean` with the namespace changed. The
last section is what this folder adds, and for this row alone it is a
**second order**, not a clause bolted onto the first: the history
Definition 4 uses here inverts a specification-visibility arrow, so the
answer has to be reproved at an order that does not.

# The priority queue: `Laws(D_type)` and VC1 to VC5

All three stores are grow-only and each effect inserts into exactly one of
them, so every pair of events commutes and `rc` is empty. `Laws(D_type)` is
then immediate, and the five conditions are identities among finite unions.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.PriorityQueue

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

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
theorem chosenOrderSound : Soundness.ChosenOrderSound D historySpec issuance := by
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

/-! ## SPEC-NON-COMM fails here

`all_commute` says every pair of events commutes in the implementation, so
SPEC-NON-COMM collapses to the demand that every pair of specification
updates commute. Two additions of one element do not: the specification
keeps the innate value of the later one in the history, while the
implementation resolves them by the greater timestamp.

Nothing downstream consumes SPEC-NON-COMM, so the certificate is unaffected.
What the failure costs is the stronger criterion of
`Artifact/MRDTs/Paper1/SpecificationVisibility.lean`, which this row cannot
reach, and it is why the row needs `Soundness.ChosenOrderSound` rather than
`Soundness.AnyOrderSound`. -/

/-- Two additions of one element do not commute in `Spec`: the priority read
at the end of the history tells the two orders apart. -/
theorem not_spec_commutes :
    ¬ Interface.spec_commutes historySpec (.add 0 0) (.add 0 1) := by
  intro h
  have lhs : historySpec.admits
      ([SeqLabel.update (AppOp.add 0 0), .update (.add 0 1)]
        ++ [.query (.getPri 0) (.priority (some 1))]) :=
    (specMachine.updates_query_iff [.add 0 0, .add 0 1] (.getPri 0)
      (.priority (some 1))).mpr (by simp [specMachine])
  have rhs := (h [] [SeqLabel.query (.getPri 0) (.priority (some 1))]).mp
    (by simpa using lhs)
  have key : (Answer.priority (some 1)) = .priority (some 0) :=
    (specMachine.updates_query_iff [AppOp.add 0 1, .add 0 0] (.getPri 0)
      (.priority (some 1))).mp (by simpa using rhs)
  simp at key

/-- **SPEC-NON-COMM fails for the priority queue.** The two additions commute
in the implementation and do not commute in `Spec`. -/
theorem not_spec_non_comm : ¬ Interface.spec_non_comm D historySpec := fun h =>
  h (0, 0, .add 0 0) (1, 1, .add 0 1) not_spec_commutes (all_commute _ _)

/-! # Specification visibility

The order above is the one Definition 4 asks for, and it is **not**
specification-visibility respecting. `rank` sorts a deletion before the
addition it disabled, and a deletion disables an addition only by observing
it, so the chosen history inverts a `vis` arrow that `Spec` separates.
`rank_remove_lt_rank_losing_add` and `not_spec_commutes_add_remove` below
are those two sentences.

So this row needs a second order, which the rest of the file builds. The
repair is to stop grouping by rank-with-deletions-first and sort
chronologically instead, pulling out only what chronology gets wrong: the
winning addition may be concurrent with a later losing addition, and the
losing one must not overwrite it. `srank` is that order, three blocks
instead of four, and the order clause then follows from `causal_mono`
alone, inside each block, together with issuance across the blocks.
-/


/-- **An addition and a deletion of one element do not commute in `Spec`.**
Taken in one order the element is gone, in the other it is present, and a
lookup at the end of the history tells them apart. -/
theorem not_spec_commutes_add_remove :
    ¬ historySpec.Commutes (AppOp.add 0 0) (AppOp.remove 0 ∅) := by
  intro h
  have lhs : historySpec.admits
      ([SeqLabel.update (AppOp.add 0 0), .update (.remove 0 ∅)]
        ++ [.query (.lookup 0) (.boolean false)]) :=
    (specMachine.updates_query_iff [.add 0 0, .remove 0 ∅] (.lookup 0)
      (.boolean false)).mpr (by simp [specMachine])
  have rhs := (h [] [SeqLabel.query (.lookup 0) (.boolean false)]).mp (by simpa using lhs)
  have key := (specMachine.updates_query_iff [AppOp.remove 0 ∅, .add 0 0] (.lookup 0)
      (.boolean false)).mp (by simpa using rhs)
  simp [specMachine] at key

/-- **With a live winner, deletions sort before losing additions.** So
`arrange` puts the deletion first, although the deletion observed the
addition it disabled. -/
theorem rank_remove_lt_rank_losing_add {pi : List D.Event} {r a : D.Event}
    {x : Nat} {W : Finset Nat} {v : Int} {b : Lex (Nat × Int)}
    (hw : winner pi x = some b) (hrx : elemOf r = x) (hax : elemOf a = x)
    (hr : r.op = .remove x W) (ha : a.op = .add x v)
    (hlose : a.time ≠ (ofLex b).1) :
    rank pi r < rank pi a := by
  simp only [rank, hrx, hax, hw, hr, ha, if_neg hlose]
  norm_num


/-! ## Operations of different elements commute in `Spec`

Every specification-visibility arrow this row has to respect joins two
events of **one** element, because the specification's cells are
independent. That is what lets the order below sort globally and still
argue one element at a time. -/

/-- The increment step in closed form, so that no `match` is left to block
rewriting. -/
theorem supd_inc (m : SpecState) (x : Nat) (n : Int) (W : Finset Nat) :
    supd m (.inc x n W)
      = (m.1, fun y => if y = x then (m.2 x).map (fun v => v + n) else m.2 y) := by
  show (match m.2 x with
      | some v => (m.1, fun z => if z = x then some (v + n) else m.2 z)
      | none => m) = _
  cases hx : m.2 x <;>
    refine Prod.ext rfl (funext fun z => ?_) <;>
    by_cases hz : z = x <;> simp [hz, hx]

/-- Two updates of different elements commute on the specification's
state. -/
theorem supd_comm_of_ne {o₁ o₂ : type.OType} (h : opElem o₁ ≠ opElem o₂)
    (m : SpecState) : supd (supd m o₁) o₂ = supd (supd m o₂) o₁ := by
  rcases o₁ with ⟨x, v⟩ | ⟨x, n, W⟩ | ⟨x, W⟩ <;>
    rcases o₂ with ⟨y, v'⟩ | ⟨y, n', W'⟩ | ⟨y, W'⟩ <;>
    simp only [opElem, ne_eq] at h <;>
    simp only [supd_add, supd_rem, supd_inc] <;>
    refine Prod.ext (by
      simp [Finset.insert_comm, Finset.erase_right_comm, Finset.erase_insert_of_ne,
        h, Ne.symm h]) (funext fun z => ?_) <;>
    by_cases hzx : z = x <;> by_cases hzy : z = y <;>
    simp_all

/-- **Different elements commute in `Spec`.** So a specification conflict
names one element twice. -/
theorem spec_commutes_of_ne_elem {o₁ o₂ : type.OType} (h : opElem o₁ ≠ opElem o₂) :
    historySpec.Commutes o₁ o₂ :=
  specMachine.language_commutes o₁ o₂ (fun m => supd_comm_of_ne h m)

/-- The contrapositive, at events: a specification conflict is local. -/
theorem elemOf_eq_of_not_commutes {a b : D.Event}
    (h : ¬ historySpec.Commutes a.op b.op) : elemOf a = elemOf b := by
  by_contra hne
  exact h (spec_commutes_of_ne_elem (by rwa [opElem_elemOf, opElem_elemOf]))

/-! ## What an honest issuer knows

The order below rests on issuance, not on a law. Two directions are needed.
Forwards: a tag a visible event minted is **observed** by the issuer, unless
it has already been disabled, so the issuer's own observed set names it.
Backwards: every tag an issuer observes was minted by a visible event, which
is what puts the minting event earlier in time. -/

/-- A tag is observed exactly when it is live. -/
theorem mem_observed_iff (s : St) (x u : Nat) :
    u ∈ observed s x ↔ ((x, u) : Tag) ∈ liveTags s := by
  simp only [observed, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, htx⟩, rfl⟩
    rwa [← htx]
  · intro h
    exact ⟨(x, u), ⟨h, rfl⟩, rfl⟩

/-- An `add` of the replay puts its own tag in the record. -/
theorem mem_recordTags_add {pi : List D.Event} {e : D.Event} (he : e ∈ pi)
    {x : Nat} {v : Int} (hop : e.op = .add x v) :
    ((x, e.time) : Tag) ∈ recordTags (D.applyList D.sigma0 pi) := by
  refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨((x, e.time), v), ?_, rfl⟩)
  rw [state_replay]
  exact List.mem_toFinset.mpr ((mem_birthList pi _).mpr ⟨e, he, by rw [hop], rfl⟩)

/-- An `inc` of the replay puts every tag it names in the record. -/
theorem mem_recordTags_inc {pi : List D.Event} {e : D.Event} (he : e ∈ pi)
    {x u : Nat} {n : Int} {W : Finset Nat} (hop : e.op = .inc x n W) (hu : u ∈ W) :
    ((x, u) : Tag) ∈ recordTags (D.applyList D.sigma0 pi) := by
  refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨((x, u), e.time, n), ?_, rfl⟩)
  rw [state_replay]
  refine List.mem_toFinset.mpr ((mem_incList pi _).mpr ⟨e, he, ?_, ?_⟩)
  · simp [incAt, hop, hu]
  · simp [incAmount, hop]

/-- Conversely, a tag in the record comes from an `add` that minted it or an
`inc` that named it. -/
theorem mem_recordTags_elim {pi : List D.Event} {x u : Nat}
    (h : ((x, u) : Tag) ∈ recordTags (D.applyList D.sigma0 pi)) :
    (∃ e ∈ pi, ∃ v, e.op = .add x v ∧ e.time = u) ∨
      (∃ e ∈ pi, ∃ n W, e.op = .inc x n W ∧ u ∈ W) := by
  rcases Finset.mem_union.mp h with hb | hi
  · obtain ⟨b, hb, hbt⟩ := Finset.mem_image.mp hb
    rw [state_replay] at hb
    obtain ⟨e, he, hop, ht⟩ := (mem_birthList pi b).mp (by simpa using hb)
    refine Or.inl ⟨e, he, b.2, ?_, ?_⟩
    · rw [hop, show b.1.1 = x from congrArg Prod.fst hbt]
    · rw [← ht, show b.1.2 = u from congrArg Prod.snd hbt]
  · obtain ⟨a, ha, hat⟩ := Finset.mem_image.mp hi
    rw [state_replay] at ha
    obtain ⟨e, he, hinc, -⟩ := (mem_incList pi a).mp (by simpa using ha)
    have hx : a.1.1 = x := congrArg Prod.fst hat
    have hu : a.1.2 = u := congrArg Prod.snd hat
    rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
      simp only [incAt, hop, decide_eq_true_eq] at hinc
    · exact absurd hinc (by simp)
    · exact Or.inr ⟨e, he, n, W, by rw [hop, hinc.1, hx], by rw [← hu]; exact hinc.2⟩
    · exact absurd hinc (by simp)

/-- Replaying fewer events disables fewer tags. -/
theorem removed_subset {pi rho : List D.Event} (h : ∀ a ∈ pi, a ∈ rho) :
    (D.applyList D.sigma0 pi).removed ⊆ (D.applyList D.sigma0 rho).removed := by
  intro t ht
  rw [state_replay] at ht ⊢
  simp only [List.mem_toFinset, remList, List.mem_flatMap] at ht ⊢
  obtain ⟨e, he, hmem⟩ := ht
  exact ⟨e, h e he, hmem⟩

/-! ## Issuance at an honest event -/

section Honest

variable {C : Configuration D.toMRDTSig}

/-- `MintHonest` unpacked: every event was issuable at a replay of exactly
its visible past. -/
theorem canIssue_of_mint (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {e : D.Event} (he : e ∈ C.events) :
    ∃ pi : List D.Event, (∀ a ∈ pi, a ∈ C.events ∧ C.vis a e) ∧
      (∀ a, a ∈ C.events → C.vis a e → a ∈ pi) ∧
      issuance.CanIssue e (D.applyList D.sigma0 pi) := by
  obtain ⟨pi, hpi, -, hg⟩ := hmint e he
  exact ⟨pi, fun a ha => by simpa using (hpi.2 a).mp ha,
    fun a hc hv => (hpi.2 a).mpr (by simpa using ⟨hc, hv⟩), hg⟩

/-- **Backwards.** Every tag an honest issuer knows was minted by a visible
event. Induction on the issuer's timestamp: a tag in the birth store names
the `add` that minted it, and a tag in the attachment store was named by a
visible `inc`, which observed it, so the hypothesis applies at that strictly
earlier event. -/
theorem tag_mint (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    (hvs : VisStrict D C.replayContext) :
    ∀ t : Nat, ∀ e : D.Event, e.time ≤ t → e ∈ C.events → ∀ x u : Nat,
      ∀ pi : List D.Event, (∀ a ∈ pi, a ∈ C.events ∧ C.vis a e) →
      ((x, u) : Tag) ∈ recordTags (D.applyList D.sigma0 pi) →
      ∃ c, c ∈ C.events ∧ c.time = u ∧ C.vis c e := by
  intro t
  induction t with
  | zero =>
      intro e het he x u pi hpi hmem
      rcases mem_recordTags_elim hmem with ⟨c, hc, v, hop, ht⟩ | ⟨c, hc, n, W, hop, hu⟩
      · exact ⟨c, (hpi c hc).1, ht, (hpi c hc).2⟩
      · exact absurd (C.causal_mono (hpi c hc).2)
          (Nat.not_lt.mpr (Nat.le_trans het (Nat.zero_le _)))
  | succ t ih =>
      intro e het he x u pi hpi hmem
      rcases mem_recordTags_elim hmem with ⟨c, hc, v, hop, ht⟩ | ⟨c, hc, n, W, hop, hu⟩
      · exact ⟨c, (hpi c hc).1, ht, (hpi c hc).2⟩
      · obtain ⟨hcC, hcv⟩ := hpi c hc
        have hlt : c.time < e.time := C.causal_mono hcv
        obtain ⟨rho, hrho, -, hg⟩ := canIssue_of_mint hmint hcC
        simp only [issuance, hop] at hg
        have hmem' : ((x, u) : Tag) ∈ recordTags (D.applyList D.sigma0 rho) :=
          (Finset.mem_sdiff.mp ((mem_observed_iff _ x u).mp (hg.2 ▸ hu))).1
        obtain ⟨c', hc'C, hc't, hc'v⟩ :=
          ih c (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt het)) hcC x u rho hrho hmem'
        exact ⟨c', hc'C, hc't, hvs.1 hc'v hcv⟩

/-- **Forwards.** A tag a visible event minted or named, still live at the
end, is observed by the issuer. -/
theorem mem_observed_of_record {pi rho : List D.Event}
    (hsub : ∀ b ∈ pi, b ∈ rho) {x u : Nat}
    (hmem : ((x, u) : Tag) ∈ recordTags (D.applyList D.sigma0 pi))
    (hlive : ((x, u) : Tag) ∉ (D.applyList D.sigma0 rho).removed) :
    u ∈ observed (D.applyList D.sigma0 pi) x :=
  (mem_observed_iff _ x u).mpr
    (Finset.mem_sdiff.mpr ⟨hmem, fun hr => hlive (removed_subset hsub hr)⟩)

/-- The winning insertion's tag is live. -/
theorem winner_tag_live {pi : List D.Event} {x : Nat} {w : Lex (Nat × Int)}
    (hw : winner pi x = some w) :
    ((x, (ofLex w).1) : Tag) ∉ (D.applyList D.sigma0 pi).removed := by
  have hmem : w ∈ candidates (D.applyList D.sigma0 pi) x := Finset.mem_of_max hw
  simp only [candidates, Finset.mem_image, Finset.mem_filter] at hmem
  obtain ⟨b, ⟨-, hbx, hbr⟩, hbw⟩ := hmem
  have h1 : (ofLex w).1 = b.1.2 := by rw [← hbw]; rfl
  rw [h1, show ((x, b.1.2) : Tag) = b.1 from by rw [← hbx]]
  exact hbr

end Honest

/-! ## The specification-respecting order

Three blocks instead of four, and chronological inside each:

```
  0   every event of the element except the winning addition and the
      increments attached to it
  1   the winning addition
  2   those increments
```

Chronology is what block 0 needs, because `causal_mono` then orders it. The
winning addition has to leave that block, because it may be concurrent with
a losing addition of a later timestamp, which would otherwise overwrite it;
and its increments follow it, because an increment attached to it observed
it. Nothing else of the element is `vis`-after it, which is the content of
`attached_of_vis`.

The element is **not** part of the key. It need not be: filtering preserves
sortedness, so each element's events are still sorted by `(srank, time)`
after the filter, and a specification conflict joins two events of one
element by `elemOf_eq_of_not_commutes`. -/

/-- The rank of an event in the specification-respecting order. -/
noncomputable def srank (pi : List D.Event) (e : D.Event) : Nat :=
  match winner pi (elemOf e) with
  | none => 0
  | some b => match e.op with
      | .add _ _ => if e.time = (ofLex b).1 then 1 else 0
      | .inc _ _ W => if (ofLex b).1 ∈ W then 2 else 0
      | .remove _ _ => 0

theorem srank_le_two (pi : List D.Event) (e : D.Event) : srank pi e ≤ 2 := by
  unfold srank
  rcases winner pi (elemOf e) with _ | b <;>
    rcases e.op with ⟨x, v⟩ | ⟨x, n, W⟩ | ⟨x, W⟩ <;>
    simp only [] <;> first | omega | (split_ifs <;> omega)

/-- With no surviving insertion every event sits in block 0. -/
theorem srank_eq_zero_of_dead {pi : List D.Event} {e : D.Event}
    (hw : winner pi (elemOf e) = none) : srank pi e = 0 := by
  unfold srank
  rw [hw]

/-- Block 1 is the winning insertion's own addition. -/
theorem srank_eq_one {pi : List D.Event} {e : D.Event} {w : Lex (Nat × Int)}
    (hw : winner pi (elemOf e) = some w) :
    srank pi e = 1 ↔ (∃ v, e.op = .add (elemOf e) v) ∧ e.time = (ofLex w).1 := by
  unfold srank
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

/-- Block 2 is the increments attached to that insertion. -/
theorem srank_eq_two {pi : List D.Event} {e : D.Event} {w : Lex (Nat × Int)}
    (hw : winner pi (elemOf e) = some w) :
    srank pi e = 2 ↔ incAt (elemOf e) (ofLex w).1 e = true := by
  unfold srank
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

/-- The comparator: rank first, then timestamp. -/
noncomputable def scmp (pi : List D.Event) (a b : D.Event) : Bool :=
  leKey (srank pi a, a.time) (srank pi b, b.time)

/-- The specification-respecting replay. -/
noncomputable def sarrange (pi : List D.Event) : List D.Event :=
  pi.mergeSort (scmp pi)

theorem sarrange_perm (pi : List D.Event) : (sarrange pi).Perm pi :=
  List.mergeSort_perm _ _

theorem sarrange_sorted (pi : List D.Event) :
    (sarrange pi).Pairwise (fun a b => scmp pi a b = true) :=
  List.pairwise_mergeSort (le := scmp pi)
    (fun _ _ _ hab hbc => leKey_trans hab hbc) (fun _ _ => leKey_total _ _) pi

/-- The order, read off the comparator. -/
theorem scmp_iff {pi : List D.Event} {a b : D.Event} :
    scmp pi a b = true ↔
      srank pi a < srank pi b ∨ (srank pi a = srank pi b ∧ a.time ≤ b.time) := by
  simp [scmp, leKey]

/-- Restricted to one element, the replay is still sorted by rank and then
by time, because filtering preserves sortedness. -/
theorem sarrange_filter_sorted (pi : List D.Event) (x : Nat) :
    ((sarrange pi).filter (fun e => decide (elemOf e = x))).Pairwise
      (fun a b => srank pi a < srank pi b ∨
        (srank pi a = srank pi b ∧ a.time ≤ b.time)) :=
  ((sarrange_sorted pi).filter _).imp (fun {_ _} h => scmp_iff.mp h)

/-! ## The three rank blocks -/

theorem split_three {α : Type} (f : α → Nat) (hle : ∀ a, f a ≤ 2) : ∀ (L : List α),
    L.Pairwise (fun a b => f a ≤ f b) →
    ∃ L0 L1 L2, L = L0 ++ L1 ++ L2
      ∧ (∀ a ∈ L0, f a = 0) ∧ (∀ a ∈ L1, f a = 1) ∧ (∀ a ∈ L2, f a = 2) := by
  intro L h
  obtain ⟨L0, R1, hL0, h0, h0'⟩ := split_sorted f 0 L h
  have hR1 : R1.Pairwise (fun a b => f a ≤ f b) := by
    rw [hL0] at h; exact (List.pairwise_append.mp h).2.1
  obtain ⟨L1, L2, hL1, h1, h1'⟩ := split_sorted f 1 R1 hR1
  refine ⟨L0, L1, L2, by rw [hL0, hL1]; simp, ?_, ?_, ?_⟩
  · intro a ha; have := h0 a ha; omega
  · intro a ha
    have hlo := h0' a (by rw [hL1]; simp [ha])
    have := h1 a ha; omega
  · intro a ha
    have hlo := h1' a ha
    have := hle a; omega

/-! ## A dead element's chronological block ends absent -/

/-- **A chronological block of a dead element ends with the cell absent.**
Forward induction, carrying the disjunct "or a deletion is still to come".
An addition restores that disjunct, because every addition of a dead element
is disabled by a deletion of a later timestamp, which is
`removal_after_add`. An increment preserves it, and a deletion discharges
it. -/
theorem cell_dead {x : Nat} : ∀ (L : List D.Event),
    (∀ a ∈ L, elemOf a = x) →
    L.Pairwise (fun a b => a.time ≤ b.time) →
    (∀ a ∈ L, ∀ v, a.op = .add x v →
      ∃ f ∈ L, (∃ W, f.op = .remove x W) ∧ a.time < f.time) →
    ∀ m : SpecState, (cell m x = (false, none) ∨ ∃ f ∈ L, ∃ W, f.op = .remove x W) →
    cell ((L.map Op.op).foldl supd m) x = (false, none)
  | [], _, _, _, m, hm => by
      rcases hm with h | ⟨f, hf, -⟩
      · simpa using h
      · exact absurd hf (by simp)
  | c :: L, helem, hsort, hkill, m, hm => by
      have hcx : elemOf c = x := helem c (by simp)
      have hlater : ∀ a ∈ L, c.time ≤ a.time := (List.pairwise_cons.mp hsort).1
      have hkill' : ∀ a ∈ L, ∀ v, a.op = .add x v →
          ∃ f ∈ L, (∃ W, f.op = .remove x W) ∧ a.time < f.time := by
        intro a ha v hav
        obtain ⟨f, hf, hfr, hft⟩ := hkill a (by simp [ha]) v hav
        refine ⟨f, ?_, hfr, hft⟩
        rcases List.mem_cons.mp hf with rfl | hf
        · exact absurd (hlater a ha) (Nat.not_le.mpr hft)
        · exact hf
      refine cell_dead L (fun a ha => helem a (by simp [ha]))
        (List.pairwise_cons.mp hsort).2 hkill' (supd m c.op) ?_
      rcases hop : c.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩
      · have hy : y = x := by rw [← hcx]; simp [elemOf, hop]
        rw [hy] at hop
        obtain ⟨f, hf, hfr, hft⟩ := hkill c (by simp) v hop
        refine Or.inr ⟨f, ?_, hfr⟩
        rcases List.mem_cons.mp hf with rfl | hf
        · exact absurd hft (Nat.lt_irrefl _)
        · exact hf
      · have hy : y = x := by rw [← hcx]; simp [elemOf, hop]
        rcases hm with h | ⟨f, hf, V, hfr⟩
        · refine Or.inl ?_
          rw [hy]
          exact (cell_inc_absent n W (by rw [h])).trans h
        · refine Or.inr ⟨f, ?_, V, hfr⟩
          rcases List.mem_cons.mp hf with rfl | hf
          · rw [hop] at hfr; exact absurd hfr (by simp)
          · exact hf
      · have hy : y = x := by rw [← hcx]; simp [elemOf, hop]
        refine Or.inl ?_
        rw [hy]
        exact cell_remove m x W

/-! ## Nothing follows the winning insertion but its own increments -/

section Honest

variable {C : Configuration D.toMRDTSig}

/-- **The winning insertion is observed by every later event of its
element.** Its tag is live at the end, so it is live at any issuer whose
past knows it, so that issuer's observed set names it. An addition could
then not have issued, a deletion would have disabled the winner, so the
event is an increment attached to it. -/
theorem attached_of_vis (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {pi : List D.Event} (hpi : listPermOf pi E) (hev : ∀ a ∈ pi, a ∈ C.events)
    {x : Nat} {w : Lex (Nat × Int)} (hw : winner pi x = some w)
    {a b : D.Event} (ha : a ∈ pi) (hvis : C.vis b a) (hax : elemOf a = x)
    (hknows : (∃ v, b.op = .add x v ∧ b.time = (ofLex w).1)
      ∨ (∃ n W, b.op = .inc x n W ∧ (ofLex w).1 ∈ W)) :
    incAt x (ofLex w).1 a = true := by
  obtain ⟨rho, hrhoC, hrhoAll, hg⟩ := canIssue_of_mint hmint (hev a ha)
  have hbrho : b ∈ rho := hrhoAll b (C.vis_src hvis) hvis
  have hmemrec : ((x, (ofLex w).1) : Tag) ∈ recordTags (D.applyList D.sigma0 rho) := by
    rcases hknows with ⟨v, hop, ht⟩ | ⟨n, W, hop, hmem⟩
    · rw [← ht]; exact mem_recordTags_add hbrho hop
    · exact mem_recordTags_inc hbrho hop hmem
  have hsub : ∀ c ∈ rho, c ∈ pi := by
    intro c hc
    exact (hpi.2 c).mpr (hclosed c a (hrhoC c hc).2 ((hpi.2 a).mp ha))
  have hobs : (ofLex w).1 ∈ observed (D.applyList D.sigma0 rho) x :=
    mem_observed_of_record hsub hmemrec (winner_tag_live hw)
  rcases hop : a.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩
  · have hy : y = x := by rw [← hax]; simp [elemOf, hop]
    simp only [issuance, hop] at hg
    rw [hy] at hg
    rw [hg] at hobs
    exact absurd hobs (by simp)
  · have hy : y = x := by rw [← hax]; simp [elemOf, hop]
    simp only [issuance, hop] at hg
    rw [hy] at hg hop
    simp [incAt, hop, hg.2 ▸ hobs]
  · have hy : y = x := by rw [← hax]; simp [elemOf, hop]
    simp only [issuance, hop] at hg
    rw [hy] at hg hop
    exact absurd (removed_of_remove ha hop (hg.2 ▸ hobs)) (winner_tag_live hw)

end Honest

/-! ## The explaining replay at the new order -/

/-- A disabled tag of `x` comes from a removal of `x` that names it. -/
theorem remove_of_removed' {pi : List D.Event} {x u : Nat}
    (h : (x, u) ∈ (D.applyList D.sigma0 pi).removed) :
    ∃ e ∈ pi, ∃ W, e.op = .remove x W ∧ u ∈ W := by
  rw [state_replay] at h
  simp only [List.mem_toFinset, remList, List.mem_flatMap] at h
  obtain ⟨e, he, hmem⟩ := h
  rcases hop : e.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;> rw [hop] at hmem <;>
    simp only [List.mem_map, Finset.mem_toList] at hmem
  · exact absurd hmem (by simp)
  · exact absurd hmem (by simp)
  · obtain ⟨u', hu', heq⟩ := hmem
    have hy : y = x := congrArg Prod.fst heq
    have hu : u' = u := congrArg Prod.snd heq
    exact ⟨e, he, W, by rw [hop, hy], hu ▸ hu'⟩

section Honest

variable {C : Configuration D.toMRDTSig}

/-- **A deletion that disables an addition is later in time.** The deletion
observed the addition's tag, so by `tag_mint` the event that minted that tag
is visible to the deletion, and timestamps are distinct, so that event is
the addition itself. -/
theorem removal_after_add (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    (hvs : VisStrict D C.replayContext) {pi : List D.Event}
    (hev : ∀ a ∈ pi, a ∈ C.events) {a f : D.Event} (ha : a ∈ pi) (hf : f ∈ pi)
    {x : Nat} {v : Int} {W : Finset Nat}
    (hav : a.op = .add x v) (hfr : f.op = .remove x W) (hmem : a.time ∈ W) :
    a.time < f.time := by
  obtain ⟨rho, hrhoC, -, hg⟩ := canIssue_of_mint hmint (hev f hf)
  simp only [issuance, hfr] at hg
  have hrec : ((x, a.time) : Tag) ∈ recordTags (D.applyList D.sigma0 rho) :=
    (Finset.mem_sdiff.mp ((mem_observed_iff _ x a.time).mp (hg.2 ▸ hmem))).1
  obtain ⟨c, hcC, hct, hcv⟩ :=
    tag_mint hmint hvs f.time f le_rfl (hev f hf) x a.time rho hrhoC hrec
  have hca : c = a := by
    by_contra hne
    exact time_ne (C := C.replayContext)
      (by rw [Configuration.replayContext_events]; exact hcC)
      (by rw [Configuration.replayContext_events]; exact hev a ha) hne hct
  exact C.causal_mono (hca ▸ hcv)

/-- **The replay at the new order gives every element the cell the
implementation reports.** The live case is the old argument with one block
fewer, because the winning addition still overwrites whatever precedes it.
The dead case is `cell_dead`. -/
theorem cell_sarrange (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    (hvs : VisStrict D C.replayContext) {E : Set D.Event}
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E) {pi : List D.Event}
    (hpi : listPermOf pi E) (hev : ∀ a ∈ pi, a ∈ C.events) (x : Nat) :
    cell (((sarrange pi).map Op.op).foldl supd ((∅ : Finset Nat), fun _ => none)) x
      = (decide (x ∈ elements (D.applyList D.sigma0 pi)),
         priority (D.applyList D.sigma0 pi) x) := by
  have hnd : pi.Nodup := hpi.1
  have hdist : ∀ a ∈ pi, ∀ b ∈ pi, a ≠ b → a.time ≠ b.time := fun a ha b hb hne =>
    time_ne (C := C.replayContext)
      (by rw [Configuration.replayContext_events]; exact hev a ha)
      (by rw [Configuration.replayContext_events]; exact hev b hb) hne
  have hperm := sarrange_perm pi
  have hndA : (sarrange pi).Nodup := hperm.nodup_iff.mpr hnd
  rw [cell_fold_filter, filter_map_op]
  set Lx := (sarrange pi).filter (fun e => decide (elemOf e = x)) with hLx
  have hndLx : Lx.Nodup := hndA.filter _
  have hsub : ∀ a ∈ Lx, a ∈ pi := fun a ha =>
    hperm.subset (List.mem_filter.mp ha).1
  have helem : ∀ a ∈ Lx, elemOf a = x := fun a ha => by
    simpa using (List.mem_filter.mp ha).2
  have hsorted := sarrange_filter_sorted pi x
  rw [← hLx] at hsorted
  obtain ⟨L0, L1, L2, hsplit, h0, h1, h2⟩ :=
    split_three (srank pi) (srank_le_two pi) Lx
      (hsorted.imp (fun {_ _} h => h.elim Nat.le_of_lt (fun h => Nat.le_of_eq h.1)))
  have hmemLx : ∀ a, a ∈ L0 ∨ a ∈ L1 ∨ a ∈ L2 → a ∈ Lx := by
    intro a ha; rw [hsplit]; simp only [List.mem_append]; tauto
  have hsplitOps : (Lx.map Op.op)
      = (L0.map Op.op ++ L1.map Op.op) ++ L2.map Op.op := by
    rw [hsplit]; simp
  rw [hsplitOps, List.foldl_append, List.foldl_append]
  rcases hw : winner pi x with _ | w
  · -- no surviving insertion
    have hdead : ∀ a ∈ Lx, winner pi (elemOf a) = none := fun a ha => by
      rw [helem a ha]; exact hw
    have hzero : ∀ a ∈ Lx, srank pi a = 0 := fun a ha =>
      srank_eq_zero_of_dead (hdead a ha)
    have hL1 : L1 = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr (fun a ha => ?_)
      have := hzero a (hmemLx a (Or.inr (Or.inl ha)))
      have := h1 a ha
      omega
    have hL2 : L2 = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr (fun a ha => ?_)
      have := hzero a (hmemLx a (Or.inr (Or.inr ha)))
      have := h2 a ha
      omega
    have hnotmem : x ∉ elements (D.applyList D.sigma0 pi) :=
      (winner_none_iff pi x).mp hw
    have hpri : priority (D.applyList D.sigma0 pi) x = none := by
      simp only [priority, winner] at hw ⊢; rw [hw]; rfl
    have hLx0 : Lx = L0 := by rw [hsplit, hL1, hL2]; simp
    have hsortL0 : L0.Pairwise (fun a b => a.time ≤ b.time) := by
      refine ((hLx0 ▸ hsorted).imp_of_mem ?_)
      intro a b ha hb h
      rcases h with h | h
      · rw [hzero a (hmemLx a (Or.inl ha)), hzero b (hmemLx b (Or.inl hb))] at h
        omega
      · exact h.2
    have hkill : ∀ a ∈ L0, ∀ v, a.op = .add x v →
        ∃ f ∈ L0, (∃ W, f.op = .remove x W) ∧ a.time < f.time := by
      intro a ha v hav
      have haLx : a ∈ Lx := hmemLx a (Or.inl ha)
      have hrm : ((x, a.time) : Tag) ∈ (D.applyList D.sigma0 pi).removed := by
        by_contra hr
        exact hnotmem (elements_of_add (hsub a haLx) hav hr)
      obtain ⟨f, hf, W, hfr, hfu⟩ := remove_of_removed' hrm
      have hfLx : f ∈ Lx :=
        List.mem_filter.mpr ⟨hperm.mem_iff.mpr hf, by simp [elemOf, hfr]⟩
      exact ⟨f, hLx0 ▸ hfLx, ⟨W, hfr⟩,
        removal_after_add hmint hvs hev (hsub a haLx) hf hav hfr hfu⟩
    rw [hL1, hL2, hpri]
    simp only [List.map_nil, List.foldl_nil,
      decide_eq_false_iff_not.mpr hnotmem]
    exact cell_dead L0 (fun a ha => helem a (hmemLx a (Or.inl ha))) hsortL0 hkill _
      (Or.inl rfl)
  · -- a surviving insertion
    obtain ⟨es, hesPi, hesOp, hesTime⟩ := winner_event hw
    have hesElem : elemOf es = x := by simp [elemOf, hesOp]
    have hesLx : es ∈ Lx :=
      List.mem_filter.mpr ⟨hperm.mem_iff.mpr hesPi, by simpa using hesElem⟩
    have hwElem : ∀ a ∈ Lx, winner pi (elemOf a) = some w := fun a ha => by
      rw [helem a ha]; exact hw
    have hesRank : srank pi es = 1 :=
      (srank_eq_one (hwElem es hesLx)).mpr ⟨⟨_, by rw [hesOp, hesElem]⟩, hesTime⟩
    have hesL1 : es ∈ L1 := by
      rw [hsplit] at hesLx
      simp only [List.mem_append] at hesLx
      rcases hesLx with (ha | ha) | ha
      · exact absurd (h0 es ha) (by omega)
      · exact ha
      · exact absurd (h2 es ha) (by omega)
    have hL1single : L1 = [es] := by
      refine eq_singleton_of_all_eq ?_ hesL1 ?_
      · rw [hsplit] at hndLx
        simp only [List.nodup_append] at hndLx
        tauto
      · intro a ha
        have haLx : a ∈ Lx := hmemLx a (Or.inr (Or.inl ha))
        obtain ⟨⟨v, hav⟩, hat⟩ := (srank_eq_one (hwElem a haLx)).mp (h1 a ha)
        by_contra hne
        exact hdist a (hsub a haLx) es hesPi hne (by rw [hat, hesTime])
    have hincs : ∀ o ∈ L2.map Op.op, ∃ n W, o = .inc x n W := by
      intro o ho
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
      have haLx : a ∈ Lx := hmemLx a (Or.inr (Or.inr ha))
      have hinc := (srank_eq_two (hwElem a haLx)).mp (h2 a ha)
      rcases hop : a.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
        simp only [incAt, hop, helem a haLx, decide_eq_true_eq] at hinc
      · exact absurd hinc (by simp)
      · exact ⟨n, W, by rw [hinc.1]⟩
      · exact absurd hinc (by simp)
    rw [hL1single]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [hesOp]
    rw [fold_incs_present _ hincs (cell_add _ x (ofLex w).2)]
    have hmem : x ∈ elements (D.applyList D.sigma0 pi) := by
      by_contra hc
      rw [(winner_none_iff pi x).mpr hc] at hw
      cases hw
    have hsum : (List.map (fun o => match o with | .inc _ n _ => n | _ => 0)
        (L2.map Op.op)).sum = acquired (D.applyList D.sigma0 pi) (x, (ofLex w).1) := by
      rw [acquired_eq hnd hdist]
      rw [List.map_map]
      refine List.Perm.sum_eq ?_
      refine (List.Perm.map _ ?_)
      have hL2eq : L2 = Lx.filter (fun a => decide (srank pi a = 2)) := by
        rw [hsplit]
        simp only [List.filter_append]
        rw [List.filter_eq_nil_iff.mpr (fun a ha => by simp [h0 a ha]),
          List.filter_eq_nil_iff.mpr (fun a ha => by simp [h1 a ha]),
          List.filter_eq_self.mpr (fun a ha => by simp [h2 a ha])]
        simp
      rw [hL2eq, hLx, List.filter_filter]
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
        have : srank pi a = 2 := (srank_eq_two hwa).mpr (by rw [helemA]; exact hinc)
        simp [hinc, helemA, this]
      · simp only [Bool.not_eq_true] at hinc
        by_cases helemA : elemOf a = x
        · have : srank pi a ≠ 2 := by
            intro hr
            have := (srank_eq_two (by rw [helemA]; exact hw)).mp hr
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

end Honest

/-! ## Clause 2 and the order clause at the new order -/

section Honest

variable {C : Configuration D.toMRDTSig}

theorem spec_state_sarrange (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    (hvs : VisStrict D C.replayContext) {E : Set D.Event}
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E) {pi : List D.Event}
    (hpi : listPermOf pi E) (hev : ∀ a ∈ pi, a ∈ C.events) :
    ((sarrange pi).map Op.op).foldl supd ((∅ : Finset Nat), fun _ => none)
      = (elements (D.applyList D.sigma0 pi), priority (D.applyList D.sigma0 pi)) := by
  refine Prod.ext ?_ ?_
  · ext y
    have h := congrArg Prod.fst (cell_sarrange hmint hvs hclosed hpi hev y)
    simpa [cell] using h
  · funext y
    exact congrArg Prod.snd (cell_sarrange hmint hvs hclosed hpi hev y)

/-- **The replay at the new order answers every query as the implementation
does.** -/
theorem query_sarrange (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    (hvs : VisStrict D C.replayContext) {E : Set D.Event}
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E) {pi : List D.Event}
    (hpi : listPermOf pi E) (hev : ∀ a ∈ pi, a ∈ C.events) (q : type.QType) :
    D.query (D.applyList D.sigma0 (sarrange pi)) q
      = specMachine.query
          (((sarrange pi).map Op.op).foldl specMachine.update specMachine.initial) q := by
  rw [show specMachine.initial = ((∅ : Finset Nat), fun _ => none) from rfl,
    show specMachine.update = supd from rfl,
    spec_state_sarrange hmint hvs hclosed hpi hev,
    state_perm (sarrange_perm pi)]
  cases q <;> rfl

/-- **The new order respects specification visibility.** A conflict the
specification sees names one element twice, so the two events are ranked
against each other. Inside a block the order is chronological and
`causal_mono` settles it. Across blocks the later block is the winning
addition or one of its increments, and `attached_of_vis` says nothing of
smaller rank is `vis`-after either. -/
theorem sarrange_respects_spec (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {pi : List D.Event} (hpi : listPermOf pi E) (hev : ∀ a ∈ pi, a ∈ C.events) :
    respects (sarrange pi) (specVisibility historySpec C.replayContext) := by
  refine (sarrange_sorted pi).imp_of_mem ?_
  rintro a b ha hb hcmp ⟨hvis, hnc⟩
  have hel : elemOf b = elemOf a := elemOf_eq_of_not_commutes hnc
  have htime : b.time < a.time := C.causal_mono hvis
  rcases scmp_iff.mp hcmp with hlt | ⟨-, hle⟩
  · have hpos : 0 < srank pi b := by omega
    have hwb : ∃ w, winner pi (elemOf b) = some w := by
      rcases hw : winner pi (elemOf b) with _ | w
      · exact absurd (srank_eq_zero_of_dead hw) (by omega)
      · exact ⟨w, rfl⟩
    obtain ⟨w, hw⟩ := hwb
    have hax : elemOf a = elemOf b := hel.symm
    have haPi : a ∈ pi := (sarrange_perm pi).subset ha
    have hknows : (∃ v, b.op = .add (elemOf b) v ∧ b.time = (ofLex w).1)
        ∨ (∃ n W, b.op = .inc (elemOf b) n W ∧ (ofLex w).1 ∈ W) := by
      rcases Nat.lt_or_ge (srank pi b) 2 with hb2 | hb2
      · obtain ⟨⟨v, hop⟩, ht⟩ := (srank_eq_one hw).mp (by omega)
        exact Or.inl ⟨v, hop, ht⟩
      · have hinc := (srank_eq_two hw).mp (by have := srank_le_two pi b; omega)
        rcases hop : b.op with ⟨y, v⟩ | ⟨y, n, W⟩ | ⟨y, W⟩ <;>
          simp only [incAt, hop, decide_eq_true_eq] at hinc
        · exact absurd hinc (by simp)
        · exact Or.inr ⟨n, W, by rw [hinc.1], hinc.2⟩
        · exact absurd hinc (by simp)
    have hatt := attached_of_vis hmint hclosed hpi hev hw haPi hvis hax hknows
    have h2 : srank pi a = 2 :=
      (srank_eq_two (by rw [hax]; exact hw)).mpr (by rw [hax]; exact hatt)
    have hle2 := srank_le_two pi b
    omega
  · exact absurd htime (Nat.not_lt.mpr hle)

end Honest

/-- **The sequential premise, execution-scoped, with specification
visibility.** The row chooses the chronological history of each element,
with the winning addition and its own increments moved to the end. -/
theorem specChosenOrderSound :
    Soundness.SpecChosenOrderSound D historySpec issuance := by
  rintro C hmint hvs E hsub hclosed ⟨pi, hpi⟩ q
  have hev : ∀ a ∈ pi, a ∈ C.events := fun a ha => hsub a ((hpi.2 a).mp ha)
  refine ⟨sarrange pi, ?_, ?_, ?_, ?_⟩
  · exact ⟨(sarrange_perm pi).nodup_iff.mpr hpi.1,
      fun a => ((sarrange_perm pi).mem_iff).trans (hpi.2 a)⟩
  · exact ((sarrange_perm pi).nodup_iff.mpr hpi.1).imp
      (fun {_ _} _ => Soundness.paperOrder_false rc_non_comm_uniform all_commute _ _ _ _)
  · exact sarrange_respects_spec hmint hclosed hpi hev
  · rw [show projectedUpdates (D := D.toMRDTSig) (sarrange pi)
          = DeterministicSpec.updateLabels ((sarrange pi).map Op.op) from by
        simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
          Function.comp],
      historySpec, specMachine.updates_query_iff]
    exact query_sarrange hmint hvs hclosed hpi hev q

end LeanProofs.NoSpecNonComm.Implementations.PriorityQueue
