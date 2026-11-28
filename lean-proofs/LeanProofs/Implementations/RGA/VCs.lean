import LeanProofs_no_spec_non_comm.Implementations.RGA.Definition
import LeanProofs_no_spec_non_comm.Interface.VCRoute
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything up to the last section is
`Implementations/RGA/VCs.lean` with the namespace changed. The last section
is what this folder adds: the chosen history respects **specification
visibility** as well, with no appeal to SPEC-NON-COMM, which this row
refutes.

# RGA: `Laws(D_type)` and VC1 to VC5

Both components of the state are grow-only, and `do` sets one bit in one of
them. So every pair of events commutes, `rc` is empty, and `Laws(D_type)` is
immediate. The five conditions are Boolean algebra: `merge` is a pointwise
`or` of three states, and each VC is an identity among disjunctions.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.RGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

theorem do_eq (s : St) (e : D.Event) : D.do_ s e = step s e := rfl

/-! ## Every pair of events commutes -/

theorem sigma0_eq : D.sigma0 = ((fun _ => false), (fun _ => false)) := rfl

theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro s
  simp only [do_eq]
  rcases h₁ : e₁.op with ⟨i₁, a₁⟩ | x₁ <;> rcases h₂ : e₂.op with ⟨i₂, a₂⟩ | x₂ <;>
    simp only [step, h₁, h₂] <;>
    refine Prod.ext (funext fun p => ?_) (funext fun y => ?_) <;>
    simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

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

/-! ## VC1 to VC5

`merge l a b` is `l ∨ a ∨ b` in each component, so every condition is an
identity among disjunctions, and `do m e` contributes one further disjunct. -/

theorem merge_eq (l a b : D.Sigma) : D.merge l a b = mergeState l a b := rfl

theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  simp only [merge_eq, mergeState]
  exact Prod.ext (funext fun p => by
      simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm])
    (funext fun x => by simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm])

theorem vc2_merge_init :
    ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s → D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  simp only [merge_eq, mergeState, sigma0_eq]
  exact Prod.ext (funext fun p => by simp) (funext fun x => by simp)

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
  rcases hop : e.op with ⟨i, a⟩ | t <;>
    simp only [merge_eq, mergeState, do_eq, step, hop] <;>
    refine Prod.ext (funext fun p => ?_) (funext fun z => ?_) <;>
    simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

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
  rcases hop : e.op with ⟨i, a⟩ | t <;>
    simp only [merge_eq, mergeState, do_eq, step, sigma0_eq, hop] <;>
    refine Prod.ext (funext fun p => ?_) (funext fun z => ?_) <;>
    simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

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
  rcases hop : e.op with ⟨i, a⟩ | t <;>
    simp only [merge_eq, mergeState, do_eq, step, hop] <;>
    refine Prod.ext (funext fun p => ?_) (funext fun z => ?_) <;>
    simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

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

/-! ## What a replay leaves in each component

Both components are grow-only, so a replay's state is read off the list
directly: an edge is present exactly when some insertion of the list made
it, and an identity is tombstoned exactly when some deletion named it. -/

/-- `e` is an insertion. -/
def isInsert (e : D.Event) : Bool :=
  match e.op with
  | .addAfter _ _ => true
  | .remove _ => false

/-- The edge an insertion contributes. -/
def edgeOf (e : D.Event) : Entry :=
  match e.op with
  | .addAfter i a => (i, a)
  | .remove _ => (0, 0)

/-- The identity an insertion allocates, as a key to sort on. -/
def keyOf (e : D.Event) : Nat := (edgeOf e).1

/-- The identity a deletion names. -/
def target (e : D.Event) : Nat :=
  match e.op with
  | .remove x => x
  | .addAfter _ _ => 0

theorem isInsert_add {e : D.Event} {i a : Nat} (h : e.op = .addAfter i a) :
    isInsert e = true := by simp [isInsert, h]

theorem edgeOf_add {e : D.Event} {i a : Nat} (h : e.op = .addAfter i a) :
    edgeOf e = (i, a) := by simp [edgeOf, h]

theorem isInsert_rem {e : D.Event} {x : Nat} (h : e.op = .remove x) :
    isInsert e = false := by simp [isInsert, h]

theorem fst_applyList (pi : List D.Event) (p : Entry) :
    (D.applyList D.sigma0 pi).1 p = true
      ↔ ∃ e ∈ pi, isInsert e = true ∧ edgeOf e = p := by
  have gen : ∀ (s : D.Sigma) (pi : List D.Event) (p : Entry),
      (D.applyList s pi).1 p = true
        ↔ s.1 p = true ∨ ∃ e ∈ pi, isInsert e = true ∧ edgeOf e = p := by
    intro s pi
    induction pi generalizing s with
    | nil => intro p; simp [Impl.applyList]
    | cons e rest ih =>
        intro p
        show (D.applyList (D.do_ s e) rest).1 p = true ↔ _
        rw [ih]
        rcases hop : e.op with ⟨i, a⟩ | x
        · simp only [do_eq, step, hop, Bool.or_eq_true, decide_eq_true_eq,
            List.mem_cons]
          constructor
          · rintro ((h | rfl) | ⟨f, hf, hi, he⟩)
            · exact Or.inl h
            · exact Or.inr ⟨e, Or.inl rfl, isInsert_add hop, edgeOf_add hop⟩
            · exact Or.inr ⟨f, Or.inr hf, hi, he⟩
          · rintro (h | ⟨f, hf | hf, hi, he⟩)
            · exact Or.inl (Or.inl h)
            · subst hf
              rw [edgeOf_add hop] at he
              exact Or.inl (Or.inr he.symm)
            · exact Or.inr ⟨f, hf, hi, he⟩
        · simp only [do_eq, step, hop, List.mem_cons]
          constructor
          · rintro (h | ⟨f, hf, hi, he⟩)
            · exact Or.inl h
            · exact Or.inr ⟨f, Or.inr hf, hi, he⟩
          · rintro (h | ⟨f, hf | hf, hi, he⟩)
            · exact Or.inl h
            · subst hf
              rw [isInsert_rem hop] at hi
              exact absurd hi (by simp)
            · exact Or.inr ⟨f, hf, hi, he⟩
  rw [gen]
  simp [Impl.sigma0, D]

theorem snd_applyList (pi : List D.Event) (x : Nat) :
    (D.applyList D.sigma0 pi).2 x = true ↔ ∃ e ∈ pi, e.op = .remove x := by
  have gen : ∀ (s : D.Sigma) (pi : List D.Event) (x : Nat),
      (D.applyList s pi).2 x = true
        ↔ s.2 x = true ∨ ∃ e ∈ pi, e.op = .remove x := by
    intro s pi
    induction pi generalizing s with
    | nil => intro x; simp [Impl.applyList]
    | cons e rest ih =>
        intro x
        show (D.applyList (D.do_ s e) rest).2 x = true ↔ _
        rw [ih]
        rcases hop : e.op with ⟨i, a⟩ | y
        · simp only [do_eq, step, hop, List.mem_cons]
          constructor
          · rintro (h | ⟨f, hf, he⟩)
            · exact Or.inl h
            · exact Or.inr ⟨f, Or.inr hf, he⟩
          · rintro (h | ⟨f, hf | hf, he⟩)
            · exact Or.inl h
            · subst hf; rw [hop] at he; exact absurd he (by simp)
            · exact Or.inr ⟨f, hf, he⟩
        · simp only [do_eq, step, hop, Bool.or_eq_true, decide_eq_true_eq,
            List.mem_cons]
          constructor
          · rintro ((h | rfl) | ⟨f, hf, he⟩)
            · exact Or.inl h
            · exact Or.inr ⟨e, Or.inl rfl, hop⟩
            · exact Or.inr ⟨f, Or.inr hf, he⟩
          · rintro (h | ⟨f, hf | hf, he⟩)
            · exact Or.inl (Or.inl h)
            · subst hf; rw [hop] at he
              exact Or.inl (Or.inr (by injection he with h; exact h.symm))
            · exact Or.inr ⟨f, hf, he⟩
  rw [gen]
  simp [Impl.sigma0, D]

/-! ## The replay this row chooses

`lo^C_E` has no edges, because every pair of events commutes and `rc` is
empty, so clause 1 accepts any enumeration of `E`. The one that explains the
query puts the insertions first, in increasing identity order, and the
deletions after them. That is exactly the order the implementation's own
query folds them in. -/

theorem rc_non_comm_uniform : UniformRcNonComm D := by
  intro e₁ e₂
  constructor
  · exact fun h => absurd (all_commute e₁ e₂) h
  · rintro (h | h) <;> exact absurd h (no_rc_edge _ _)

/-- Order two events by the identity an insertion allocates. -/
def leKey (a b : D.Event) : Bool := decide (keyOf a ≤ keyOf b)

/-- The insertions of a list, in increasing identity order. -/
def sortedInserts (pi : List D.Event) : List D.Event :=
  (pi.filter isInsert).mergeSort leKey

/-- Insertions in increasing identity order, then deletions. -/
def arrange (pi : List D.Event) : List D.Event :=
  sortedInserts pi ++ pi.filter (fun e => !isInsert e)

theorem sortedInserts_perm (pi : List D.Event) :
    (sortedInserts pi).Perm (pi.filter isInsert) :=
  List.mergeSort_perm _ _

theorem arrange_perm (pi : List D.Event) : (arrange pi).Perm pi :=
  ((sortedInserts_perm pi).append_right _).trans (List.filter_append_perm isInsert pi)

/-- The insertion prefix is sorted on the identity. -/
theorem sortedInserts_sorted (pi : List D.Event) :
    (sortedInserts pi).Pairwise (fun a b => keyOf a ≤ keyOf b) := by
  have := List.pairwise_mergeSort (le := leKey)
    (by intro a b c hab hbc; simp only [leKey, decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [leKey, Bool.or_eq_true, decide_eq_true_eq]; omega)
    (pi.filter isInsert)
  exact this.imp (by intro a b h; simpa only [leKey, decide_eq_true_eq] using h)

/-! ## Running the specification

The machine admits an insertion only when its anchor is the root or is live.
While no deletion has run, the live list holds exactly the identities
allocated so far, and that invariant is what carries the anchor condition
along. -/

/-- With a live anchor, `insertAfter` really inserts. -/
theorem mem_insertAfter {a i : Nat} : ∀ {B : List Nat}, (a = 0 ∨ a ∈ B) →
    ∀ x, (x ∈ insertAfter a i B ↔ x = i ∨ x ∈ B)
  | [], h, x => by
      rcases h with rfl | h
      · simp [insertAfter]
      · exact absurd h (by simp)
  | y :: tail, h, x => by
      by_cases ha : a = 0
      · subst ha; simp [insertAfter]
      · by_cases hy : y = a
        · simp [insertAfter, ha, hy]
          tauto
        · have htail : a = 0 ∨ a ∈ tail := by
            rcases h with rfl | h
            · exact absurd rfl ha
            · rcases List.mem_cons.mp h with rfl | h
              · exact absurd rfl (fun hh => hy hh.symm)
              · exact Or.inr h
          simp only [insertAfter, if_neg ha, if_neg hy, List.mem_cons,
            mem_insertAfter htail x]
          tauto

/-- One step of the specification's insertion fold. -/
def insStep (p : SpecState) (e : D.Event) : SpecState :=
  (insertAfter (edgeOf e).2 (keyOf e) p.1, insert (keyOf e) p.2)

/-- One step of the specification's deletion fold. -/
def remStep (p : SpecState) (e : D.Event) : SpecState :=
  (p.1.filter (fun y => y ≠ target e), p.2)

/-- The insertions of `es` are admitted from `(B, I)`. -/
inductive OkInserts : List Nat → Finset Nat → List D.Event → Prop
  | nil {B I} : OkInserts B I []
  | cons {B I e es} :
      isInsert e = true → 0 < keyOf e → keyOf e ∉ I →
      ((edgeOf e).2 = 0 ∨ (edgeOf e).2 ∈ B) →
      OkInserts (insStep (B, I) e).1 (insStep (B, I) e).2 es →
      OkInserts B I (e :: es)

theorem run_inserts {B : List Nat} {I : Finset Nat} {es : List D.Event}
    (h : OkInserts B I es) :
    Runs specMachine.transition (B, I)
      (projectedUpdates (D := D.toMRDTSig) es) (es.foldl insStep (B, I)) := by
  induction h with
  | nil => exact Runs.nil _
  | @cons B I e es hins hpos hfresh hanchor _ ih =>
      refine Runs.cons (l := .update e.op) ?_ ih
      rcases hop : e.op with ⟨i, a⟩ | x
      · have hk : keyOf e = i := by simp [keyOf, edgeOf_add hop]
        have ha : (edgeOf e).2 = a := by simp [edgeOf_add hop]
        refine ⟨by rw [← hk]; exact hpos, by rw [← hk]; exact hfresh, ?_, ?_⟩
        · rw [← ha]; exact hanchor
        · simp [insStep, hk, ha]
      · exact absurd hins (by rw [isInsert_rem hop]; simp)

theorem run_removes {es : List D.Event} (h : ∀ e ∈ es, isInsert e = false)
    (st : SpecState) :
    Runs specMachine.transition st
      (projectedUpdates (D := D.toMRDTSig) es) (es.foldl remStep st) := by
  induction es generalizing st with
  | nil => exact Runs.nil _
  | cons e rest ih =>
      refine Runs.cons (l := .update e.op) ?_ (ih (fun f hf => h f (by simp [hf])) _)
      rcases hop : e.op with ⟨i, a⟩ | x
      · exact absurd (h e (by simp)) (by rw [isInsert_add hop]; simp)
      · show _ = _
        simp only [remStep, target, hop]

/-! ## The arranged insertions are admitted

Sorting on the identity is what makes the anchor condition hold at every
step. An anchor is always smaller than the identity it anchors, so in
increasing order the anchor's own insertion has already run, and while no
deletion has happened the live list holds every identity allocated so far. -/

theorem okInserts_of_sorted : ∀ (es : List D.Event) (B : List Nat) (I : Finset Nat),
    (∀ x, x ∈ B ↔ x ∈ I) →
    (∀ e ∈ es, keyOf e ∉ I) →
    es.Pairwise (fun a b => keyOf a ≤ keyOf b) →
    (es.map keyOf).Nodup →
    (∀ e ∈ es, isInsert e = true) →
    (∀ e ∈ es, 0 < keyOf e) →
    (∀ e ∈ es, (edgeOf e).2 = 0 ∨ (edgeOf e).2 ∈ I ∨
      ∃ f ∈ es, keyOf f = (edgeOf e).2 ∧ (edgeOf e).2 < keyOf e) →
    OkInserts B I es
  | [], _, _, _, _, _, _, _, _, _ => OkInserts.nil
  | e :: rest, B, I, hinv, hfresh, hsort, hnd, hins, hpos, hanch => by
      have hsortE : ∀ f ∈ rest, keyOf e ≤ keyOf f :=
        (List.pairwise_cons.mp hsort).1
      have hndrest : (rest.map keyOf).Nodup ∧ keyOf e ∉ rest.map keyOf := by
        rw [List.map_cons, List.nodup_cons] at hnd
        exact ⟨hnd.2, hnd.1⟩
      have hndE : keyOf e ∉ rest.map keyOf := hndrest.2
      -- the head's anchor is already allocated
      have hhead : (edgeOf e).2 = 0 ∨ (edgeOf e).2 ∈ B := by
        rcases hanch e (by simp) with h | h | ⟨f, hf, hkf, hlt⟩
        · exact Or.inl h
        · exact Or.inr ((hinv _).mpr h)
        · exfalso
          rcases List.mem_cons.mp hf with rfl | hf
          · omega
          · have := hsortE f hf
            omega
      refine OkInserts.cons (hins e (by simp)) (hpos e (by simp))
        (hfresh e (by simp)) hhead ?_
      refine okInserts_of_sorted rest _ _ ?_ ?_
        (List.pairwise_cons.mp hsort).2 hndrest.1 (fun f hf => hins f (by simp [hf]))
        (fun f hf => hpos f (by simp [hf])) ?_
      · intro x
        simp only [insStep, Finset.mem_insert, mem_insertAfter hhead x, hinv x]
      · intro f hf
        simp only [insStep, Finset.mem_insert, not_or]
        refine ⟨fun hk => ?_, hfresh f (by simp [hf])⟩
        exact hndE (List.mem_map.mpr ⟨f, hf, hk⟩)
      · intro f hf
        rcases hanch f (by simp [hf]) with h | h | ⟨g, hg, hkg, hlt⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl (by simp only [insStep, Finset.mem_insert]; exact Or.inr h))
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact Or.inr (Or.inl (by
              simp only [insStep, Finset.mem_insert]; exact Or.inl hkg.symm))
          · exact Or.inr (Or.inr ⟨g, hg, hkg, hlt⟩)

/-! ## The query agrees with the specification's list

`read` sorts the edge support on the identity, folds it with `insertAfter`,
and drops the tombstoned identities. The specification's run does the same
three things, in the same order, because `arrange` hands it the insertions
already sorted. -/

theorem supportFinset_eq {α : Type} [DecidableEq α] {f : α → Bool} {S : Finset α}
    (h : ∀ x, f x = true ↔ x ∈ S) : supportFinset f = S := by
  classical
  have hset : {x | f x = true} = (↑S : Set α) := by ext x; simpa using h x
  have hfin : Set.Finite {x | f x = true} := hset ▸ S.finite_toSet
  simp only [supportFinset, dif_pos hfin]
  ext x
  rw [Set.Finite.mem_toFinset]
  simpa using h x

/-- The deletions of a list. -/
def deletes (pi : List D.Event) : List D.Event := pi.filter (fun e => !isInsert e)

theorem mem_edges (pi : List D.Event) (p : Entry) :
    (D.applyList D.sigma0 pi).1 p = true
      ↔ p ∈ (pi.filter isInsert).map edgeOf := by
  rw [fst_applyList]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨e, he, hi, hp⟩; exact ⟨e, ⟨he, hi⟩, hp⟩
  · rintro ⟨e, ⟨he, hi⟩, hp⟩; exact ⟨e, he, hi, hp⟩

theorem mem_graves (pi : List D.Event) (x : Nat) :
    (D.applyList D.sigma0 pi).2 x = true ↔ x ∈ (deletes pi).map target := by
  rw [snd_applyList]
  simp only [deletes, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨e, he, hop⟩
    exact ⟨e, ⟨he, by rw [isInsert_rem hop]; simp⟩, by simp [target, hop]⟩
  · rintro ⟨e, ⟨he, hi⟩, hx⟩
    rcases hop : e.op with ⟨i, a⟩ | y
    · rw [isInsert_add hop] at hi; exact absurd hi (by simp)
    · refine ⟨e, he, ?_⟩
      rw [hop]
      have : target e = y := by simp [target, hop]
      rw [this] at hx; rw [hx]

theorem support_edges (pi : List D.Event) :
    supportFinset (D.applyList D.sigma0 pi).1
      = ((pi.filter isInsert).map edgeOf).toFinset :=
  supportFinset_eq (fun p => by rw [mem_edges]; simp)

theorem support_graves (pi : List D.Event) :
    supportFinset (D.applyList D.sigma0 pi).2 = ((deletes pi).map target).toFinset :=
  supportFinset_eq (fun x => by rw [mem_graves]; simp)

/-- Distinct identities make the edge list repetition-free. -/
theorem edges_nodup {pi : List D.Event}
    (hkeys : ((pi.filter isInsert).map keyOf).Nodup) :
    ((pi.filter isInsert).map edgeOf).Nodup := by
  have : ((pi.filter isInsert).map edgeOf).map Prod.fst
      = (pi.filter isInsert).map keyOf := by
    simp [List.map_map, Function.comp, keyOf]
  exact List.Nodup.of_map Prod.fst (this ▸ hkeys)

/-- Two edges of one list with the same identity are the same edge. -/
theorem edge_inj {pi : List D.Event}
    (hkeys : ((pi.filter isInsert).map keyOf).Nodup)
    {a b : Entry} (ha : a ∈ (pi.filter isInsert).map edgeOf)
    (hb : b ∈ (pi.filter isInsert).map edgeOf) (h : a.1 = b.1) : a = b := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
  have hinj := (List.nodup_map_iff_inj_on (hkeys.of_map keyOf)).mp hkeys
  exact congrArg edgeOf (hinj e he f hf h)

/-- **The query's sort is the arrangement's own order.** Both lists hold the
same edges, both are sorted on the identity, and distinct insertions carry
distinct identities, so they are the same list. -/
theorem sorted_support_eq (pi : List D.Event) (es : List D.Event)
    (hes : ((pi.filter isInsert)).Perm es)
    (hsorted : es.Pairwise (fun a b => keyOf a ≤ keyOf b))
    (hkeys : ((pi.filter isInsert).map keyOf).Nodup) :
    (supportFinset (D.applyList D.sigma0 pi).1).toList.mergeSort leEntry
      = es.map edgeOf := by
  have hLnd := edges_nodup hkeys
  have h1 : (supportFinset (D.applyList D.sigma0 pi).1).toList.Perm
      ((pi.filter isInsert).map edgeOf) := by
    rw [support_edges]; exact List.toFinset_toList hLnd
  have hsortL : ((supportFinset (D.applyList D.sigma0 pi).1).toList.mergeSort
      leEntry).Pairwise (fun a b => a.1 ≤ b.1) := by
    have := List.pairwise_mergeSort (le := leEntry)
      (by intro a b c hab hbc; simp only [leEntry, decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [leEntry, Bool.or_eq_true, decide_eq_true_eq]; omega)
      (supportFinset (D.applyList D.sigma0 pi).1).toList
    exact this.imp (by intro a b h; simpa only [leEntry, decide_eq_true_eq] using h)
  have hsortR : (es.map edgeOf).Pairwise (fun a b => a.1 ≤ b.1) :=
    List.pairwise_map.mpr (hsorted.imp (fun {a b} h => h))
  have hperm : ((supportFinset (D.applyList D.sigma0 pi).1).toList.mergeSort
      leEntry).Perm (es.map edgeOf) :=
    ((List.mergeSort_perm _ _).trans h1).trans (hes.map edgeOf)
  refine List.Perm.eq_of_pairwise ?_ hsortL hsortR hperm
  intro a b ha hb hab hba
  refine edge_inj hkeys ?_ ?_ (Nat.le_antisymm hab hba)
  · exact h1.subset ((List.mergeSort_perm _ _).subset ha)
  · exact (hes.map edgeOf).symm.subset hb

/-! ## The two folds -/

theorem insert_fold_eq : ∀ (es : List D.Event) (B : List Nat) (I : Finset Nat),
    (es.foldl insStep (B, I)).1
      = (es.map edgeOf).foldl (fun xs p => insertAfter p.2 p.1 xs) B
  | [], _, _ => rfl
  | e :: rest, B, I => by
      show (rest.foldl insStep (insStep (B, I) e)).1 = _
      rw [show insStep (B, I) e
            = (insertAfter (edgeOf e).2 (keyOf e) B, insert (keyOf e) I) from rfl,
        insert_fold_eq rest _ _]
      simp [keyOf]

theorem remove_fold_eq : ∀ (es : List D.Event) (B : List Nat) (I : Finset Nat),
    (es.foldl remStep (B, I)).1 = B.filter (fun y => decide (y ∉ es.map target))
  | [], B, _ => by simp
  | e :: rest, B, I => by
      show (rest.foldl remStep (remStep (B, I) e)).1 = _
      rw [show remStep (B, I) e = (B.filter (fun y => y ≠ target e), I) from rfl,
        remove_fold_eq rest _ _, List.filter_filter]
      refine List.filter_congr (fun y _ => ?_)
      by_cases h1 : y = target e <;> by_cases h2 : y ∈ rest.map target <;>
        simp [h1, h2]

/-- The insertion prefix of the arrangement is exactly the sorted
insertions, and its deletion suffix exactly the deletions. -/
theorem filter_arrange (pi : List D.Event) :
    (arrange pi).filter isInsert = sortedInserts pi := by
  have h1 : (sortedInserts pi).filter isInsert = sortedInserts pi := by
    refine List.filter_eq_self.mpr (fun e he => ?_)
    exact List.mem_filter.mp ((sortedInserts_perm pi).subset he) |>.2
  have h2 : (pi.filter (fun e => !isInsert e)).filter isInsert = [] := by
    refine List.filter_eq_nil_iff.mpr (fun e he => ?_)
    have := (List.mem_filter.mp he).2
    simpa using this
  simp [arrange, List.filter_append, h1, h2]

theorem deletes_arrange (pi : List D.Event) : deletes (arrange pi) = deletes pi := by
  show (arrange pi).filter (fun e => !isInsert e) = deletes pi
  have h1 : (sortedInserts pi).filter (fun e => !isInsert e) = [] := by
    refine List.filter_eq_nil_iff.mpr (fun e he => ?_)
    have := List.mem_filter.mp ((sortedInserts_perm pi).subset he) |>.2
    simp [this]
  have h2 : (pi.filter (fun e => !isInsert e)).filter (fun e => !isInsert e)
      = pi.filter (fun e => !isInsert e) := by
    refine List.filter_eq_self.mpr (fun e he => (List.mem_filter.mp he).2)
  simp [arrange, deletes, List.filter_append, h1, h2]

/-! ## What honest issuance gives

`MintHonest` replays each event's causal past and checks `G` there. Three
facts fall out, and they are exactly the three the arrangement needs: an
insertion's identity is its timestamp, so identities are distinct; it is
positive; and its anchor is the root or an identity inserted earlier, by an
event the issuer had already observed. -/

/-- Distinct observed events carry distinct timestamps. -/
theorem time_ne {C : Ctx D} {a b : D.Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hne : a ≠ b) : a.time ≠ b.time := by
  obtain ⟨p, t, hL, ht⟩ := ha
  obtain ⟨p', t', hL', ht'⟩ := hb
  exact C.timestamps_distinct hL ht hL' ht' hne

theorem exists_add {e : D.Event} (h : isInsert e = true) :
    ∃ i a, e.op = .addAfter i a := by
  rcases hop : e.op with ⟨i, a⟩ | t
  · exact ⟨i, a, rfl⟩
  · rw [isInsert_rem hop] at h; exact absurd h (by simp)

variable {C : Configuration D.toMRDTSig}

theorem issued_insert (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {e : D.Event} (he : e ∈ C.events) {i a : Nat} (hop : e.op = .addAfter i a) :
    i = e.time ∧ 0 < i
      ∧ (a = 0 ∨ ∃ f, C.vis f e ∧ f ∈ C.events ∧ isInsert f = true ∧ keyOf f = a) := by
  obtain ⟨pi, hpi, -, hg⟩ := hmint e he
  rw [show issuance.CanIssue e (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init pi)
        = issuance.CanIssue e (D.applyList D.sigma0 pi) from rfl] at hg
  simp only [issuance, hop] at hg
  obtain ⟨hid, hanchor, -, -⟩ := hg
  refine ⟨hid, ?_, ?_⟩
  · rcases hanchor with ⟨-, hpos⟩ | ⟨-, hlt, -⟩
    · exact hpos
    · omega
  · rcases hanchor with ⟨ha, -⟩ | ⟨-, -, b, hb⟩
    · exact Or.inl ha
    · refine Or.inr ?_
      obtain ⟨f, hf, hins, hedge⟩ := (fst_applyList pi (a, b)).mp hb
      have hmem := (hpi.2 f).mp hf
      exact ⟨f, hmem.2, hmem.1, hins, by rw [keyOf, hedge]⟩

/-- Honest insertions carry their own timestamp, so distinct events of a
context carry distinct identities. -/
theorem keys_nodup (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {pi : List D.Event} (hnd : pi.Nodup) (hsub : ∀ e ∈ pi, e ∈ C.events) :
    ((pi.filter isInsert).map keyOf).Nodup := by
  refine List.Nodup.map_on ?_ (hnd.filter _)
  intro x hx y hy hk
  have hxm := List.mem_filter.mp hx
  have hym := List.mem_filter.mp hy
  obtain ⟨i, a, hopx⟩ := exists_add hxm.2
  obtain ⟨j, b, hopy⟩ := exists_add hym.2
  have hkx : keyOf x = i := by simp [keyOf, edgeOf_add hopx]
  have hky : keyOf y = j := by simp [keyOf, edgeOf_add hopy]
  have hx' := (issued_insert hmint (hsub x hxm.1) hopx).1
  have hy' := (issued_insert hmint (hsub y hym.1) hopy).1
  have htime : x.time = y.time := by rw [← hx', ← hy', ← hkx, ← hky, hk]
  by_contra hne
  exact time_ne (C := C.replayContext)
    (by rw [Configuration.replayContext_events]; exact hsub x hxm.1)
    (by rw [Configuration.replayContext_events]; exact hsub y hym.1) hne htime

/-! ## Clause 2

The arranged history is admitted, and its final list is the one the
implementation's query computes. -/

/-- The anchor condition the arrangement needs, from honest issuance and
causal closure of `E`. -/
theorem anchors_present (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} {pi : List D.Event} (hpi : listPermOf pi E)
    (hsub : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.replayContext.vis a b → b ∈ E → a ∈ E)
    (e : D.Event) (he : e ∈ pi.filter isInsert) :
    (edgeOf e).2 = 0 ∨ ∃ f ∈ pi.filter isInsert, keyOf f = (edgeOf e).2
      ∧ (edgeOf e).2 < keyOf e := by
  have hem := List.mem_filter.mp he
  obtain ⟨i, a, hop⟩ := exists_add hem.2
  have hkey : keyOf e = i := by simp [keyOf, edgeOf_add hop]
  have hanc : (edgeOf e).2 = a := by simp [edgeOf_add hop]
  have heE : e ∈ E := (hpi.2 e).mp hem.1
  obtain ⟨hid, -, hrest⟩ := issued_insert hmint (hsub e heE) hop
  rcases hrest with ha | ⟨f, hvis, hfC, hfins, hfkey⟩
  · exact Or.inl (by rw [hanc, ha])
  · refine Or.inr ⟨f, ?_, by rw [hanc, hfkey], ?_⟩
    · exact List.mem_filter.mpr ⟨(hpi.2 f).mpr (hclosed f e hvis heE), hfins⟩
    · -- the anchor is smaller than the identity it anchors
      obtain ⟨pi', hpi', -, hg⟩ := hmint e (hsub e heE)
      rw [show issuance.CanIssue e
            (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init pi')
          = issuance.CanIssue e (D.applyList D.sigma0 pi') from rfl] at hg
      simp only [issuance, hop] at hg
      have hlt : a < i := by
        rcases hg.2.1 with ⟨ha0, hpos⟩ | ⟨-, hlt, -⟩
        · subst ha0; exact hpos
        · exact hlt
      rw [hanc, hkey]; exact hlt

theorem chosenOrderSound : Soundness.ChosenOrderSound D historySpec issuance := by
  rintro C hmint E hsub hclosed ⟨pi, hpi⟩ q
  have hkeys := keys_nodup hmint hpi.1 (fun e he => hsub e ((hpi.2 e).mp he))
  have hkeysS : ((sortedInserts pi).map keyOf).Nodup :=
    ((sortedInserts_perm pi).map keyOf).nodup_iff.mpr hkeys
  -- the arrangement
  refine ⟨arrange pi, ?_, ?_, ?_⟩
  · exact ⟨(arrange_perm pi).nodup_iff.mpr hpi.1,
      fun a => ((arrange_perm pi).mem_iff).trans (hpi.2 a)⟩
  · exact ((arrange_perm pi).nodup_iff.mpr hpi.1).imp
      (fun {_ _} _ => Soundness.paperOrder_false rc_non_comm_uniform all_commute _ _ _ _)
  · -- the run
    have hok : OkInserts [] ∅ (sortedInserts pi) := by
      refine okInserts_of_sorted _ [] ∅ (by simp) (by simp)
        (sortedInserts_sorted pi) hkeysS
        (fun e he => (List.mem_filter.mp ((sortedInserts_perm pi).subset he)).2)
        (fun e he => ?_) (fun e he => ?_)
      · obtain ⟨i, a, hop⟩ :=
          exists_add (List.mem_filter.mp ((sortedInserts_perm pi).subset he)).2
        have hmem := List.mem_filter.mp ((sortedInserts_perm pi).subset he)
        have := (issued_insert hmint (hsub e ((hpi.2 e).mp hmem.1)) hop).2.1
        simpa [keyOf, edgeOf_add hop] using this
      · rcases anchors_present hmint hpi hsub hclosed e
            ((sortedInserts_perm pi).subset he) with h | ⟨f, hf, hkf, hlt⟩
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨f, (sortedInserts_perm pi).mem_iff.mpr hf, hkf, hlt⟩)
    have hrunI := run_inserts hok
    have hrunR := run_removes (es := deletes pi)
      (fun e he => by simpa using (List.mem_filter.mp he).2)
      ((sortedInserts pi).foldl insStep ([], ∅))
    set mid : SpecState :=
      (deletes pi).foldl remStep ((sortedInserts pi).foldl insStep ([], ∅)) with hmid
    refine ⟨mid, Runs.append (m := mid) ?_ ?_⟩
    · rw [show projectedUpdates (D := D.toMRDTSig) (arrange pi)
            = projectedUpdates (D := D.toMRDTSig) (sortedInserts pi)
              ++ projectedUpdates (D := D.toMRDTSig) (deletes pi) from by
          simp [arrange, projectedUpdates, deletes, List.map_append]]
      exact Runs.append hrunI hrunR
    · refine Runs.cons (l := SeqLabel.query q _) (m := mid) ⟨rfl, ?_⟩ (Runs.nil mid)
      -- the answer
      show D.query (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init (arrange pi)) q = _
      have hq : D.query (D.applyList D.sigma0 (arrange pi)) q
          = read (D.applyList D.sigma0 (arrange pi)) := rfl
      rw [show applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init (arrange pi)
            = D.applyList D.sigma0 (arrange pi) from rfl, hq]
      rw [hmid, remove_fold_eq, insert_fold_eq]
      show (((supportFinset (D.applyList D.sigma0 (arrange pi)).1).toList.mergeSort
          leEntry).foldl (fun xs e => insertAfter e.2 e.1 xs) []).filter
          (fun i => decide (i ∉ supportFinset (D.applyList D.sigma0 (arrange pi)).2)) = _
      rw [sorted_support_eq (arrange pi) (sortedInserts pi)
          (by rw [filter_arrange]) (sortedInserts_sorted pi)
          (by rw [filter_arrange]; exact hkeysS),
        support_graves, deletes_arrange]
      refine List.filter_congr (fun y _ => ?_)
      simp

/-! ## SPEC-NON-COMM fails here

`all_commute` says every pair of events commutes in the implementation, so
SPEC-NON-COMM collapses to the demand that every pair of specification
updates commute. Two insertions after the root do not: taking them in one
order reads `[2, 1]`, in the other `[1, 2]`.

Nothing downstream consumes SPEC-NON-COMM, so the certificate is unaffected.
What the failure costs is the stronger criterion of
`Artifact/MRDTs/Paper1/SpecificationVisibility.lean`, which this row cannot
reach, and it is why the row needs `Soundness.ChosenOrderSound` rather than
`Soundness.AnyOrderSound`. -/

/-- Two root insertions do not commute in `Spec`: the order decides which
ends up first in the list. -/
theorem not_spec_commutes :
    ¬ historySpec.Commutes (AppOp.addAfter 1 0) (AppOp.addAfter 2 0) := by
  intro hc
  have hyes : historySpec.admits
      ([] ++ [SeqLabel.update (AppOp.addAfter 1 0),
              SeqLabel.update (AppOp.addAfter 2 0)]
        ++ [SeqLabel.query () [2, 1]]) := by
    refine ⟨([2, 1], {1, 2}), ?_⟩
    refine Runs.cons (m := ([1], {1})) ⟨by norm_num, by decide, Or.inl rfl, rfl⟩
      (Runs.cons (m := ([2, 1], {1, 2}))
        ⟨by norm_num, by decide, Or.inl rfl, by decide⟩
        (Runs.cons ⟨rfl, rfl⟩ (Runs.nil _)))
  obtain ⟨final, run⟩ := (hc [] [SeqLabel.query () [2, 1]]).mp hyes
  cases run with
  | cons h1 r1 => cases r1 with
    | cons h2 r2 => cases r2 with
      | cons h3 _ =>
          obtain ⟨-, -, -, e1⟩ := h1
          subst e1
          obtain ⟨-, -, -, e2⟩ := h2
          subst e2
          exact absurd h3.2 (by decide)

/-- **SPEC-NON-COMM is false for this row.** Every pair of its events
commutes, so the law would force every pair of specification updates to
commute too, and `not_spec_commutes` says they do not. -/
theorem not_spec_non_comm : ¬ Interface.spec_non_comm D historySpec := fun h =>
  h (1, 0, AppOp.addAfter 1 0) (2, 1, AppOp.addAfter 2 0)
    not_spec_commutes (all_commute _ _)

/-! # Specification visibility, without SPEC-NON-COMM

SPEC-NON-COMM fails here, so `certifiedSpecRA` is closed to this row. The
route taken instead has to work, because `arrange` is **not** chronological:
it puts every deletion after every insertion. What saves it is that the
arrows it inverts are arrows the specification does not see.

Three cases, and the third is the only one with content.

* Two insertions. `arrange` sorts them by the identity they allocate, and
  issuance makes that identity the event's own timestamp, so this part is
  chronological after all and inverts nothing.
* Two deletions. They always commute in `Spec`, each being an unconditional
  filter, so nothing here is a specification-visibility arrow.
* An insertion before a deletion it observed. This does invert a `vis`
  arrow. It is not a specification conflict, because the issuer saw the
  deletion, so its anchor is not the deleted identity, and its own identity
  is fresh. Deleting something other than the anchor and the new value
  commutes with the insertion.
-/

/-! ## Two commutations in `Spec` -/

/-- Anchoring at the root prepends. -/
theorem insertAfter_zero (i : Nat) : ∀ B : List Nat, insertAfter 0 i B = i :: B
  | [] => rfl
  | _ :: _ => rfl

/-- Deleting an identity that is neither the anchor nor the inserted value
commutes with the insertion, on the nose. -/
theorem filter_insertAfter {a i y : Nat} (hyi : y ≠ i) (hya : y ≠ a) :
    ∀ B : List Nat, (insertAfter a i B).filter (fun z => z ≠ y)
      = insertAfter a i (B.filter (fun z => z ≠ y)) := by
  have hiy : ¬ i = y := fun h => hyi h.symm
  intro B
  simp only [ne_eq, decide_not]
  induction B with
  | nil => by_cases ha : a = 0 <;> simp [insertAfter, ha, hiy]
  | cons x tail ih =>
    by_cases ha : a = 0
    · subst ha; simp [insertAfter_zero, hiy]
    · by_cases hx : x = a
      · subst hx
        have hxy : ¬ x = y := fun h => hya h.symm
        simp [insertAfter, ha, hiy, hxy]
      · by_cases hxy : x = y
        · subst hxy; simp [insertAfter, ha, hx, ih]
        · simp [insertAfter, ha, hx, hxy, ih]

/-- **Two deletions commute in `Spec`.** Each is an unconditional filter,
and filters commute. -/
theorem spec_commutes_remove_remove (x y : Nat) :
    historySpec.Commutes (AppOp.remove x) (AppOp.remove y) := by
  refine specMachine.commutes_of_diamond _ _ (fun s t => ?_)
  simp only [NoSpecNonComm.Soundness.runs_pair]
  constructor <;>
  · rintro ⟨m, h1, h2⟩
    simp only [specMachine] at h1 h2
    subst h1
    refine ⟨_, rfl, ?_⟩
    simp only [specMachine]
    rw [h2]
    simp [List.filter_filter, Bool.and_comm]

/-- **A deletion commutes in `Spec` with an insertion that neither anchors
at the deleted identity nor allocates it.** -/
theorem spec_commutes_remove_add {i a y : Nat} (hyi : y ≠ i) (hya : y ≠ a) :
    historySpec.Commutes (AppOp.remove y) (AppOp.addAfter i a) := by
  refine specMachine.commutes_of_diamond _ _ (fun s t => ?_)
  simp only [NoSpecNonComm.Soundness.runs_pair]
  constructor
  · rintro ⟨m, h1, h2⟩
    simp only [specMachine] at h1 h2
    subst h1
    obtain ⟨hpos, hfresh, hanch, ht⟩ := h2
    refine ⟨(insertAfter a i s.1, insert i s.2), ⟨hpos, hfresh, ?_, rfl⟩, ?_⟩
    · exact hanch.imp id List.mem_of_mem_filter
    · simp only [specMachine]
      rw [ht]
      exact Prod.ext (filter_insertAfter hyi hya s.1).symm rfl
  · rintro ⟨m, h1, h2⟩
    simp only [specMachine] at h1 h2
    obtain ⟨hpos, hfresh, hanch, hm⟩ := h1
    subst hm
    refine ⟨(s.1.filter (fun z => z ≠ y), s.2), rfl, ⟨hpos, hfresh, ?_, ?_⟩⟩
    · refine hanch.imp id (fun h => List.mem_filter.mpr ⟨h, ?_⟩)
      simpa using fun hc => hya hc.symm
    · rw [h2]
      exact Prod.ext (filter_insertAfter hyi hya s.1) rfl

/-! ## What issuance rules out -/

/-- A non-insertion is a deletion. -/
theorem exists_rem {e : D.Event} (h : isInsert e = false) :
    ∃ y, e.op = .remove y := by
  rcases hop : e.op with ⟨i, a⟩ | y
  · rw [isInsert_add hop] at h; exact absurd h (by simp)
  · exact ⟨y, rfl⟩

/-- An honest deletion names an identity some insertion allocated, and
insertions allocate positive identities, so the root is never deleted. -/
theorem issued_remove (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {f : D.Event} (hf : f ∈ C.events) {y : Nat} (hop : f.op = .remove y) :
    0 < y := by
  obtain ⟨pi, hpi, -, hg⟩ := hmint f hf
  rw [show issuance.CanIssue f (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init pi)
        = issuance.CanIssue f (D.applyList D.sigma0 pi) from rfl] at hg
  simp only [issuance, hop] at hg
  obtain ⟨⟨b, hb⟩, -⟩ := hg
  obtain ⟨g, hgpi, hgins, hedge⟩ := (fst_applyList pi (y, b)).mp hb
  obtain ⟨j, c, hgop⟩ := exists_add hgins
  have hkey : j = y := by rw [edgeOf, hgop] at hedge; exact congrArg Prod.fst hedge
  have := (issued_insert hmint ((hpi.2 g).mp hgpi).1 hgop).2.1
  omega

/-- **An insertion anchors away from what its issuer has seen deleted, and
its own identity is fresh.** This is the fact that makes the deletions-last
arrangement admissible against specification visibility. -/
theorem insert_avoids_removed (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {e : D.Event} (he : e ∈ C.events) {i a : Nat} (hop : e.op = .addAfter i a)
    {f : D.Event} (hf : f ∈ C.events) (hvis : C.vis f e) {y : Nat}
    (hfop : f.op = .remove y) : y ≠ a ∧ y ≠ i := by
  obtain ⟨pi, hpi, -, hg⟩ := hmint e he
  rw [show issuance.CanIssue e (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init pi)
        = issuance.CanIssue e (D.applyList D.sigma0 pi) from rfl] at hg
  simp only [issuance, hop] at hg
  obtain ⟨-, hanch, -, hfresh⟩ := hg
  have hfpi : f ∈ pi := (hpi.2 f).mpr ⟨hf, hvis⟩
  have hrem : (D.applyList D.sigma0 pi).2 y = true :=
    (snd_applyList pi y).mpr ⟨f, hfpi, hfop⟩
  constructor
  · rintro rfl
    rcases hanch with ⟨ha, -⟩ | ⟨hna, -, -⟩
    · have hpos := issued_remove hmint hf hfop
      omega
    · rw [hna] at hrem; exact absurd hrem (by simp)
  · rintro rfl; rw [hfresh] at hrem; exact absurd hrem (by simp)

/-! ## The clause -/

/-- **The chosen history respects specification visibility.** The three
cases of the header, in order. -/
theorem arrange_respects_specVisibility
    (hmint : MintHonest D.toMRDTSig issuance.CanIssue C)
    {E : Set D.Event} {pi : List D.Event} (hpi : listPermOf pi E)
    (hsub : ∀ e ∈ E, e ∈ C.events) :
    respects (arrange pi) (specVisibility historySpec C.replayContext) := by
  have hev : ∀ e ∈ pi, e ∈ C.events := fun e he => hsub e ((hpi.2 e).mp he)
  rw [arrange, respects, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · refine (sortedInserts_sorted pi).imp_of_mem ?_
    rintro a b ha hb hab ⟨hvis, -⟩
    obtain ⟨-, hains⟩ := List.mem_filter.mp ((sortedInserts_perm pi).subset ha)
    obtain ⟨-, hbins⟩ := List.mem_filter.mp ((sortedInserts_perm pi).subset hb)
    obtain ⟨i, x, hopa⟩ := exists_add hains
    obtain ⟨j, y, hopb⟩ := exists_add hbins
    have hta := (issued_insert hmint
      (hev a (List.mem_filter.mp ((sortedInserts_perm pi).subset ha)).1) hopa).1
    have htb := (issued_insert hmint
      (hev b (List.mem_filter.mp ((sortedInserts_perm pi).subset hb)).1) hopb).1
    have hka : keyOf a = a.time := by rw [keyOf, edgeOf_add hopa]; exact hta
    have hkb : keyOf b = b.time := by rw [keyOf, edgeOf_add hopb]; exact htb
    rw [hka, hkb] at hab
    exact absurd (C.causal_mono hvis) (Nat.not_lt.mpr hab)
  · refine List.pairwise_iff_forall_sublist.mpr ?_
    intro a b hsl
    rintro ⟨-, hnc⟩
    have ha : a ∈ deletes pi := hsl.subset (by simp)
    have hb : b ∈ deletes pi := hsl.subset (by simp)
    obtain ⟨x, hopa⟩ := exists_rem (by simpa using (List.mem_filter.mp ha).2)
    obtain ⟨y, hopb⟩ := exists_rem (by simpa using (List.mem_filter.mp hb).2)
    rw [hopa, hopb] at hnc
    exact hnc (spec_commutes_remove_remove y x)
  · rintro a ha b hb ⟨hvis, hnc⟩
    obtain ⟨-, hains⟩ := List.mem_filter.mp ((sortedInserts_perm pi).subset ha)
    obtain ⟨i, x, hopa⟩ := exists_add hains
    obtain ⟨y, hopb⟩ := exists_rem (by simpa using (List.mem_filter.mp hb).2)
    obtain ⟨hyx, hyi⟩ := insert_avoids_removed hmint
      (hev a (List.mem_filter.mp ((sortedInserts_perm pi).subset ha)).1) hopa
      (hev b (List.mem_filter.mp hb).1) hvis hopb
    rw [hopa, hopb] at hnc
    exact hnc (spec_commutes_remove_add hyi hyx)

/-- **The scoped premise with specification visibility.** The same witness
as `chosenOrderSound`, with the extra clause. -/
theorem specChosenOrderSound :
    NoSpecNonComm.Soundness.SpecChosenOrderSound D historySpec issuance := by
  rintro C hmint _ E hsub hclosed ⟨pi, hpi⟩ q
  have hkeys := keys_nodup hmint hpi.1 (fun e he => hsub e ((hpi.2 e).mp he))
  have hkeysS : ((sortedInserts pi).map keyOf).Nodup :=
    ((sortedInserts_perm pi).map keyOf).nodup_iff.mpr hkeys
  -- the arrangement
  refine ⟨arrange pi, ?_, ?_, ?_, ?_⟩
  · exact ⟨(arrange_perm pi).nodup_iff.mpr hpi.1,
      fun a => ((arrange_perm pi).mem_iff).trans (hpi.2 a)⟩
  · exact ((arrange_perm pi).nodup_iff.mpr hpi.1).imp
      (fun {_ _} _ => Soundness.paperOrder_false rc_non_comm_uniform all_commute _ _ _ _)
  · exact arrange_respects_specVisibility hmint hpi hsub
  · -- the run
    have hok : OkInserts [] ∅ (sortedInserts pi) := by
      refine okInserts_of_sorted _ [] ∅ (by simp) (by simp)
        (sortedInserts_sorted pi) hkeysS
        (fun e he => (List.mem_filter.mp ((sortedInserts_perm pi).subset he)).2)
        (fun e he => ?_) (fun e he => ?_)
      · obtain ⟨i, a, hop⟩ :=
          exists_add (List.mem_filter.mp ((sortedInserts_perm pi).subset he)).2
        have hmem := List.mem_filter.mp ((sortedInserts_perm pi).subset he)
        have := (issued_insert hmint (hsub e ((hpi.2 e).mp hmem.1)) hop).2.1
        simpa [keyOf, edgeOf_add hop] using this
      · rcases anchors_present hmint hpi hsub hclosed e
            ((sortedInserts_perm pi).subset he) with h | ⟨f, hf, hkf, hlt⟩
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨f, (sortedInserts_perm pi).mem_iff.mpr hf, hkf, hlt⟩)
    have hrunI := run_inserts hok
    have hrunR := run_removes (es := deletes pi)
      (fun e he => by simpa using (List.mem_filter.mp he).2)
      ((sortedInserts pi).foldl insStep ([], ∅))
    set mid : SpecState :=
      (deletes pi).foldl remStep ((sortedInserts pi).foldl insStep ([], ∅)) with hmid
    refine ⟨mid, Runs.append (m := mid) ?_ ?_⟩
    · rw [show projectedUpdates (D := D.toMRDTSig) (arrange pi)
            = projectedUpdates (D := D.toMRDTSig) (sortedInserts pi)
              ++ projectedUpdates (D := D.toMRDTSig) (deletes pi) from by
          simp [arrange, projectedUpdates, deletes, List.map_append]]
      exact Runs.append hrunI hrunR
    · refine Runs.cons (l := SeqLabel.query q _) (m := mid) ⟨rfl, ?_⟩ (Runs.nil mid)
      -- the answer
      show D.query (applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init (arrange pi)) q = _
      have hq : D.query (D.applyList D.sigma0 (arrange pi)) q
          = read (D.applyList D.sigma0 (arrange pi)) := rfl
      rw [show applySeq D.toMRDTSig.toUpdateSig D.toMRDTSig.init (arrange pi)
            = D.applyList D.sigma0 (arrange pi) from rfl, hq]
      rw [hmid, remove_fold_eq, insert_fold_eq]
      show (((supportFinset (D.applyList D.sigma0 (arrange pi)).1).toList.mergeSort
          leEntry).foldl (fun xs e => insertAfter e.2 e.1 xs) []).filter
          (fun i => decide (i ∉ supportFinset (D.applyList D.sigma0 (arrange pi)).2)) = _
      rw [sorted_support_eq (arrange pi) (sortedInserts pi)
          (by rw [filter_arrange]) (sortedInserts_sorted pi)
          (by rw [filter_arrange]; exact hkeysS),
        support_graves, deletes_arrange]
      refine List.filter_congr (fun y _ => ?_)
      simp

end LeanProofs.NoSpecNonComm.Implementations.RGA