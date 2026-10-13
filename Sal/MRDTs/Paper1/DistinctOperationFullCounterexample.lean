import Sal.MRDTs.Paper1.DistinctOperationFullModel

/-! The representation selects maximum-timestamp states. Its peel always
chooses the largest event, so all five raw merge equations hold even though
the concrete overwrite updates do not commute on equal application payloads.
This file supplies every algebraic and representation premise of the scoped
VC route; the execution and independent history language live separately. -/

namespace Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
open Foundation ConcreteMRDT

theorem unique : Raw.Unique R := by
  intro C E s t hs ht
  rcases hs.2.2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases ht.2.2 with ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ <;>
    simp_all [Set.ext_iff, a,b] <;> grind

theorem bounds {C E s} (h : R C E s) : ∀ e ∈ E, e.time ≤ s := by
  rcases h.2.2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [a,b,Op.time]

theorem least {C E s k} (h : R C E s) (bound : ∀ e ∈ E, e.time ≤ k) : s ≤ k := by
  rcases h.2.2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · omega
  · exact bound a (by simp)
  · exact bound b (by simp)
  · exact bound b (by simp)

def scheme (C : ReplayContext D.toUpdateSig) := MetadataDependencies.ofConcrete C

theorem vcs : Raw.MergeVCs P R scheme where
  merge_comm := by intros; exact Nat.max_comm _ _
  init := by intros; exact Nat.zero_max _
  causal_delta := by
    intro C U s B e _ _ _ _ _ _ _ pre _ _ post
    change max s e.time = e.time
    exact Nat.max_eq_right (least pre (fun x hx => bounds post x hx.1))
  local_redistribute := by
    intros
    change max (max _ _) _ = max (max _ _) _
    simp only [max_assoc, max_left_comm, max_comm]
  shared := by
    intros
    change max (max _ _) (max _ _) = max (max _ _) _
    simp only [max_assoc, max_left_comm, max_comm, max_self]

theorem initial : ∀ C E s, R C E s → R C ∅ D.init := by
  intro C E s h
  exact ⟨h.1,by simp [Supported],Or.inl ⟨rfl,rfl⟩⟩

theorem finite : ∀ C E s, R C E s → ∃ π, listPermOf π E := by
  intro C E s h
  rcases h.2.2 with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
  · exact ⟨[], by simp [listPermOf]⟩
  · exact ⟨[a], by simp [listPermOf]⟩
  · exact ⟨[b], by simp [listPermOf]⟩
  · exact ⟨[a,b], by simp [listPermOf,a,b]⟩

theorem supported : ∀ C E s, R C E s → Supported C E := fun _ _ _ h => h.2.1

theorem empty_order {C} (good : Good C) (E) (x y : Op Unit) :
    ¬ paperOrder P C E x y := by
  simp [paperOrder,P,good.1 x y]

theorem canonical : ∀ C E s, R C E s → Canonical P C E s := by
  intro C E s h
  have ordered : ∀ π, respects π (paperOrder P C E) := fun _ =>
    List.pairwise_of_forall (fun x y => empty_order h.1 E y x)
  rcases h.2.2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨[],by simp [listPermOf],ordered [],rfl⟩
  · exact ⟨[a],by simp [listPermOf],ordered [a],rfl⟩
  · exact ⟨[b],by simp [listPermOf],ordered [b],rfl⟩
  · exact ⟨[a,b],by simp [listPermOf,a,b],ordered [a,b],rfl⟩

theorem shapes {E : Set (Op Unit)} (sub : ∀ x ∈ E, x=a ∨ x=b) :
    E=∅ ∨ E={a} ∨ E={b} ∨ E={a,b} := by
  classical
  by_cases ha : a ∈ E <;> by_cases hb : b ∈ E
  · right; right; right; ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    exact ⟨sub x,fun h => h.elim (fun e => e ▸ ha) (fun e => e ▸ hb)⟩
  · right; left; ext x; simp only [Set.mem_singleton_iff]
    constructor
    · intro hx; exact (sub x hx).resolve_right (fun eq => hb (eq ▸ hx))
    · intro eq; exact eq ▸ ha
  · right; right; left; ext x; simp only [Set.mem_singleton_iff]
    constructor
    · intro hx; exact (sub x hx).resolve_left (fun eq => ha (eq ▸ hx))
    · intro eq; exact eq ▸ hb
  · left; ext x; simp only [Set.mem_empty_iff_false,iff_false]
    intro hx; rcases sub x hx with rfl | rfl
    · exact ha hx
    · exact hb hx

theorem represented {C E} (good : Good C) (sup : Supported C E) : ∃ s, R C E s := by
  rcases shapes (fun x hx => good.2 x (sup x hx)) with rfl | rfl | rfl | rfl
  · exact ⟨0,good,sup,Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨1,good,sup,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  · exact ⟨2,good,sup,Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))⟩
  · exact ⟨2,good,sup,Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))⟩

theorem past {C} (good : Good C) (e : Op Unit) : (scheme C).Past e = {e} := by
  ext x
  simp only [MetadataDependencies.Past,Set.mem_setOf_eq,Set.mem_singleton_iff]
  constructor
  · rintro (eq | path)
    · exact eq
    · have no : ∀ x y, ¬ (scheme C).before x y := fun x y h => good.1 x y h.1
      induction path with
      | single edge => exact False.elim (no _ _ edge)
      | tail _ edge _ => exact False.elim (no _ _ edge)
  · exact Or.inl

theorem peel {C E s} (h : R C E s) (nonempty : E.Nonempty) :
    Nonempty (Raw.PeelChoice P R C (scheme C) E) := by
  have good := h.1
  have sup := h.2.1
  have semantic : ∀ e x, ¬ paperOrder P C E e x := empty_order good E
  have metadata : ∀ e x, ¬ (scheme C).before e x := fun e x edge => good.1 e x edge.1
  rcases h.2.2 with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
  · simp at nonempty
  · refine ⟨{
      event := a
      member := by simp
      semantic_maximal := fun x _ _ => semantic a x
      metadata_maximal := fun x _ _ => metadata a x
      remainder := 0
      past := 0
      remainder_rep := ?_
      past_rep := ?_
      reconstructed_past := ?_
      reconstructed_union := ?_}⟩
    all_goals simp only [past good,Set.diff_self]
    all_goals simp [R,good,Supported,D,a,b,Op.time] at sup ⊢
    all_goals exact sup
  · refine ⟨{
      event := b
      member := by simp
      semantic_maximal := fun x _ _ => semantic b x
      metadata_maximal := fun x _ _ => metadata b x
      remainder := 0
      past := 0
      remainder_rep := ?_
      past_rep := ?_
      reconstructed_past := ?_
      reconstructed_union := ?_}⟩
    all_goals simp only [past good,Set.diff_self]
    all_goals simp [R,good,Supported,D,a,b,Op.time] at sup ⊢
    all_goals exact sup
  · refine ⟨{
      event := b
      member := by simp
      semantic_maximal := fun x _ _ => semantic b x
      metadata_maximal := fun x _ _ => metadata b x
      remainder := 1
      past := 0
      remainder_rep := ?_
      past_rep := ?_
      reconstructed_past := ?_
      reconstructed_union := ?_}⟩
    all_goals simp only [past good,Set.diff_self]
    all_goals simp [R,good,Supported,D,a,b,Op.time,Set.ext_iff] at sup ⊢
    all_goals grind

theorem replaySupply : ∀ C E₁ E₂ s t, Transitive C.vis → (∀ x, ¬ C.vis x x) →
    Supported C E₁ → Supported C E₂ → R C E₁ s → R C E₂ t →
    Raw.ReplaySupply P R scheme C := by
  intro C E₁ E₂ s t _ _ _ _ h _
  exact ⟨fun E _ _ sup => represented h.1 sup,
    fun _ _ rep _ nonempty _ => peel rep nonempty⟩

#print axioms vcs
#print axioms replaySupply
#print axioms canonical
end Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
