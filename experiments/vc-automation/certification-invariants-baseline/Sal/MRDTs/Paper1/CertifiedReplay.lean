import Sal.MRDTs.Paper1.GuardedReplay

/-! Scoped replay algebra. Eligibility is a fixed certified event set;
representation tracks the events already replayed. Causal readiness is an
additional admissibility condition, not a change to the semantic paper order.
The only exchange axiom is a two-update diamond on represented prefix states.
-/
namespace Sal.MRDTs.Paper1.CertifiedReplay
open Foundation Classical
variable {D : UpdateSig}

structure Scope (D : UpdateSig) where
  context : ReplayContext D
  events : Set (Op D.AppOp)
  represented : Set (Op D.AppOp) → D.State → Prop

def Ready (S : Scope D) (H : Set (Op D.AppOp)) (e : Op D.AppOp) : Prop :=
  e ∈ S.events ∧ e ∉ H ∧ ∀ p ∈ S.events, S.context.vis p e → p ∈ H

inductive Legal (S : Scope D) : Set (Op D.AppOp) → List (Op D.AppOp) → Prop
  | nil (H) : Legal S H []
  | cons {H e π} : Ready S H e → Legal S (insert e H) π → Legal S H (e :: π)

structure Laws (S : Scope D) (P : OperationPolicy D.AppOp) : Prop where
  update_closed : ∀ H s e, S.represented H s → Ready S H e →
    S.represented (insert e H) (D.update s e)
  diamond : ∀ H s a b, S.represented H s → Ready S H a → Ready S H b →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    ¬ paperOrder P S.context S.events a b → ¬ paperOrder P S.context S.events b a →
    D.update (D.update s a) b = D.update (D.update s b) a

def Order (S : Scope D) (P : OperationPolicy D.AppOp) (a b : Op D.AppOp) : Prop :=
  S.context.vis a b ∨ paperOrder P S.context S.events a b

private theorem ready_insert {S : Scope D} {H : Set (Op D.AppOp)} {a b}
    (h : Ready S H a) (ne : a ≠ b) : Ready S (insert b H) a := by
  refine ⟨h.1, ?_, fun p hp hv => Or.inr (h.2.2 p hp hv)⟩
  simpa only [Set.mem_insert_iff, not_or] using And.intro ne h.2.1

private theorem legal_append {S : Scope D} {H : Set (Op D.AppOp)} {π τ}
    (h : Legal S H (π ++ τ)) : Legal S H π := by
  induction π generalizing H with
  | nil => exact .nil _
  | cons e π ih => cases h with | cons hr ht => exact .cons hr (ih ht)

private theorem legal_cons_iff {S : Scope D} {H : Set (Op D.AppOp)} {e π} :
    Legal S H (e :: π) ↔ Ready S H e ∧ Legal S (insert e H) π := by
  constructor
  · intro h; cases h with | cons hr ht => exact ⟨hr,ht⟩
  · rintro ⟨hr,ht⟩; exact .cons hr ht

/-- One admissible adjacent exchange preserves eligibility of the entire suffix. -/
theorem legal_swap {S : Scope D} {H : Set (Op D.AppOp)} {a b π}
    (ha : Ready S H a) (hb : Ready S H b) (ne : a ≠ b)
    (h : Legal S H (a :: b :: π)) : Legal S H (b :: a :: π) := by
  rcases legal_cons_iff.mp h with ⟨_,ht⟩
  rcases legal_cons_iff.mp ht with ⟨_,ht⟩
  refine .cons hb (.cons (ready_insert ha ne) ?_)
  simpa only [Set.insert_comm] using ht

/-- A visibility-respecting enumeration is legal from the empty prefix.
Readiness is proved from enumeration completeness, rather than assumed for
each operation by a port. -/
theorem legal_of_causal_enumeration {S : Scope D} {π : List (Op D.AppOp)}
    (irrefl : ∀ e, ¬ S.context.vis e e) (hp : listPermOf π S.events)
    (hc : respects π S.context.vis) : Legal S ∅ π := by
  suffices gen : ∀ (xs : List (Op D.AppOp)) (H : Set (Op D.AppOp)), xs.Nodup →
      (∀ e, e ∈ S.events ↔ e ∈ H ∨ e ∈ xs) →
      (∀ e ∈ xs, e ∉ H) → respects xs S.context.vis → Legal S H xs by
    apply gen π ∅ hp.1
    · intro e; simpa using (hp.2 e).symm
    · intro e _ h; exact h.elim
    · exact hc
  intro xs
  induction xs with
  | nil => intro H _ _ _ _; exact .nil H
  | cons e xs ih =>
    intro H nd cover disjoint order
    rcases List.nodup_cons.mp nd with ⟨absent,nd⟩
    rcases List.pairwise_cons.mp order with ⟨minimal,order⟩
    have ready : Ready S H e := by
      refine ⟨(cover e).mpr (Or.inr List.mem_cons_self),disjoint e List.mem_cons_self,?_⟩
      intro p hp vis
      rcases (cover p).mp hp with h | h
      · exact h
      · rcases List.mem_cons.mp h with rfl | h
        · exact False.elim (irrefl p vis)
        · exact False.elim (minimal p h vis)
    apply Legal.cons ready
    apply ih (insert e H) nd
    · intro p
      rw [cover p]
      simp only [Set.mem_insert_iff,List.mem_cons]
      tauto
    · intro p hp mem
      rcases mem with rfl | mem
      · exact absent hp
      · exact disjoint p (List.mem_cons_of_mem _ hp) mem
    · exact order

/-- Every legal replay preserves its represented-prefix evidence. -/
theorem represented_fold {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S P) {H : Set (Op D.AppOp)} {s : D.State} {π}
    (hs : S.represented H s) (legal : Legal S H π) :
    S.represented (H ∪ {e | e ∈ π}) (applySeq D s π) := by
  induction legal generalizing s with
  | nil H => simpa [applySeq] using hs
  | @cons H e π ready legal ih =>
    have h := ih (laws.update_closed H s e hs ready)
    have sets : insert e H ∪ {x | x ∈ π} = H ∪ {x | x ∈ e :: π} := by
      ext x; simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_setOf_eq,List.mem_cons]; tauto
    simpa only [sets,applySeq,List.foldl_cons] using h

private theorem bubble {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S P) {H : Set (Op D.AppOp)} {s : D.State}
    (e : Op D.AppOp) (σ τ : List (Op D.AppOp))
    (hs : S.represented H s) (he : Ready S H e)
    (legal : Legal S H (σ ++ e :: τ)) (absent : e ∉ σ)
    (forward : ∀ y ∈ σ, ¬ Order S P e y)
    (backward : ∀ y ∈ σ, ¬ Order S P y e) :
    Legal S H (e :: σ ++ τ) ∧
      applySeq D s (σ ++ e :: τ) = applySeq D s (e :: σ ++ τ) := by
  induction σ generalizing H s with
  | nil => exact ⟨legal,rfl⟩
  | cons y σ ih =>
    rcases legal_cons_iff.mp legal with ⟨hy,ht⟩
    have ne : e ≠ y := fun h => absent (by simp [h])
    have he' := ready_insert he ne
    have hs' := laws.update_closed H s y hs hy
    obtain ⟨hl,eq⟩ := ih hs' he' ht
      (fun h => absent (List.mem_cons_of_mem _ h))
      (fun z hz => forward z (List.mem_cons_of_mem _ hz))
      (fun z hz => backward z (List.mem_cons_of_mem _ hz))
    have hf := forward y List.mem_cons_self
    have hb := backward y List.mem_cons_self
    have swap := laws.diamond H s y e hs hy he
      (fun hv => hb (Or.inl hv)) (fun hv => hf (Or.inl hv))
      (fun hp => hb (Or.inr hp)) (fun hp => hf (Or.inr hp))
    refine ⟨legal_swap hy he ne.symm (.cons hy hl), ?_⟩
    change applySeq D (D.update s y) (σ ++ e :: τ) =
      applySeq D (D.update (D.update s e) y) (σ ++ τ)
    rw [eq]
    change applySeq D (D.update (D.update s y) e) (σ ++ τ) = _
    rw [swap]

/-- All causally admissible, paper-order-respecting enumerations converge,
using diamonds only at certified represented prefixes. -/
theorem convergence {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S P) {H : Set (Op D.AppOp)} {s : D.State}
    {π₁ π₂ : List (Op D.AppOp)}
    (hs : S.represented H s) (perm : π₁.Perm π₂) (nodup : π₁.Nodup)
    (legal₁ : Legal S H π₁) (legal₂ : Legal S H π₂)
    (order₁ : respects π₁ (Order S P)) (order₂ : respects π₂ (Order S P)) :
    applySeq D s π₁ = applySeq D s π₂ := by
  induction π₁ generalizing H s π₂ with
  | nil => have empty := List.Perm.nil_eq perm; subst π₂; rfl
  | cons e π ih =>
    have mem : e ∈ π₂ := perm.mem_iff.mp List.mem_cons_self
    obtain ⟨σ,τ,split⟩ := List.append_of_mem mem
    subst π₂
    rcases legal_cons_iff.mp legal₁ with ⟨he,hl₁⟩
    rcases List.nodup_cons.mp nodup with ⟨hne,nd⟩
    have absent : e ∉ σ := by
      have nd₂ := perm.nodup nodup
      rw [List.nodup_append] at nd₂
      exact fun h => nd₂.2.2 e h e List.mem_cons_self rfl
    have backward : ∀ y ∈ σ, ¬ Order S P y e := by
      intro y hy
      have ym : y ∈ e :: π := perm.mem_iff.mpr (List.mem_append.mpr (Or.inl hy))
      have ym' : y ∈ π := by
        rcases List.mem_cons.mp ym with eq | h
        · exact False.elim (absent (eq ▸ hy))
        · exact h
      exact (List.pairwise_cons.mp order₁).1 y ym'
    have forward : ∀ y ∈ σ, ¬ Order S P e y :=
      fun y hy => (List.pairwise_append.mp order₂).2.2 y hy e List.mem_cons_self
    obtain ⟨hl,eq⟩ := bubble laws e σ τ hs he legal₂ absent forward backward
    rw [eq]
    have tailperm : π.Perm (σ ++ τ) := by
      apply List.Perm.cons_inv
      exact perm.trans List.perm_middle
    have tailorder : respects (σ ++ τ) (Order S P) := by
      obtain ⟨hσ,hτ,hcross⟩ := List.pairwise_append.mp order₂
      refine List.pairwise_append.mpr ⟨hσ,(List.pairwise_cons.mp hτ).2,?_⟩
      exact fun a ha b hb => hcross a ha b (List.mem_cons_of_mem _ hb)
    exact ih (laws.update_closed H s e hs he) tailperm nd hl₁
      (legal_cons_iff.mp hl).2 (List.pairwise_cons.mp order₁).2 tailorder

/-- Public paper-order admissibility is retained explicitly. Causal
admissibility and mint-certified replay readiness are additional sufficient evidence. -/
theorem convergence_on {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S P) {H : Set (Op D.AppOp)} {s : D.State}
    {F : Set (Op D.AppOp)} {π₁ π₂ : List (Op D.AppOp)}
    (hs : S.represented H s) (hp₁ : listPermOf π₁ F) (hp₂ : listPermOf π₂ F)
    (hl₁ : Legal S H π₁) (hl₂ : Legal S H π₂)
    (hc₁ : respects π₁ S.context.vis) (hc₂ : respects π₂ S.context.vis)
    (ho₁ : respects π₁ (paperOrder P S.context S.events))
    (ho₂ : respects π₂ (paperOrder P S.context S.events)) :
    applySeq D s π₁ = applySeq D s π₂ := by
  apply convergence laws hs ((List.perm_ext_iff_of_nodup hp₁.1 hp₂.1).mpr (fun x =>
    (hp₁.2 x).trans (hp₂.2 x).symm)) hp₁.1 hl₁ hl₂
  · exact hc₁.and ho₁ |>.imp (fun {_ _} h => fun horder => horder.elim h.1 h.2)
  · exact hc₂.and ho₂ |>.imp (fun {_ _} h => fun horder => horder.elim h.1 h.2)

/-- Scoped canonicality retains exact concrete state equality and the original
semantic paper order. It makes the extra legal and causal evidence explicit. -/
def Canonical (S : Scope D) (P : OperationPolicy D.AppOp) (initial s : D.State) : Prop :=
  ∃ π, listPermOf π S.events ∧ Legal S ∅ π ∧ respects π S.context.vis ∧
    respects π (paperOrder P S.context S.events) ∧ applySeq D initial π = s

theorem canonical_unique {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S P) {initial a b : D.State}
    (represented : S.represented ∅ initial)
    (ha : Canonical S P initial a) (hb : Canonical S P initial b) : a = b := by
  obtain ⟨π₁,hp₁,hl₁,hc₁,ho₁,hf₁⟩ := ha
  obtain ⟨π₂,hp₂,hl₂,hc₂,ho₂,hf₂⟩ := hb
  rw [← hf₁,← hf₂]
  exact convergence_on laws represented hp₁ hp₂ hl₁ hl₂ hc₁ hc₂ ho₁ ho₂

theorem canonical_represented {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S P) {initial s : D.State}
    (represented : S.represented ∅ initial) (canonical : Canonical S P initial s) :
    S.represented S.events s := by
  obtain ⟨π,hp,hl,_,_,hf⟩ := canonical
  have h := represented_fold laws represented hl
  have events : (∅ : Set (Op D.AppOp)) ∪ {e | e ∈ π} = S.events := by
    ext e; simp only [Set.empty_union,Set.mem_setOf_eq]; exact hp.2 e
  simpa only [events,hf] using h

end Sal.MRDTs.Paper1.CertifiedReplay
