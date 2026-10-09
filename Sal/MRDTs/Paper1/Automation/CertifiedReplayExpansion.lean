import Sal.MRDTs.Paper1.ConcreteJoin

namespace Sal.MRDTs.Paper1.Automation.CertifiedReplay
open Sal.MRDTs.Foundation

theorem provenance {E S R : Type} (step : S → E → S) (init : S)
    (mem : R → S → Prop) (born : E → R → Prop)
    (empty : ∀ p, ¬mem p init)
    (one : ∀ s e p, mem p (step s e) → born e p ∨ mem p s)
    (xs : List E) : ∀ p, mem p (xs.foldl step init) → ∃ e ∈ xs, born e p := by
  induction xs using List.reverseRecOn with
  | nil => intro p hp; exact False.elim (empty p hp)
  | append_singleton xs e ih =>
    intro p hp
    rw [List.foldl_append] at hp
    rcases one _ e p hp with h | h
    · exact ⟨e,by simp,h⟩
    · obtain ⟨q,hq,hb⟩ := ih p h
      exact ⟨q,List.mem_append_left _ hq,hb⟩

/-- New generic fold expansion; the only order premise excludes a killer
before a later birth of the same record. -/
theorem alive {E S R : Type} (step : S → E → S) (init : S)
    (mem : R → S → Prop) (born kill : E → R → Prop)
    (empty : ∀ p, ¬mem p init) (xs : List E)
    (one : ∀ pre e post, xs = pre ++ e :: post → ∀ p,
      mem p (step (pre.foldl step init) e) ↔ born e p ∨ (mem p (pre.foldl step init) ∧ ¬kill e p))
    (same : ∀ e p, born e p → ¬kill e p)
    (before : ∀ pre d mid e post, xs = pre ++ d :: (mid ++ e :: post) → ∀ p,
      kill d p → ¬born e p) :
    ∀ p, mem p (xs.foldl step init) ↔
      (∃ e ∈ xs, born e p) ∧ ∀ d ∈ xs, ¬kill d p := by
  induction xs using List.reverseRecOn with
  | nil => intro p; simp [empty]
  | append_singleton xs e ih =>
    have prefixOne : ∀ pre q post, xs = pre ++ q :: post → ∀ p,
        mem p (step (pre.foldl step init) q) ↔ born q p ∨ (mem p (pre.foldl step init) ∧ ¬kill q p) := by
      intro pre q post eq
      apply one pre q (post ++ [e])
      simp [eq,List.append_assoc]
    have prefixBefore : ∀ pre d mid q post, xs = pre ++ d :: (mid ++ q :: post) → ∀ p,
        kill d p → ¬born q p := by
      intro pre d mid q post eq
      apply before pre d mid q (post ++ [e])
      simp [eq,List.append_assoc]
    intro p
    rw [List.foldl_append]
    change mem p (step (xs.foldl step init) e) ↔ _
    rw [one xs e [] (by simp), ih prefixOne prefixBefore p]
    have newSafe : born e p → ∀ d ∈ xs, ¬kill d p := by
      intro hb d hd hk
      obtain ⟨pre,post,eq⟩ := List.mem_iff_append.mp hd
      exact before pre d post e [] (by simp [eq,List.append_assoc]) p hk hb
    simp only [List.mem_append,List.mem_singleton]
    constructor
    · rintro (hb | ⟨⟨birth,nokill⟩,he⟩)
      · exact ⟨⟨e,Or.inr rfl,hb⟩,fun d hd => hd.elim (newSafe hb d) (fun h => h ▸ same e p hb)⟩
      · exact ⟨by obtain ⟨q,hq,hb⟩ := birth; exact ⟨q,Or.inl hq,hb⟩,
          fun d hd => hd.elim (nokill d) (fun h => h ▸ he)⟩
    · rintro ⟨⟨q,hq,hb⟩,nk⟩
      rcases hq with hq | rfl
      · exact Or.inr ⟨⟨⟨q,hq,hb⟩,fun d hd => nk d (Or.inl hd)⟩,nk e (Or.inr rfl)⟩
      · exact Or.inl hb
end Sal.MRDTs.Paper1.Automation.CertifiedReplay
