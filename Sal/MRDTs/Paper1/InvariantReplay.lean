import Sal.MRDTs.Paper1.CertifiedScopeRestriction
import Sal.MRDTs.Paper1.InvariantOrder

/-! Certified replay with an explicit invariant-indexed state domain.
Readiness uses fixed eligible events; commutation and every order edge use
the same invariant, independently of prefix readiness. -/
namespace Sal.MRDTs.Paper1.InvariantReplay
open Foundation Classical
variable {D : UpdateSig} {Inv : D.State → Prop}

abbrev Scope := CertifiedReplay.Scope
abbrev Ready := @CertifiedReplay.Ready D
abbrev Legal := @CertifiedReplay.Legal D

structure Laws (S : Scope D) (Inv : D.State → Prop) (P : OperationPolicy D.AppOp) : Prop where
  represented_valid : ∀ H s, S.represented H s → Inv s
  update_closed : ∀ H s e, S.represented H s → Ready S H e →
    S.represented (insert e H) (D.update s e)
  diamond : ∀ H s a b, S.represented H s → Ready S H a → Ready S H b →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    ¬ InvariantOrder.order Inv P S.context S.events a b → ¬ InvariantOrder.order Inv P S.context S.events b a →
    D.update (D.update s a) b = D.update (D.update s b) a

def Order (S : Scope D) (Inv : D.State → Prop) (P : OperationPolicy D.AppOp) (a b : Op D.AppOp) : Prop :=
  S.context.vis a b ∨ InvariantOrder.order Inv P S.context S.events a b

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
    apply CertifiedReplay.Legal.cons ready
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
    (laws : Laws S Inv P) {H : Set (Op D.AppOp)} {s : D.State} {π}
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
    (laws : Laws S Inv P) {H : Set (Op D.AppOp)} {s : D.State}
    (e : Op D.AppOp) (σ τ : List (Op D.AppOp))
    (hs : S.represented H s) (he : Ready S H e)
    (legal : Legal S H (σ ++ e :: τ)) (absent : e ∉ σ)
    (forward : ∀ y ∈ σ, ¬ Order S Inv P e y)
    (backward : ∀ y ∈ σ, ¬ Order S Inv P y e) :
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
    (laws : Laws S Inv P) {H : Set (Op D.AppOp)} {s : D.State}
    {π₁ π₂ : List (Op D.AppOp)}
    (hs : S.represented H s) (perm : π₁.Perm π₂) (nodup : π₁.Nodup)
    (legal₁ : Legal S H π₁) (legal₂ : Legal S H π₂)
    (order₁ : respects π₁ (Order S Inv P)) (order₂ : respects π₂ (Order S Inv P)) :
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
    have backward : ∀ y ∈ σ, ¬ Order S Inv P y e := by
      intro y hy
      have ym : y ∈ e :: π := perm.mem_iff.mpr (List.mem_append.mpr (Or.inl hy))
      have ym' : y ∈ π := by
        rcases List.mem_cons.mp ym with eq | h
        · exact False.elim (absent (eq ▸ hy))
        · exact h
      exact (List.pairwise_cons.mp order₁).1 y ym'
    have forward : ∀ y ∈ σ, ¬ Order S Inv P e y :=
      fun y hy => (List.pairwise_append.mp order₂).2.2 y hy e List.mem_cons_self
    obtain ⟨hl,eq⟩ := bubble laws e σ τ hs he legal₂ absent forward backward
    rw [eq]
    have tailperm : π.Perm (σ ++ τ) := by
      apply List.Perm.cons_inv
      exact perm.trans List.perm_middle
    have tailorder : respects (σ ++ τ) (Order S Inv P) := by
      obtain ⟨hσ,hτ,hcross⟩ := List.pairwise_append.mp order₂
      refine List.pairwise_append.mpr ⟨hσ,(List.pairwise_cons.mp hτ).2,?_⟩
      exact fun a ha b hb => hcross a ha b (List.mem_cons_of_mem _ hb)
    exact ih (laws.update_closed H s e hs he) tailperm nd hl₁
      (legal_cons_iff.mp hl).2 (List.pairwise_cons.mp order₁).2 tailorder

/-- Public paper-order admissibility is retained explicitly. Causal
admissibility and mint-certified replay readiness are additional sufficient evidence. -/
theorem convergence_on {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S Inv P) {H : Set (Op D.AppOp)} {s : D.State}
    {F : Set (Op D.AppOp)} {π₁ π₂ : List (Op D.AppOp)}
    (hs : S.represented H s) (hp₁ : listPermOf π₁ F) (hp₂ : listPermOf π₂ F)
    (hl₁ : Legal S H π₁) (hl₂ : Legal S H π₂)
    (hc₁ : respects π₁ S.context.vis) (hc₂ : respects π₂ S.context.vis)
    (ho₁ : respects π₁ (InvariantOrder.order Inv P S.context S.events))
    (ho₂ : respects π₂ (InvariantOrder.order Inv P S.context S.events)) :
    applySeq D s π₁ = applySeq D s π₂ := by
  apply convergence laws hs ((List.perm_ext_iff_of_nodup hp₁.1 hp₂.1).mpr (fun x =>
    (hp₁.2 x).trans (hp₂.2 x).symm)) hp₁.1 hl₁ hl₂
  · exact hc₁.and ho₁ |>.imp (fun {_ _} h => fun horder => horder.elim h.1 h.2)
  · exact hc₂.and ho₂ |>.imp (fun {_ _} h => fun horder => horder.elim h.1 h.2)

/-- Scoped canonicality retains exact concrete state equality and the invariant-indexed
semantic order. It makes the extra legal and causal evidence explicit. -/
def Canonical (S : Scope D) (Inv : D.State → Prop) (P : OperationPolicy D.AppOp) (initial s : D.State) : Prop :=
  ∃ π, listPermOf π S.events ∧ Legal S ∅ π ∧ respects π S.context.vis ∧
    respects π (InvariantOrder.order Inv P S.context S.events) ∧ applySeq D initial π = s

theorem canonical_unique {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S Inv P) {initial a b : D.State}
    (represented : S.represented ∅ initial)
    (ha : Canonical S Inv P initial a) (hb : Canonical S Inv P initial b) : a = b := by
  obtain ⟨π₁,hp₁,hl₁,hc₁,ho₁,hf₁⟩ := ha
  obtain ⟨π₂,hp₂,hl₂,hc₂,ho₂,hf₂⟩ := hb
  rw [← hf₁,← hf₂]
  exact convergence_on laws represented hp₁ hp₂ hl₁ hl₂ hc₁ hc₂ ho₁ ho₂

theorem canonical_represented {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S Inv P) {initial s : D.State}
    (represented : S.represented ∅ initial) (canonical : Canonical S Inv P initial s) :
    S.represented S.events s := by
  obtain ⟨π,hp,hl,_,_,hf⟩ := canonical
  have h := represented_fold laws represented hl
  have events : (∅ : Set (Op D.AppOp)) ∪ {e | e ∈ π} = S.events := by
    ext e; simp only [Set.empty_union,Set.mem_setOf_eq]; exact hp.2 e
  simpa only [events,hf] using h

/-- Final replay states remain in the same explicit state invariant. -/
theorem valid_fold {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S Inv P) {H : Set (Op D.AppOp)} {s : D.State} {π}
    (hs : S.represented H s) (legal : Legal S H π) : Inv (applySeq D s π) :=
  laws.represented_valid _ _ (represented_fold laws hs legal)

/-- Fixed-domain concurrent commutation supplies represented-prefix diamonds.
No reissuability claim is made about the reordered intermediate state. -/
def laws_of_concurrent_commutation (S : Scope D) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp)
    (valid : ∀ H s, S.represented H s → Inv s)
    (closed : ∀ H s e, S.represented H s → Ready S H e →
      S.represented (insert e H) (D.update s e))
    (commute : ∀ a b, a ∈ S.events → b ∈ S.events →
      ¬ S.context.vis a b → ¬ S.context.vis b a → InvariantOrder.Commutes D Inv a b) :
    Laws S Inv P where
  represented_valid := valid
  update_closed := closed
  diamond H s a b represented readyA readyB notab notba _ _ :=
    commute a b readyA.1 readyB.1 notab notba s (valid H s represented)

structure PolicyLaws (S : Scope D) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) : Prop where
  concurrent_exact : ∀ a b, a ∈ S.events → b ∈ S.events →
    distinctOps a b → a.rep ≠ b.rep →
    ¬ S.context.vis a b → ¬ S.context.vis b a →
    (¬ InvariantOrder.Commutes D Inv a b ↔ P.before a.op b.op ∨ P.before b.op a.op)
  no_chain : ∀ a b c, a ∈ S.events → b ∈ S.events → c ∈ S.events →
    distinctOps a b → distinctOps b c →
    ¬ (P.before a.op b.op ∧ P.before b.op c.op)

structure RestrictedLaws (S : Scope D) (Inv : D.State → Prop)
    (P : OperationPolicy D.AppOp) : Prop where
  replay : Laws S Inv P
  policy : PolicyLaws S Inv P

theorem emptyPolicyLaws (S : Scope D) (Inv : D.State → Prop)
    (commute : ∀ a b, a ∈ S.events → b ∈ S.events →
      ¬ S.context.vis a b → ¬ S.context.vis b a → InvariantOrder.Commutes D Inv a b) :
    PolicyLaws S Inv (commutingPolicy D.AppOp) where
  concurrent_exact a b ha hb _ _ hv hw := by
    simp [commutingPolicy,commute a b ha hb hv hw]
  no_chain _ _ _ _ _ _ _ _ := by simp [commutingPolicy]

abbrev restrict := @CertifiedReplay.restrict D

/-- Removing possible absorbers can add order edges. The state domain is
identical on both sides; restriction does not redefine commutation. -/
theorem order_restrict (Inv : D.State → Prop) (P : OperationPolicy D.AppOp)
    (C : ReplayContext D) {E F : Set (Op D.AppOp)} (sub : E ⊆ F)
    {a b : Op D.AppOp} (edge : InvariantOrder.order Inv P C F a b) :
    InvariantOrder.order Inv P C E a b := by
  rcases edge with causal | ⟨ab,ba,policy,noAbsorber⟩
  · exact Or.inl causal
  · exact Or.inr ⟨ab,ba,policy,fun ⟨c,member,vis,nc⟩ =>
      noAbsorber ⟨c,sub member,vis,nc⟩⟩

theorem restrict_laws {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : Laws S Inv P) (E : Set (Op D.AppOp)) (sub : E ⊆ S.events)
    (closed : ∀ a ∈ S.events, ∀ b ∈ E, S.context.vis a b → a ∈ E) :
    Laws (restrict S E) Inv P := by
  constructor
  · intro H s rep
    exact laws.represented_valid H s rep.2
  · intro H s e represented ready
    exact ⟨Set.insert_subset ready.1 represented.1,
      laws.update_closed H s e represented.2 (CertifiedReplay.ready_of_restrict sub closed ready)⟩
  · intro H s a b represented readyA readyB notab notba noab noba
    exact laws.diamond H s a b represented.2
      (CertifiedReplay.ready_of_restrict sub closed readyA)
      (CertifiedReplay.ready_of_restrict sub closed readyB) notab notba
      (fun edge => noab (order_restrict Inv P S.context sub edge))
      (fun edge => noba (order_restrict Inv P S.context sub edge))

theorem restrict_policyLaws {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : PolicyLaws S Inv P) (E : Set (Op D.AppOp)) (sub : E ⊆ S.events) :
    PolicyLaws (restrict S E) Inv P where
  concurrent_exact a b ha hb distinct replica hv hw :=
    laws.concurrent_exact a b (sub ha) (sub hb) distinct replica hv hw
  no_chain a b c ha hb hc ab bc := laws.no_chain a b c (sub ha) (sub hb) (sub hc) ab bc

theorem restrict_restrictedLaws {S : Scope D} {P : OperationPolicy D.AppOp}
    (laws : RestrictedLaws S Inv P) (E : Set (Op D.AppOp)) (sub : E ⊆ S.events)
    (closed : ∀ a ∈ S.events, ∀ b ∈ E, S.context.vis a b → a ∈ E) :
    RestrictedLaws (restrict S E) Inv P :=
  ⟨restrict_laws laws.replay E sub closed,restrict_policyLaws laws.policy E sub⟩

#print axioms convergence_on
#print axioms restrict_restrictedLaws

end Sal.MRDTs.Paper1.InvariantReplay
