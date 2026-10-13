import Sal.MRDTs.Paper1.ConcreteORSetSorting

namespace Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem joint_maximal (C : ReplayContext (D α).toUpdateSig) (E : Set (Event α))
    (π : List (Event α)) (perm : listPermOf π E) (nonempty : E.Nonempty)
    (trans : Transitive C.vis) (mono : ∀ a b, C.vis a b → a.time < b.time) :
    ∃ e ∈ E,
      (∀ x ∈ E, x ≠ e → ¬ paperOrder (EventSpec.conflict α) C E e x) ∧
      (∀ x ∈ E, x ≠ e → ¬ (ConcreteMRDT.MetadataDependencies.ofConcrete C).before e x) := by
  obtain ⟨sorted,hperm,hsort⟩ := exists_sorted C.vis E π perm
  apply ConcreteMRDT.joint_maximal_of_enumeration sorted hperm nonempty
  · exact sorted_respects_raw C E sorted hperm trans mono hsort
  · apply hsort.imp_of_mem
    intro a b ha hb no edge
    exact no (before_of_vis C.vis E trans mono ((hperm.2 a).mp ha) edge.1
      (EventSpec.noncomm_same_element b a edge.2))

end Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep

namespace Sal.MRDTs.Paper1.ORSet.ConcreteRep
open Foundation
variable {α : Type} [DecidableEq α]

theorem joint_maximal (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α)))
    (s : (D α).State) (rep : representation C E s) (nonempty : E.Nonempty) :
    ∃ e ∈ E,
      (∀ x ∈ E, x ≠ e → ¬ paperOrder (conflict α) C E e x) ∧
      (∀ x ∈ E, x ≠ e → ¬ (ConcreteMRDT.MetadataDependencies.ofConcrete C).before e x) := by
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  obtain ⟨π,hp,hr,_⟩ := rep
  have ordered : respects π (paperOrder (conflict α) C E) := by
    apply hr.imp
    intro a b h edge
    exact h ((paperOrder_iff_loOn restrictedLaws C E b a).mp edge)
  have metadata : respects π (ConcreteMRDT.MetadataDependencies.ofConcrete C).before := by
    apply hr.imp
    intro a b h edge
    exact h ((paperOrder_iff_loOn restrictedLaws C E b a).mp (Or.inl edge))
  exact ConcreteMRDT.joint_maximal_of_enumeration π hp nonempty ordered metadata

end Sal.MRDTs.Paper1.ORSet.ConcreteRep

namespace Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

/-- Replacing or removing a different birth record is a concrete conflict,
even when two adds commute at the observation level. -/
theorem kills_noncomm (p : Record α) (e : Event α)
    (kill : kills p.1 p.2.2 e) (different : (p.2.1,p.1,SetOp.add p.2.2) ≠ e) :
    ¬ (D α).toUpdateSig.commutes (p.2.1,p.1,SetOp.add p.2.2) e := by
  rcases p with ⟨r,t,x⟩
  rcases e with ⟨u,q,op⟩
  cases op with
  | remove y =>
    change y = x at kill
    subst y
    exact EventSpec.add_remove_noncomm t r u q x
  | add y =>
    change q = r ∧ y = x at kill
    obtain ⟨replica,element⟩ := kill
    subst q
    subst y
    have times : t ≠ u := by
      intro equal
      exact different (by simp [equal])
    intro commute
    have equation := commute (∅ : State α)
    change update (update ∅ (t,r,.add x)) (u,r,.add x) =
      update (update ∅ (u,r,.add x)) (t,r,.add x) at equation
    have old : (r,t,x) ∈ update (update ∅ (u,r,.add x)) (t,r,.add x) := by
      simp [update]
    rw [← equation] at old
    simpa [update,times] using old

/-- A local replay step needs only evidence about live records killed by the
step, and absence of a later killer of the new record. It needs no merge law. -/
theorem represents_snoc (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (s : State α) (e : Event α)
    (fresh : e ∉ E) (irrefl : ¬ C.vis e e) (rep : Represents C.vis E s)
    (newLive : ∀ p : Record α, (p.2.1,p.1,SetOp.add p.2.2) = e → ¬ dead C.vis E p)
    (killedBefore : ∀ p : Record α, live C.vis E p → kills p.1 p.2.2 e →
      C.vis (p.2.1,p.1,SetOp.add p.2.2) e) :
    Represents C.vis (E ∪ {e}) (update s e) := by
  intro p
  rw [mem_update_iff,rep p]
  by_cases birth : (p.2.1,p.1,SetOp.add p.2.2) = e
  · have notdead := newLive p birth
    have notdeadUnion : ¬ dead C.vis (E ∪ {e}) p := by
      rintro ⟨z,hz,vis,kill⟩
      rcases hz with hz | equal
      · exact notdead ⟨z,hz,vis,kill⟩
      · rw [Set.mem_singleton_iff] at equal
        subst z
        exact irrefl (birth ▸ vis)
    simp only [live,notdeadUnion,birth,Set.mem_union,Set.mem_singleton_iff,
      fresh,notdead,or_true,true_or,true_and]
    trivial
  · simp only [live,Set.mem_union,Set.mem_singleton_iff,birth,or_false]
    constructor
    · rintro (equal | ⟨⟨member,alive⟩,notkill⟩)
      · exact False.elim (birth equal.symm)
      · refine ⟨member,?_⟩
        rintro ⟨z,hz,vis,kill⟩
        rcases hz with old | equal
        · exact alive ⟨z,old,vis,kill⟩
        · exact notkill (Set.mem_singleton_iff.mp equal ▸ kill)
    · rintro ⟨member,alive⟩
      have oldLive : live C.vis E p :=
        ⟨member,fun h => alive (dead_mono C.vis Set.subset_union_left h)⟩
      exact Or.inr ⟨oldLive,fun kill =>
        alive ⟨e,Or.inr rfl,killedBefore p oldLive kill,kill⟩⟩

private theorem replica_vis (C : ReplayContext (D α).toUpdateSig)
    (a b : Event α) (ha : a ∈ C.events) (hb : b ∈ C.events)
    (ne : a ≠ b) (same : a.2.1 = b.2.1) : C.vis a b ∨ C.vis b a := by
  obtain ⟨r,E,head,mem⟩ := ha
  obtain ⟨q,F,other,member⟩ := hb
  exact C.vis_total_same_replica head mem other member ne same

theorem live_killed_before (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (e : Event α)
    (member : e ∈ U) (supported : ConcreteMRDT.Supported C U)
    (semantic : ∀ x ∈ U, x ≠ e →
      ¬ paperOrder (EventSpec.conflict α) C U e x)
    (metadata : ∀ x ∈ U, x ≠ e →
      ¬ (ConcreteMRDT.MetadataDependencies.ofConcrete C).before e x) :
    ∀ p : Record α, live C.vis (U \ {e}) p → kills p.1 p.2.2 e →
      C.vis (p.2.1,p.1,SetOp.add p.2.2) e := by
  intro p living kill
  let b : Event α := (p.2.1,p.1,SetOp.add p.2.2)
  have hb : b ∈ U := living.1.1
  have ne : b ≠ e := living.1.2
  have nc := kills_noncomm p e kill ne
  have notforward : ¬ C.vis e b := fun vis => metadata b hb ne
    ⟨vis,fun commute => nc (Foundation.commutes_symm commute)⟩
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x =>
    change r = p.1 ∧ x = p.2.2 at kill
    exact (replica_vis C b (t,r,.add x) (supported b hb)
      (supported _ member) ne kill.1.symm).resolve_right notforward
  | remove x =>
    change x = p.2.2 at kill
    subst x
    by_contra notback
    apply semantic b hb ne
    refine Or.inr ⟨notforward,notback,⟨p.2.2,rfl,rfl⟩,?_⟩
    rintro ⟨z,hz,vis,conflict⟩
    have killed := raw_noncomm_kills p z conflict
    exact living.2 ⟨z,⟨hz,fun equal => notback (equal ▸ vis)⟩,vis,killed⟩

theorem represents_snoc_maximal (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (s : State α) (e : Event α)
    (member : e ∈ U) (supported : ConcreteMRDT.Supported C U)
    (irrefl : ∀ x, ¬ C.vis x x)
    (semantic : ∀ x ∈ U, x ≠ e →
      ¬ paperOrder (EventSpec.conflict α) C U e x)
    (metadata : ∀ x ∈ U, x ≠ e →
      ¬ (ConcreteMRDT.MetadataDependencies.ofConcrete C).before e x)
    (rep : Represents C.vis (U \ {e}) s) :
    Represents C.vis U (update s e) := by
  have union : (U \ {e}) ∪ {e} = U := by
    ext x
    simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · rintro (h | rfl)
      · exact h.1
      · exact member
    · intro hx
      by_cases equal : x = e
      · exact Or.inr equal
      · exact Or.inl ⟨hx,equal⟩
  rw [← union]
  apply represents_snoc C _ s e (by simp) (irrefl e) rep
  · intro p birth
    rintro ⟨z,hz,vis,kill⟩
    have different : e ≠ z := Ne.symm (show z ≠ e from hz.2)
    exact metadata z hz.1 hz.2
      ⟨birth ▸ vis,birth ▸ kills_noncomm p z kill (birth.symm ▸ different)⟩
  · exact live_killed_before C U e member supported semantic metadata

/-- Finite supported histories have concrete representatives, constructed by
the existing tag-sensitive sorting proof rather than a Join assumption. -/
theorem representation_exists (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (π : List (Event α)) (perm : listPermOf π E)
    (supported : ConcreteMRDT.Supported C E) (trans : Transitive C.vis)
    (mono : ∀ a b, C.vis a b → a.time < b.time) :
    ∃ s, representation C E s := by
  obtain ⟨sorted,hperm,hsort⟩ := exists_sorted C.vis E π perm
  have total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → C.vis a b ∨ C.vis b a :=
    fun a ha b hb ne same => replica_vis C a b (supported a ha) (supported b hb) ne same
  exact ⟨sorted.foldl update (∅ : State α),represents_sorted_fold C.vis E trans mono total sorted hperm hsort,
    ⟨sorted,hperm⟩,supported,trans,mono⟩

theorem peel_choice (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (s : State α) (rep : representation C U s)
    (nonempty : U.Nonempty)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed U)
    (irrefl : ∀ x, ¬ C.vis x x) :
    Nonempty (ConcreteMRDT.Raw.PeelChoice (EventSpec.conflict α)
      representation C (ConcreteMRDT.MetadataDependencies.ofConcrete C) U) := by
  let M := ConcreteMRDT.MetadataDependencies.ofConcrete C
  obtain ⟨π,hp⟩ := rep.2.1
  have supported := rep.2.2.1
  have trans := rep.2.2.2.1
  have mono := rep.2.2.2.2
  obtain ⟨e,he,semantic,metadata⟩ := joint_maximal C U π hp nonempty trans mono
  have pastSub : M.Past e ⊆ U := M.past_subset U e closed he
  obtain ⟨pre,hpre⟩ := ConcreteMRDT.enumeration_subset hp
    (show U \ {e} ⊆ U from fun _ h => h.1)
  obtain ⟨past,hpast⟩ := ConcreteMRDT.enumeration_subset hp
    (show M.Past e \ {e} ⊆ U from fun _ h => pastSub h.1)
  obtain ⟨wholePast,hwhole⟩ := ConcreteMRDT.enumeration_subset hp pastSub
  obtain ⟨a,ha⟩ := representation_exists C _ pre hpre
    (fun x h => supported x h.1) trans mono
  obtain ⟨b,hb⟩ := representation_exists C _ past hpast
    (fun x h => supported x (pastSub h.1)) trans mono
  refine ⟨⟨e,he,semantic,metadata,a,b,ha,hb,?_,?_⟩⟩
  · refine ⟨represents_snoc_maximal C (M.Past e) b e (Or.inl rfl)
      (fun x h => supported x (pastSub h)) irrefl
      (M.past_semantic_maximal (EventSpec.conflict α) trans irrefl e) ?_ hb.1,
      ⟨wholePast,hwhole⟩,(fun x h => supported x (pastSub h)),trans,mono⟩
    intro x hx ne edge
    exact irrefl e (trans edge.1 (M.past_vis trans hx ne))
  · exact ⟨represents_snoc_maximal C U a e he supported irrefl semantic metadata ha.1,
      ⟨π,hp⟩,supported,trans,mono⟩

end Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep

namespace Sal.MRDTs.Paper1.ORSet.ConcreteRep
open Foundation
variable {α : Type} [DecidableEq α]

private theorem raw_maximal (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (e : Op (Update α))
    (maximal : ∀ x ∈ E, x ≠ e →
      ¬ paperOrder (conflict α) C E e x) :
    ∀ x ∈ E, x ≠ e → ¬ @loOn (D α).toUpdateSig (conflict α).lift C E e x := by
  intro x hx ne edge
  apply maximal x hx ne
  have paper := (paperOrder_iff_loOn restrictedLaws C E e x).mpr edge
  exact paper

/-- Produces the complete represented peel data without invoking merge or
representation Join. -/
theorem peel_choice (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (s : (D α).State)
    (rep : representation C U s) (nonempty : U.Nonempty)
    (supported : ConcreteMRDT.Supported C U)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    Nonempty (ConcreteMRDT.Raw.PeelChoice (conflict α)
      representation C (ConcreteMRDT.MetadataDependencies.ofConcrete C) U) := by
  classical
  letI : ReplayPolicy (D α).toUpdateSig := (conflict α).lift
  let M := ConcreteMRDT.MetadataDependencies.ofConcrete C
  obtain ⟨e,he,semantic,metadata⟩ := joint_maximal C U s rep nonempty
  obtain ⟨π,hp,_,_⟩ := rep
  have pastSub : M.Past e ⊆ U := M.past_subset U e closed he
  obtain ⟨pre,hpre⟩ := ConcreteMRDT.enumeration_subset hp
    (show U \ {e} ⊆ U from fun _ h => h.1)
  obtain ⟨past,hpast⟩ := ConcreteMRDT.enumeration_subset hp
    (show M.Past e \ {e} ⊆ U from fun _ h => pastSub h.1)
  obtain ⟨a,ha⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
    (fun {_ _ _} h k => trans h k) irrefl hpre (fun x h => supported x h.1)
  obtain ⟨b,hb⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
    (fun {_ _ _} h k => trans h k) irrefl hpast (fun x h => supported x (pastSub h.1))
  refine ⟨⟨e,he,semantic,metadata,a,b,ha,hb,?_,?_⟩⟩
  · exact isCanonicalState_snoc (Or.inl rfl)
      (raw_maximal C _ e (M.past_semantic_maximal (conflict α) trans irrefl e)) hb
  · exact isCanonicalState_snoc he (raw_maximal C U e semantic) ha

end Sal.MRDTs.Paper1.ORSet.ConcreteRep
