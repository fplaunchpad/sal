import Sal.MRDTs.Paper1.ConcreteORSetRepresentation

namespace Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]


theorem representation_unique {C : ReplayContext (D α).toUpdateSig}
    {E : Set (Event α)} {s t : State α}
    (hs : representation C E s) (ht : representation C E t) : s = t := by
  ext p
  exact (hs.1 p).trans (ht.1 p).symm

theorem sorted_respects_raw (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (sorted : List (Event α)) (hperm : listPermOf sorted E)
    (trans : Transitive C.vis) (mono : ∀ a b, C.vis a b → a.time < b.time)
    (hsort : respects sorted (Before C.vis E)) :
    respects sorted (paperOrder (EventSpec.conflict α) C E) := by
  apply hsort.imp_of_mem
  intro a b ha hb hn hedge
  apply hn
  rcases hedge with ⟨vis, noncomm⟩ | ⟨_, _, hrc, noAbsorber⟩
  · exact before_of_vis C.vis E trans mono ((hperm.2 a).mp ha) vis
      (EventSpec.noncomm_same_element _ _ noncomm)
  · obtain ⟨x, hremove, hadd⟩ := hrc
    change b.2.2 = .remove x at hremove
    change a.2.2 = .add x at hadd
    have early : Early C.vis E b := Or.inl ⟨x, hremove⟩
    have late : ¬ Early C.vis E a := by
      rintro (⟨y, hy⟩ | ⟨z, hz, hvis, hzop⟩)
      · rw [hadd] at hy
        cases hy
      · apply noAbsorber ⟨z, hz, hvis, ?_⟩
        rcases a with ⟨ats, ar, aop⟩
        rcases z with ⟨zt, zr, zop⟩
        change aop = .add x at hadd
        simp only at hzop
        subst aop
        simp only [element] at hzop
        subst zop
        exact EventSpec.add_remove_noncomm _ _ _ _ x
    simp [Before, rank, early, late]

theorem represents_raw_canonical (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (s : State α) (h : representation C E s) :
    ∃ π : List (Event α), listPermOf π E ∧
      respects π (paperOrder (EventSpec.conflict α) C E) ∧
      applySeq (D α).toUpdateSig (D α).init π = s := by
  obtain ⟨π,hp⟩ := h.2.1
  obtain ⟨sorted,perm,ordered⟩ := exists_sorted C.vis E π hp
  have total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → C.vis a b ∨ C.vis b a := by
    intro a ha b hb ne same
    obtain ⟨r,er,head,mem⟩ := h.2.2.1 a ha
    obtain ⟨q,eq,other,member⟩ := h.2.2.1 b hb
    exact C.vis_total_same_replica head mem other member ne same
  refine ⟨sorted,perm,sorted_respects_raw C E sorted perm h.2.2.2.1 h.2.2.2.2 ordered,?_⟩
  apply Finset.ext
  intro p
  exact (represents_sorted_fold C.vis E h.2.2.2.1 h.2.2.2.2 total sorted perm ordered p).trans
    (h.1 p).symm

theorem raw_noncomm_kills (p : Record α) (z : Event α)
    (nc : ¬ (D α).toUpdateSig.commutes (p.2.1,p.1,SetOp.add p.2.2) z) :
    kills p.1 p.2.2 z := by
  have he := EventSpec.noncomm_same_element (p.2.1,p.1,SetOp.add p.2.2) z nc
  rcases z with ⟨zt,zr,zo⟩
  cases zo with
  | remove x =>
    change p.2.2 = x at he
    exact he.symm
  | add x =>
    change p.2.2 = x at he
    refine ⟨?_,he.symm⟩
    by_contra ne
    exact nc (NeemScope.adds_commute_of_replica_ne p.2.1 p.1 zt zr p.2.2 x (Ne.symm ne))


end Sal.MRDTs.Paper1.EfficientORSet.ConcreteRep
