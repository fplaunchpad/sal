import Sal.MRDTs.Paper1.ConcreteORSetMetadata
import Sal.MRDTs.Paper1.ConcreteReplay

namespace Sal.MRDTs.Paper1.EfficientORSet.RawReplay
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

abbrev representation := ConcreteRep.representation (α := α)

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


def scheme (C : ReplayContext (D α).toUpdateSig) :=
  ConcreteMRDT.MetadataDependencies.ofConcrete C

theorem representsCanonical : ∀ C E s, representation C E s →
    ConcreteMRDT.Canonical (EventSpec.conflict α) C E s :=
  represents_raw_canonical

theorem unique : ConcreteMRDT.Raw.Unique (representation (α := α)) :=
  fun _ _ _ _ hs ht => representation_unique hs ht

theorem initial (C : ReplayContext (D α).toUpdateSig)
    (trans : Transitive C.vis) (mono : ∀ a b, C.vis a b → a.time < b.time) :
    representation C ∅ (D α).init := by
  refine ⟨?_,⟨[],?_,?_⟩,?_,trans,mono⟩
  · intro p
    simp [D,live]
  · simp
  · simp
  · simp

theorem initial_from_representation (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (s : State α) (h : representation C E s) :
    representation C ∅ (D α).init := initial C h.2.2.2.1 h.2.2.2.2

theorem finite (C : ReplayContext (D α).toUpdateSig) (E : Set (Event α))
    (s : State α) (h : representation C E s) : ∃ π, listPermOf π E := h.2.1

theorem peel_choice (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (s : State α) (rep : representation C U s)
    (nonempty : U.Nonempty) (closed : (scheme (α := α) C).Closed U)
    (irrefl : ∀ x, ¬ C.vis x x) :
    Nonempty (ConcreteMRDT.Raw.PeelChoice (EventSpec.conflict α)
      representation C (scheme (α := α) C) U) :=
  ConcreteRep.peel_choice C U s rep nonempty closed irrefl

theorem replaySupply (C : ReplayContext (D α).toUpdateSig)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (mono : ∀ a b, C.vis a b → a.time < b.time) :
    ConcreteMRDT.Raw.ReplaySupply (EventSpec.conflict α) representation
      (scheme (α := α)) C := by
  refine ⟨?_,?_⟩
  · intro E π perm supported
    exact ConcreteRep.representation_exists C E π perm supported trans mono
  · intro E s rep _ nonempty closed
    exact peel_choice C E s rep nonempty closed irrefl

#print axioms representsCanonical
#print axioms unique
#print axioms replaySupply

end Sal.MRDTs.Paper1.EfficientORSet.RawReplay

namespace Sal.MRDTs.Paper1.ORSet.RawReplay
open Foundation
open Classical
variable {α : Type} [DecidableEq α]

def scheme (C : ReplayContext (D α).toUpdateSig) :=
  ConcreteMRDT.MetadataDependencies.ofConcrete C

def representation (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (s : (D α).State) : Prop :=
  ConcreteRep.representation C E s ∧ ConcreteMRDT.Supported C E

theorem representsCanonical (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (s : (D α).State) (h : representation C E s) :
    ConcreteMRDT.Canonical (conflict α) C E s := by
  obtain ⟨π,hp,hr,hf⟩ := h.1
  refine ⟨π,hp,?_,hf⟩
  apply hr.imp
  intro a b hab edge
  exact hab ((paperOrder_iff_loOn restrictedLaws C E b a).mp edge)

theorem unique : ConcreteMRDT.Raw.Unique (representation (α := α)) := by
  intro C E s t hs ht
  obtain ⟨π,hp,hr,hf⟩ := representsCanonical C E s hs
  obtain ⟨π',hp',hr',hf'⟩ := representsCanonical C E t ht
  exact hf.symm.trans ((convergence_on_guarded Guarded.laws (C := C)
    (D α).init hs.2 hp hp' hr hr').trans hf')

theorem initial (C : ReplayContext (D α).toUpdateSig) :
    representation C ∅ (D α).init := by
  refine ⟨⟨[],?_,?_,rfl⟩,?_⟩
  · exact ⟨List.nodup_nil,by simp⟩
  · simp [respects]
  · simp [ConcreteMRDT.Supported]

theorem finite (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α)))
    (s : (D α).State) (h : representation C E s) : ∃ π, listPermOf π E := by
  obtain ⟨π,hp,_,_⟩ := h.1
  exact ⟨π,hp⟩

/-- The selected metadata reconstruction reuses the earlier observable
peel proof. Raw canonicality and uniqueness above are proved separately from
that proof, and this adapter invokes no representation Join theorem. -/
theorem peel_choice (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (s : (D α).State) (rep : representation C U s)
    (nonempty : U.Nonempty) (closed : (scheme (α := α) C).Closed U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    Nonempty (ConcreteMRDT.Raw.PeelChoice (conflict α)
      representation C (scheme (α := α) C) U) := by
  obtain ⟨choice⟩ := ConcreteRep.peel_choice C U s rep.1 nonempty rep.2 closed trans irrefl
  let oldM := ConcreteMRDT.MetadataDependencies.ofConcrete C
  have pastSub : oldM.Past choice.event ⊆ U := oldM.past_subset U choice.event closed choice.member
  refine ⟨⟨choice.event,choice.member,?_,choice.metadata_maximal,
    choice.remainder,choice.past,⟨choice.remainder_rep,?_⟩,
    ⟨choice.past_rep,?_⟩,⟨choice.reconstructed_past,?_⟩,
    ⟨choice.reconstructed_union,rep.2⟩⟩⟩
  · exact choice.semantic_maximal
  · exact fun x hx => rep.2 x hx.1
  · exact fun x hx => rep.2 x (pastSub hx.1)
  · exact fun x hx => rep.2 x (pastSub hx)

theorem replaySupply (C : ReplayContext (D α).toUpdateSig)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    ConcreteMRDT.Raw.ReplaySupply (conflict α) representation
      (scheme (α := α)) C := by
  refine ⟨?_,?_⟩
  · intro E π perm supported
    obtain ⟨s,hs⟩ := @isCanonicalState_exists_of_replayLaws (D α).toUpdateSig
      (conflict α).lift restrictedLaws.replayLaws C
      (fun {_ _ _} h k => trans h k) irrefl E π perm supported
    exact ⟨s,hs,supported⟩
  · intro E s rep _ nonempty closed
    exact peel_choice C E s rep nonempty closed trans irrefl

#print axioms unique
#print axioms replaySupply
end Sal.MRDTs.Paper1.ORSet.RawReplay
