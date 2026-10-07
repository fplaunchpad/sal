import Sal.MRDTs.Paper1.QueryReplay
import Sal.MRDTs.Paper1.EfficientORSetEventSpec

/-! The efficient OR-set meets the query-relative implementation replay laws.
Its hidden per-replica tags are retained for merge, but add/add is no longer
classified as a replay conflict solely because those tags differ. -/
namespace Sal.MRDTs.Paper1.EfficientORSet.QuerySpec
open Foundation
open QueryReplay
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]
local instance : ReplayPolicy (D α).toUpdateSig := rc

def abstraction : QueryReplay.Abstraction (D α) where
  Abstract := Finset α
  abs := elements
  step := setStep
  read s x := decide (x ∈ s)
  update_abs := elements_update
  query_abs _ _ := rfl
  separates a b h := by
    ext x
    have hx := h x
    by_cases ha : x ∈ a <;> by_cases hb : x ∈ b <;> simp_all

/-- All future local updates and reads see exactly the ordinary set. -/
theorem equivalent_iff_elements (s t : State α) :
    Equivalent (D α) s t ↔ elements s = elements t :=
  abstraction.equivalent_iff s t

theorem commutes_of_views (a b : Event α)
    (h : ∀ s : State α, elements (update (update s a) b) =
      elements (update (update s b) a)) : Commutes (D α) a b :=
  fun s => (equivalent_iff_elements _ _).mpr (h s)

theorem adds_commute (ta ra tb rb : Nat) (x y : α) :
    Commutes (D α) (ta,ra,.add x) (tb,rb,.add y) := by
  apply commutes_of_views
  intro s
  simp [elements_update,setStep,Finset.insert_comm]

theorem removes_commute (ta ra tb rb : Nat) (x y : α) :
    Commutes (D α) (ta,ra,.remove x) (tb,rb,.remove y) := by
  apply commutes_of_views
  intro s
  ext z
  simp only [elements_update,setStep,Finset.mem_erase]
  tauto

theorem add_remove_commute_of_ne (ta ra tb rb : Nat) {x y : α} (ne : x ≠ y) :
    Commutes (D α) (ta,ra,.add x) (tb,rb,.remove y) := by
  apply commutes_of_views
  intro s
  ext z
  simp [elements_update,setStep]
  grind

theorem add_remove_conflict (ta ra tb rb : Nat) (x : α) :
    ¬ Commutes (D α) (ta,ra,.add x) (tb,rb,.remove x) := by
  intro h
  have same := (equivalent_iff_elements _ _).mp (h (∅ : State α))
  change elements (update (update (∅ : State α) (ta,ra,.add x)) (tb,rb,.remove x)) =
    elements (update (update (∅ : State α) (tb,rb,.remove x)) (ta,ra,.add x)) at same
  simp only [elements_update,setStep] at same
  simp [elements] at same

theorem commutes_symm {a b : Event α} (h : Commutes (D α) a b) :
    Commutes (D α) b a := fun s => equivalent_symm (h s)

theorem noncomm_exact (a b : Event α) :
    ¬ Commutes (D α) a b ↔
      (EventSpec.conflict α).before a.op b.op ∨
      (EventSpec.conflict α).before b.op a.op := by
  rcases a with ⟨ta,ra,ao⟩
  rcases b with ⟨tb,rb,bo⟩
  cases ao with
  | add x =>
      cases bo with
      | add y =>
          have hc := adds_commute ta ra tb rb x y
          simp [EventSpec.conflict,Op.op,hc]
      | remove y =>
          by_cases same : x = y
          · subst y
            have hn := add_remove_conflict ta ra tb rb x
            simp [EventSpec.conflict,Op.op,hn]
          · simp [EventSpec.conflict,Op.op,same,
              add_remove_commute_of_ne ta ra tb rb same]
  | remove x =>
      cases bo with
      | remove y =>
          have hc := removes_commute ta ra tb rb x y
          simp [EventSpec.conflict,Op.op,hc]
      | add y =>
          by_cases same : x = y
          · subst y
            have hn : ¬ Commutes (D α) (ta,ra,.remove x) (tb,rb,.add x) :=
              fun h => add_remove_conflict tb rb ta ra x (commutes_symm h)
            simp [EventSpec.conflict,Op.op,hn]
          · have hc := commutes_symm (add_remove_commute_of_ne tb rb ta ra (Ne.symm same))
            simp [EventSpec.conflict,Op.op,Ne.symm same,hc]

private theorem erase_step_congr (x : α) (s t : Finset α) (e : Event α)
    (h : s.erase x = t.erase x) :
    (setStep s e).erase x = (setStep t e).erase x := by
  ext y
  have hy := congrArg (fun z : Finset α => y ∈ z) h
  rcases e with ⟨ts,r,op⟩
  cases op <;> simp only [setStep,Finset.mem_erase,Finset.mem_insert] at * <;> grind

private theorem erase_fold_congr (x : α) (s t : Finset α) (xs : List (Event α))
    (h : s.erase x = t.erase x) :
    (xs.foldl setStep s).erase x = (xs.foldl setStep t).erase x := by
  induction xs generalizing s t with
  | nil => exact h
  | cons e xs ih => exact ih _ _ (erase_step_congr x s t e h)

theorem laws : QueryReplay.Laws (D α) (EventSpec.conflict α) := by
  refine ⟨noncomm_exact,EventSpec.no_chain,?_⟩
  intro s a b c between before conflict
  obtain ⟨x,ha,hb⟩ := before
  change a.op = .remove x at ha
  change b.op = .add x at hb
  have hc : c.op = .remove x := by
    rcases (noncomm_exact b c).mp conflict with edge | edge
    · obtain ⟨y,hy,_⟩ := edge
      rw [hb] at hy
      cases hy
    · obtain ⟨y,hy,hby⟩ := edge
      rw [hb] at hby
      cases hby
      exact hy
  change a.2.2 = .remove x at ha
  change b.2.2 = .add x at hb
  change c.2.2 = .remove x at hc
  apply (equivalent_iff_elements _ _).mpr
  have hbase :
      (elements (update (update s b) a)).erase x =
      (elements (update (update s a) b)).erase x := by
    simp [elements_update,setStep,ha,hb]
  have hfold := erase_fold_congr x _ _ between hbase
  change elements (update (between.foldl update (update (update s b) a)) c) =
    elements (update (between.foldl update (update (update s a) b)) c)
  rw [elements_update,elements_update]
  simpa [setStep,hc,Op.op,elements_fold] using hfold

theorem specificationCompatibility :
    QueryReplay.SpecificationCompatibility (D α) (EventSpec.spec α) := by
  intro a b hc
  apply DeterministicSpec.language_commutes
  intro s
  let repr : State α := s.image (fun x => (0,0,x))
  have hv : elements repr = s := by
    simp [repr,elements,Finset.image_image,Function.comp_def]
  have same := (equivalent_iff_elements _ _).mp (hc repr)
  change elements (update (update repr a) b) =
    elements (update (update repr b) a) at same
  simpa only [elements_update,hv] using same

theorem sorted_respects_order (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (sorted : List (Event α))
    (hperm : listPermOf sorted E) (ht : Transitive C.vis)
    (hm : ∀ a b, C.vis a b → a.time < b.time)
    (hsort : respects sorted (Before C.vis E)) :
    respects sorted (QueryReplay.order (EventSpec.conflict α) C E) := by
  apply hsort.imp_of_mem
  intro a b ha hb hn hedge
  apply hn
  rcases hedge with ⟨vis,noncomm⟩ | ⟨_,_,hrc,noAbsorber⟩
  · exact before_of_vis C.vis E ht hm ((hperm.2 a).mp ha) vis
      (EventSpec.noncomm_same_element _ _ (fun h => noncomm (of_state_commutes h)))
  · obtain ⟨x,hremove,hadd⟩ := hrc
    change b.2.2 = .remove x at hremove
    change a.2.2 = .add x at hadd
    have early : Early C.vis E b := Or.inl ⟨x,hremove⟩
    have late : ¬ Early C.vis E a := by
      rintro (⟨y,hy⟩ | ⟨z,hz,hvis,hzop⟩)
      · rw [hadd] at hy
        cases hy
      · apply noAbsorber ⟨z,hz,hvis,?_⟩
        rcases a with ⟨ats,ar,aop⟩
        rcases z with ⟨zt,zr,zop⟩
        change aop = .add x at hadd
        simp only at hzop
        subst aop
        simp only [element] at hzop
        subst zop
        exact add_remove_conflict _ _ _ _ x
    simp [Before,rank,early,late]

/-- Execution evidence retains the tag representation needed by merge. Its
sorted witness establishes canonicality in the common observable algebra. -/
theorem canonical_of_representation (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (s : State α)
    (canonical : IsCanonicalState C E s) (represented : Represents C.vis E s)
    (support : ∀ e ∈ E, e ∈ C.events) (ht : Transitive C.vis)
    (hm : ∀ a b, C.vis a b → a.time < b.time) :
    QueryReplay.Canonical (D α) (EventSpec.conflict α) C E s := by
  obtain ⟨ops,hp,_,_⟩ := canonical
  obtain ⟨sorted,hperm,hsort⟩ := exists_sorted C.vis E ops hp
  have total : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → a.2.1 = b.2.1 → C.vis a b ∨ C.vis b a := by
    intro a ha b hb hne hr
    obtain ⟨r,er,hhead,hea⟩ := support a ha
    obtain ⟨r',er',hhead',heb⟩ := support b hb
    exact C.vis_total_same_replica hhead hea hhead' heb hne hr
  have state : applySeq (D α).toUpdateSig (D α).init sorted = s := by
    apply Finset.ext
    intro p
    exact (represents_sorted_fold C.vis E ht hm total sorted hperm hsort p).trans
      (represented p).symm
  have ordered := sorted_respects_order C E sorted hperm ht hm hsort
  refine ⟨sorted,hperm,?_,?_⟩
  · exact ordered.imp (fun {a b} h edge => h
      ((QueryReplay.order_eq (D := D α)
        (EventSpec.conflict α) C E b a).mpr
        ((paperOrder_iff_loOn laws.toRestricted _ _ _ _).mpr edge)))
  · change applySeq (QueryReplay.algebra (D α)) (observe (D α) (D α).init) sorted =
      observe (D α) s
    rw [fold_observe,state]

theorem canonical_of_execution {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    ∀ v s E, C.ver v = some (s,E) →
      QueryReplay.Canonical (D α) (EventSpec.conflict α) C.replayContext E s := by
  obtain ⟨_,good,represented⟩ := represented_of_mintCertifiedV reach
  intro v s E hv
  exact canonical_of_representation C.replayContext E s (good.canonical v s E hv)
    (represented v s E hv) (good.version_events_supported v s E hv)
    (fun _ _ _ hab hbc => good.vis_trans hab hbc) (fun _ _ h => C.causal_mono h)

theorem certifiedVersionsRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    QueryReplay.VersionsRALinearizable (D α) (EventSpec.conflict α) (EventSpec.spec α) C :=
  QueryReplay.of_canonical laws (canonical_of_execution reach)
    specificationCompatibility EventSpec.foldHistorySound

theorem certifiedVersionsRA {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) issuance C) :
    QueryReplay.VersionsRALinearizable (D α) (EventSpec.conflict α) (EventSpec.spec α) C :=
  certifiedVersionsRAV reach.toV

theorem certifiedRA {C : Configuration (D α)}
    (reach : MintCertifiedReach (D α) issuance C) :
    QueryReplay.RALinearizable (D α) (EventSpec.conflict α) (EventSpec.spec α) C :=
  (certifiedVersionsRA reach).heads

theorem certifiedRAV {C : Configuration (D α)}
    (reach : MintCertifiedReachV (D α) (canonicalVirtualMergeBase (D α)) issuance C) :
    QueryReplay.RALinearizable (D α) (EventSpec.conflict α) (EventSpec.spec α) C :=
  (certifiedVersionsRAV reach).heads

/-- PASS+FAIL: supplied tags differ, but every future local observation agrees. -/
theorem same_replica_add_control (x : α) :
    Commutes (D α) (1,0,.add x) (2,0,.add x) ∧
      ¬ (D α).toUpdateSig.commutes (1,0,.add x) (2,0,.add x) :=
  ⟨adds_commute _ _ _ _ _ _,EventSpec.same_replica_adds_noncomm x⟩

/-- The criterion itself drops the metadata-only visibility conflict. -/
theorem ordering_control (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (x : α) (vis : C.vis (1,0,.add x) (2,0,.add x)) :
    paperOrder (EventSpec.conflict α) C E (1,0,.add x) (2,0,.add x) ∧
      ¬ QueryReplay.order (EventSpec.conflict α) C E (1,0,.add x) (2,0,.add x) := by
  refine ⟨Or.inl ⟨vis,EventSpec.same_replica_adds_noncomm x⟩,?_⟩
  simp [QueryReplay.order,EventSpec.conflict,Op.op,adds_commute]

/-- Observable equivalence is not a merge congruence, even for these simple
set states. A new tag survives an observed removal; an unchanged tag does not. -/
theorem merge_congruence_fails (x : α) : ¬ QueryReplay.MergeCongruence (D α) := by
  intro congruent
  let old : State α := {(0,1,x)}
  let fresh : State α := {(0,2,x)}
  have same : Equivalent (D α) old fresh :=
    (equivalent_iff_elements _ _).mpr (by simp [old,fresh,elements])
  have merged := congruent old old old fresh (∅ : State α) (∅ : State α)
    (equivalent_refl _ _) same (equivalent_refl _ _)
  have answer := equivalent_query merged x
  change decide (x ∈ elements (merge old old ∅)) =
    decide (x ∈ elements (merge old fresh ∅)) at answer
  simp [old,fresh,merge,elements] at answer

end Sal.MRDTs.Paper1.EfficientORSet.QuerySpec
