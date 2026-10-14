import Sal.MRDTs.Paper1.AddWinsPriorityQueueCanonical
import Sal.MRDTs.Paper1.SplitPolicy
import Sal.MRDTs.Paper1.ConcreteJoin

namespace Sal.MRDTs.Paper1.AddWinsPriorityQueue
open Foundation Instances.AddWinsPriorityQueue
open Classical
variable {α : Type} [DecidableEq α]
/-- The paper policy relates application operations, independently of event
identifiers: remove x is before add x. -/
def conflict (α : Type) : OperationPolicy (Update α) where
  before a b := ∃ x v, a = .remove x ∧ b = .add x v

theorem conflict_lift_eq : (conflict α).lift = (policy : EventOrder (D α).toUpdateSig) := by
  apply congrArg (fun f => (⟨f⟩ : EventOrder (D α).toUpdateSig))
  funext a b
  rcases a with ⟨t, r, ao⟩; rcases b with ⟨t', r', bo⟩
  dsimp only [OperationPolicy.lift, policy]
  cases ao <;> cases bo <;>
    simp [conflict, Op.op, order]
  all_goals split <;> simp_all [eq_comm]

theorem restrictedLaws : RestrictedLaws (D α).toUpdateSig (conflict α) := by
  constructor
  · intro a b
    simpa only [replayOrder_iff, conflict, Op.op] using noncomm_iff_replayOrder a b
  · rintro a b c ⟨⟨x,v, ha, hb⟩, ⟨y,w, hb', hc⟩⟩
    rw [hb] at hb'; cases hb'
  · intro s e a r ops hea hnc
    have hrc : (D α).toUpdateSig.replayBefore e a := by
      simpa only [replayOrder_iff, conflict, Op.op] using hea
    obtain ⟨x,v, he, ha⟩ := (replayOrder_iff e a).mp hrc
    have har := (noncomm_iff_replayOrder a r).mp hnc
    have hr : r.2.2 = .remove x := by
      rcases har with h | h
      · obtain ⟨y,w, ha', _⟩ := (replayOrder_iff a r).mp h
        rw [ha] at ha'; cases ha'
      · obtain ⟨y,w, hr, ha'⟩ := (replayOrder_iff r a).mp h
        rw [ha] at ha'; injection ha' with hxy; subst y; exact hr
    have hbase : EqExcept x (step (step s a) e) (step (step s e) a) := by
      constructor
      · intro p hp; simp [step, he, ha, hp]
      · simp [step,he,ha]
    have hfold := eqExcept_fold hbase ops
    change step _ r = step _ r
    apply Prod.ext
    · ext p
      simp only [step,hr,Finset.mem_filter]
      by_cases hp : p.1 = x
      · simp [hp]
      · exact and_congr (hfold.1 p hp) Iff.rfl
    · simpa only [step,hr] using hfold.2

abbrev laws : GuardedReplay.Laws (D α).toUpdateSig (conflict α) :=
  GuardedReplay.ofUniform restrictedLaws

def splitLaws : SplitPolicy.Laws (D α).toUpdateSig (conflict α) :=
  SplitPolicy.Laws.ofGuarded laws

noncomputable local instance : EventOrder (D α).toUpdateSig := (conflict α).lift

def representation : ConcreteMRDT.Representation (D α) := fun C E s =>
  IsCanonicalState C E s ∧ ConcreteMRDT.Supported C E

def scheme (C : ReplayContext (D α).toUpdateSig) :=
  ConcreteMRDT.MetadataDependencies.ofConcrete C

theorem canonical (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (s : State α) (h : representation C E s) :
    ConcreteMRDT.Canonical (conflict α) C E s := by
  obtain ⟨π,hp,hr,hf⟩ := h.1
  refine ⟨π,hp,hr.imp (fun {_ _} h edge =>
    h ((paperOrder_iff_loOn restrictedLaws C E _ _).mp edge)),hf⟩

theorem unique : ConcreteMRDT.Raw.Unique (representation (α := α)) := by
  intro C E s t hs ht
  exact ConcreteMRDT.canonical_unique laws C E hs.2
    (canonical C E s hs) (canonical C E t ht)

theorem initial_rep (C : ReplayContext (D α).toUpdateSig) :
    representation C ∅ (D α).init := by
  refine ⟨⟨[],⟨List.nodup_nil,by simp⟩,by simp [respects],rfl⟩,?_⟩
  simp [ConcreteMRDT.Supported]

theorem finite (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α)))
    (s : State α) (h : representation C E s) : ∃ π, listPermOf π E := by
  obtain ⟨π,hp,_,_⟩ := h.1
  exact ⟨π,hp⟩

theorem joint_maximal (C : ReplayContext (D α).toUpdateSig) (E : Set (Op (Update α)))
    (s : State α) (rep : representation C E s) (nonempty : E.Nonempty) :
    ∃ e ∈ E,
      (∀ x ∈ E, x ≠ e → ¬ paperOrder (conflict α) C E e x) ∧
      (∀ x ∈ E, x ≠ e → ¬ (scheme C).before e x) := by
  obtain ⟨π,hp,hr,_⟩ := rep.1
  have ordered : respects π (paperOrder (conflict α) C E) :=
    hr.imp (fun {_ _} h edge => h ((paperOrder_iff_loOn restrictedLaws C E _ _).mp edge))
  have metadata : respects π (scheme C).before := by
    apply hr.imp
    intro a b h edge
    exact h ((paperOrder_iff_loOn restrictedLaws C E b a).mp (Or.inl edge))
  exact ConcreteMRDT.joint_maximal_of_enumeration π hp nonempty ordered metadata

private theorem raw_maximal (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Op (Update α))) (e : Op (Update α))
    (maximal : ∀ x ∈ E, x ≠ e → ¬ paperOrder (conflict α) C E e x) :
    ∀ x ∈ E, x ≠ e → ¬ loOn C E e x := by
  intro x hx ne edge
  exact maximal x hx ne ((paperOrder_iff_loOn restrictedLaws C E e x).mpr edge)

theorem peel_choice (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Op (Update α))) (s : State α)
    (rep : representation C U s) (nonempty : U.Nonempty)
    (supported : ConcreteMRDT.Supported C U) (closed : (scheme C).Closed U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    Nonempty (ConcreteMRDT.Raw.PeelChoice (conflict α)
      representation C (scheme C) U) := by
  let M := scheme C
  obtain ⟨e,he,semantic,metadata⟩ := joint_maximal C U s rep nonempty
  obtain ⟨π,hp,_,_⟩ := rep.1
  have pastSub : M.Past e ⊆ U := M.past_subset U e closed he
  obtain ⟨pre,hpre⟩ := ConcreteMRDT.enumeration_subset hp
    (show U \ {e} ⊆ U from fun _ h => h.1)
  obtain ⟨past,hpast⟩ := ConcreteMRDT.enumeration_subset hp
    (show M.Past e \ {e} ⊆ U from fun _ h => pastSub h.1)
  obtain ⟨a,ha⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
    (fun {_ _ _} h k => trans h k) irrefl hpre (fun x h => supported x h.1)
  obtain ⟨b,hb⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
    (fun {_ _ _} h k => trans h k) irrefl hpast (fun x h => supported x (pastSub h.1))
  refine ⟨⟨e,he,semantic,metadata,a,b,⟨ha,?_⟩,⟨hb,?_⟩,?_,?_⟩⟩
  · exact fun x hx => supported x hx.1
  · exact fun x hx => supported x (pastSub hx.1)
  · exact ⟨isCanonicalState_snoc (Or.inl rfl)
      (raw_maximal C _ e (M.past_semantic_maximal (conflict α) trans irrefl e)) hb,
      (fun x hx => supported x (pastSub hx))⟩
  · exact ⟨isCanonicalState_snoc he (raw_maximal C U e semantic) ha,supported⟩

theorem replaySupply (C : ReplayContext (D α).toUpdateSig)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x) :
    ConcreteMRDT.Raw.ReplaySupply (conflict α) representation (scheme (α := α)) C := by
  refine ⟨?_,?_⟩
  · intro E π perm supported
    obtain ⟨s,hs⟩ := isCanonicalState_exists_of_replayLaws restrictedLaws.replayLaws
      (fun {_ _ _} h k => trans h k) irrefl perm supported
    exact ⟨s,hs,supported⟩
  · intro E s rep sup nonempty closed
    exact peel_choice C E s rep nonempty sup closed trans irrefl

#print axioms splitLaws
#print axioms replaySupply
end Sal.MRDTs.Paper1.AddWinsPriorityQueue
