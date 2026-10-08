import PolicyExpansionAutomation
import GenericPolicyExpansion
import GenericMaskCanonical
import Sal.MRDTs.Paper1.GuardedRawORSetReplay

/-! Efficient OR-set: explicit raw-definition annotations and finite operation
cases feed reusable equation templates. No old datatype VC or invariant proof. -/
namespace NeemExpansion.AutomatedEfficientORSet
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Instances.EfficientORSet
open ConcreteMRDT
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000

def signature : Signature := LocalAssembly.ofMRDT (D α) rc.order
attribute [local policy_expansion_simps] signature LocalAssembly.ofMRDT D update merge rc

 theorem diagonal (l a : State α) : merge l a l = a := by policy_finite
 theorem comm (l a b : State α) : merge l a b = merge l b a := by policy_finite
 theorem initial (s : State α) : (D α).merge (D α).init (D α).init s = s := by policy_finite

 theorem fresh_base : (signature (α := α)).fresh_base := by
  rintro ⟨t,r,op⟩; cases op <;> policy_finite
 theorem fresh_step : (signature (α := α)).fresh_step := by
  rintro s ⟨t,r,op⟩ ⟨u,q,other⟩ distinct previous
  cases op <;> cases other <;> policy_finite
 theorem local_common : (signature (α := α)).local_common_opposite := by
  rintro l B b ⟨t,r,op⟩ ⟨u,q,other⟩ previous s
  have base := previous (∅ : State α)
  cases op <;> cases other <;> policy_finite
 theorem local_opposite : (signature (α := α)).local_opposite_fresh := by
  rintro l B b ⟨t,r,op⟩ ⟨u,q,other⟩ freshE freshH previous s
  have base := previous (∅ : State α)
  cases op <;> cases other <;> policy_finite
 theorem local_empty : (signature (α := α)).local_empty_past := by
  rintro l b ⟨t,r,op⟩ fresh s
  cases op <;> policy_finite
 theorem local_singleton : (signature (α := α)).local_past_singleton := by
  rintro l B b ⟨t,r,op⟩ ⟨u,q,other⟩ fresh previous singleton s
  have base := previous (∅ : State α)
  have one := singleton (∅ : State α)
  cases op <;> cases other <;> policy_finite
 theorem causal_common : (signature (α := α)).causal_common_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ previous
  cases op <;> cases other <;> policy_finite
 theorem causal_commuting : (signature (α := α)).causal_commuting_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ commuting previous
  have commuteEmpty := commuting (∅ : State α)
  cases op <;> cases other <;> policy_finite
 theorem causal_strict : (signature (α := α)).causal_strict_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ fresh previous strict
  cases op <;> cases other <;> policy_finite
 theorem causal_absorber : (signature (α := α)).causal_absorber_kernel := by
  rintro B s ⟨t,r,op⟩ ⟨u,q,other⟩ ⟨v,z,last⟩ strict reset
  cases op <;> cases other <;> cases last <;> policy_finite

 def birth (p : Record α) : Event α := (p.2.1,p.1,.add p.2.2)
 theorem mask_update : InductiveMask.UpdateCertificate (update (α := α))
     (fun p e => e = birth p) (fun p e => kills p.1 p.2.2 e) := by
  constructor
  rintro s ⟨t,r,op⟩ ⟨pr,pt,px⟩
  cases op <;> simp [update,birth,kills,Prod.mk.injEq] <;> grind only
 theorem mask_commuting (p : Record α) (e : Event α)
     (no : ¬kills p.1 p.2.2 e) : (D α).toUpdateSig.commutes (birth p) e := by
  intro s
  rcases p with ⟨pr,pt,px⟩; rcases e with ⟨t,r,op⟩
  dsimp [D]
  cases op <;> ext q <;> simp [D,update,birth,kills] at * <;> grind only
 theorem mask_noncomm (p : Record α) (e : Event α)
     (different : (birth p).time ≠ e.time) (kill : kills p.1 p.2.2 e) :
     ¬ (D α).toUpdateSig.commutes (birth p) e := by
  intro hc
  have witness := hc (∅ : State α)
  rcases p with ⟨pr,pt,px⟩; rcases e with ⟨t,r,op⟩
  cases op <;> simp_all [kills,D,update,birth,Op.time]
  have member := Finset.ext_iff.mp witness (pr,pt,px)
  simp [different] at member

 def maskKit : MaskCanonical.Kit (D α) (EfficientORSet.EventSpec.conflict α) (Record α) where
  carrier := id
  step := update
  birth := birth
  kill := fun p e => kills p.1 p.2.2 e
  injective := by simp [Function.Injective]
  empty := rfl
  projection := by intros; rfl
  update := mask_update
  commutes_notkill := mask_commuting
  noncomm_kill := mask_noncomm
  killer_shape := by
    rintro ⟨pr,pt,px⟩ ⟨t,r,op⟩ kill
    cases op <;> simp_all [kills,birth,EfficientORSet.EventSpec.conflict,Op.op,Op.rep]

 theorem semantic_shape (C : ReplayContext (D α).toUpdateSig) (H : Set (Event α)) (s : State α)
     (rep : EfficientORSet.RawReplay.representation C H s) :
     MaskCanonical.Shape (maskKit (α := α)) C H s := by
  refine ⟨rep.2.1,rep.2.2.1,rep.2.2.2.1,?_,?_⟩
  · intro e self; exact Nat.lt_irrefl _ (rep.2.2.2.2 e e self)
  · intro p
    change p ∈ s ↔ _
    rw [rep.1 p]
    simp only [MaskCanonical.Shape,maskKit,InductiveMask.Alive,birth,live,dead]
    constructor
    · rintro ⟨member,alive⟩
      exact ⟨(p.2.1,p.1,.add p.2.2),member,rfl,alive⟩
    · rintro ⟨b,member,rfl,alive⟩
      exact ⟨member,alive⟩

def element : SetOp α → α
  | .add x | .remove x => x

theorem commute_distinct_elements (a b : Op (SetOp α))
    (ne : element a.2.2 ≠ element b.2.2) : (D α).toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> dsimp [D] <;> ext p <;> simp [D,update,element] at * <;> grind

theorem conflict_classification (a b : Op (SetOp α))
    (nc : ¬ (D α).toUpdateSig.commutes a b) :
    rc.order a b = .Fst_then_snd ∨ rc.order b a = .Fst_then_snd ∨ a.rep = b.rep := by
  by_contra hn
  apply nc
  intro s
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> dsimp [D] <;> ext p <;> simp [D,update,rc,Op.rep] at * <;> grind

theorem remove_add_noncomm (et er ct cr : Nat) (x : α) :
    ¬ (D α).toUpdateSig.commutes (et,er,.remove x) (ct,cr,.add x) := by
  intro hc
  have h := hc (∅ : State α)
  have hp := Finset.ext_iff.mp h (cr,ct,x)
  simp [D,update] at hp

theorem absorber_classification (e h c : Op (SetOp α))
    (prior : rc.order e h = .Fst_then_snd)
    (nc : ¬ (D α).toUpdateSig.commutes h c) :
    rc.order c h = .Fst_then_snd ∨
      (rc.order e c = .Fst_then_snd ∧ ¬ (D α).toUpdateSig.commutes e c) := by
  rcases e with ⟨et,er,eo⟩; rcases h with ⟨ht,hr,ho⟩; rcases c with ⟨ct,cr,co⟩
  cases eo <;> cases ho <;> simp [rc,ite_eq_iff] at prior
  rename_i x y
  subst y
  cases co with
  | add z =>
    by_cases eq : x = z
    · subst z
      exact Or.inr ⟨by simp [rc],remove_add_noncomm et er ct cr x⟩
    · exact False.elim (nc (commute_distinct_elements _ _ eq))
  | remove z =>
    by_cases eq : z = x
    · subst z; exact Or.inl (by simp [rc])
    · exact False.elim (nc (commute_distinct_elements _ _ (Ne.symm eq)))

theorem strict_asymmetric (a b : Op (SetOp α)) (prior : rc.order a b = .Fst_then_snd) :
    rc.order b a ≠ .Fst_then_snd := by
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> simp_all [rc,ite_eq_iff]

attribute [local policy_expansion_simps] EfficientORSet.EventSpec.conflict Op.op Op.rep
theorem policy_order (a b : Op (SetOp α)) :
    rc.order a b = .Fst_then_snd ↔ (EfficientORSet.EventSpec.conflict α).before a.op b.op := by
  rcases a with ⟨t,r,op⟩; rcases b with ⟨u,q,other⟩
  cases op <;> cases other <;> simp [rc,EfficientORSet.EventSpec.conflict,Op.op,ite_eq_iff]
  exact eq_comm
omit [DecidableEq α] in
theorem no_chain (a b c : Op (SetOp α)) :
    ¬ ((EfficientORSet.EventSpec.conflict α).before a.op b.op ∧ (EfficientORSet.EventSpec.conflict α).before b.op c.op) := by
  rcases a with ⟨t,r,op⟩; rcases b with ⟨u,q,other⟩; rcases c with ⟨v,z,last⟩
  cases op <;> cases other <;> cases last <;> simp [EfficientORSet.EventSpec.conflict,Op.op]
theorem commute_nonconflict (a b : Op (SetOp α))
    (absent : ¬ ((EfficientORSet.EventSpec.conflict α).before a.op b.op ∨ (EfficientORSet.EventSpec.conflict α).before b.op a.op))
    (ne : a.rep ≠ b.rep) : (D α).toUpdateSig.commutes a b := by
  intro s
  rcases a with ⟨t,r,op⟩; rcases b with ⟨u,q,other⟩
  cases op <;> cases other <;> policy_finite

theorem guarded_noncomm (a b : Event α) (ne : a.rep ≠ b.rep) :
    ¬ (D α).toUpdateSig.commutes a b ↔
      (EfficientORSet.EventSpec.conflict α).before a.op b.op ∨ (EfficientORSet.EventSpec.conflict α).before b.op a.op := by
  constructor
  · intro nc; by_contra absent; exact nc (commute_nonconflict a b absent ne)
  · intro clash commute
    rcases clash with ⟨x,ha,hb⟩ | ⟨x,hb,ha⟩
    all_goals simp only [Op.op] at ha hb
    · have hp := Finset.ext_iff.mp (commute (∅ : State α)) (b.rep,b.time,x)
      simp [D,update,ha,hb,Op.rep,Op.time] at hp
    · have hp := Finset.ext_iff.mp (commute (∅ : State α)) (a.rep,a.time,x)
      simp [D,update,ha,hb,Op.rep,Op.time] at hp

theorem conditional_base : (signature (α := α)).ConditionalBase := by
  intro s a b c before noncomm
  dsimp [Signature.commutes, signature,LocalAssembly.ofMRDT,D] at *
  rcases a with ⟨ats, ar, ao⟩; rcases b with ⟨bt, br, bo⟩
  rcases c with ⟨ct, cr, co⟩
  cases ao <;> cases bo <;> simp only [rc] at before
  all_goals try split_ifs at before
  all_goals try cases before
  subst_vars
  rename_i x
  cases co with
  | add z =>
    have same : br = cr ∧ x = z := by
      by_contra ne
      apply noncomm
      intro t
      ext p
      simp [signature,LocalAssembly.ofMRDT,D, update]
      grind only
    rcases same with ⟨rfl, rfl⟩
    ext p
    simp [signature,LocalAssembly.ofMRDT,D, update]
    grind only
  | remove z =>
    have same : x = z := by
      by_contra ne
      apply noncomm
      intro t
      ext p
      simp [signature,LocalAssembly.ofMRDT,D, update]
      grind only
    subst z
    ext p
    simp [signature,LocalAssembly.ofMRDT,D, update]
    grind only


theorem kernel_stable : (signature (α := α)).KernelStable := by
  rintro s t ⟨u,q,op⟩ ⟨v,z,other⟩ previous
  cases op <;> cases other <;> policy_finite

def kit : PolicyExpansion.Kit (D α) (EfficientORSet.EventSpec.conflict α) rc.order where
  comm := comm
  initial := initial
  shared := fun t₀ t₁ t₂ B e => collection_shared t₀ t₁ t₂ B ((D α).update B e)
  localKernels := ⟨Signature.local_empty_sides_of_diagonal signature diagonal,
    local_common,local_opposite,fresh_base,fresh_step,local_empty,local_singleton⟩
  causalKernels := ⟨Signature.causal_base_of_diagonal signature comm diagonal,
    causal_common,causal_commuting,causal_strict,causal_absorber,fresh_base,fresh_step⟩
  eventCertificate := ⟨conflict_classification,absorber_classification,strict_asymmetric⟩
  noncomm_exact := fun a b _ ne => guarded_noncomm a b ne
  noChain := no_chain
  policy_order := policy_order
  conditionalBase := conditional_base
  kernelStable := kernel_stable

theorem automated_vcs : Raw.MergeVCs (EfficientORSet.EventSpec.conflict α)
    (EfficientORSet.RawReplay.representation (α := α)) (EfficientORSet.RawReplay.scheme (α := α)) :=
  PolicyExpansion.assemble kit EfficientORSet.RawReplay.representation
    (fun C H s rep => MaskCanonical.canonical maskKit (PolicyExpansion.laws kit) C H s (semantic_shape C H s rep))
    EfficientORSet.RawReplay.scheme
#print axioms automated_vcs
end NeemExpansion.AutomatedEfficientORSet
