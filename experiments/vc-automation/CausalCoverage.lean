import CausalExpansion
import LocalAssembly
import CausalEventClassification
import ExpandedPolicy
import Sal.MRDTs.Paper1.ConcreteJoin

/-! Source-context coverage of the last-bad-event causal expansion. The only
datatype input is a finite event-classification certificate, not a represented
state invariant or an existing VC proof. -/
namespace NeemExpansion.CausalCoverage
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT Classical

def signatureOf (D : MRDTSig) (order : Op D.AppOp → Op D.AppOp → RcRes) : Signature :=
  ⟨D.State,D.AppOp,D.init,D.update,D.merge,order⟩

structure EventCertificate (D : MRDTSig) (order : Op D.AppOp → Op D.AppOp → RcRes) : Prop where
  conflict_classification : ∀ a b, ¬ D.toUpdateSig.commutes a b →
    order a b = .Fst_then_snd ∨ order b a = .Fst_then_snd ∨ a.rep = b.rep
  absorber_classification : ∀ e h c, order e h = .Fst_then_snd →
    ¬ D.toUpdateSig.commutes h c →
    order c h = .Fst_then_snd ∨
      (order e c = .Fst_then_snd ∧ ¬ D.toUpdateSig.commutes e c)
  strict_asymmetric : ∀ a b, order a b = .Fst_then_snd → order b a ≠ .Fst_then_snd

structure Kernels (D : Signature) : Prop where
  base : ∀ e, D.CausalEquation D.init D.init e
  common : D.causal_common_kernel
  commuting : D.causal_commuting_kernel
  strict : D.causal_strict_kernel
  absorber : D.causal_absorber_kernel
  freshBase : D.fresh_base
  freshStep : D.fresh_step

theorem reset_of_context
    (D : MRDTSig) (order : Op D.AppOp → Op D.AppOp → RcRes)
    (certificate : EventCertificate D order) (P : OperationPolicy D.AppOp)
    (policy : ∀ a b, order a b = .Fst_then_snd ↔ P.before a.op b.op)
    (C : ReplayContext D.toUpdateSig) (M : MetadataDependencies C)
    (U : Set (Op D.AppOp)) (e : Op D.AppOp) (member : e ∈ U)
    (supported : Supported C U) (irrefl : ∀ x, ¬ C.vis x x)
    (semantic : ∀ x ∈ U, x ≠ e → ¬ paperOrder P C U e x)
    (metadata : ∀ x ∈ U, x ≠ e → ¬ M.before e x)
    (π : List (Op D.AppOp)) (perm : listPermOf π (U \ {e}))
    (ordered : respects π (paperOrder P C (U \ {e}))) :
    ∀ pre h post, π = pre ++ h :: post →
      (signatureOf D order).Bad (M.Past e \ {e}) (U \ {e}) e h →
      (∀ q ∈ post, ¬ (signatureOf D order).Bad (M.Past e \ {e}) (U \ {e}) e q) →
      ∃ mid c tail, post = mid ++ c :: tail ∧ c ∈ U \ {e} ∧ c ∉ M.Past e \ {e} ∧
        order e h = .Fst_then_snd ∧ order c h = .Fst_then_snd := by
  intro pre h post partition bad clean
  have hU : h ∈ U := bad.1.1
  have hne : h ≠ e := bad.1.2
  have nc : ¬ D.toUpdateSig.commutes e h := fun commute => bad.2.2 (Or.inl commute)
  have noForward : ¬ C.vis e h := by
    intro vis
    apply metadata h hU hne
    apply M.covers e h vis
    exact nc
  have noBackward : ¬ C.vis h e := by
    intro vis
    apply bad.2.1
    exact ⟨Or.inr (.single (M.covers h e vis
      (fun commute => nc (Sal.MRDTs.Foundation.commutes_symm commute)))),hne⟩
  have eh : order e h = .Fst_then_snd := by
    rcases certificate.conflict_classification e h nc with eh | he | same
    · exact eh
    · exact False.elim (bad.2.2 (Or.inr he))
    · obtain ⟨r,E,hr,he⟩ := supported e member
      obtain ⟨q,F,hq,hh⟩ := supported h hU
      rcases C.vis_total_same_replica hr he hq hh hne.symm same with forward | backward
      · exact False.elim (noForward forward)
      · exact False.elim (noBackward backward)
  have witness : ∃ c ∈ U, C.vis h c ∧ ¬ D.toUpdateSig.commutes h c := by
    by_contra absent
    apply semantic h hU hne
    exact Or.inr ⟨noForward,noBackward,(policy e h).mp eh,absent⟩
  obtain ⟨c,cU,hcvis,hcnc⟩ := witness
  have cne : c ≠ e := fun equal => noBackward (equal ▸ hcvis)
  have cS : c ∈ U \ {e} := ⟨cU,cne⟩
  have cB : c ∉ M.Past e \ {e} := by
    intro past
    exact bad.2.1 ⟨M.past_closed e h c (M.covers h c hcvis hcnc) past.1,hne⟩
  have after : c ∈ post := by
    have mem := (perm.2 c).mpr cS
    rw [partition] at mem ordered
    rcases List.mem_append.mp mem with before | rest
    · exact False.elim ((List.pairwise_append.mp ordered).2.2 c before h (by simp)
        (Or.inl ⟨hcvis,hcnc⟩))
    · rcases List.mem_cons.mp rest with equal | after
      · exact False.elim (irrefl h (equal ▸ hcvis))
      · exact after
  have ch : order c h = .Fst_then_snd := by
    rcases certificate.absorber_classification e h c eh hcnc with reset | ⟨ec,nc⟩
    · exact reset
    · apply False.elim
      apply clean c after
      refine ⟨cS,cB,?_⟩
      rintro (commute | ce)
      · exact nc commute
      · exact certificate.strict_asymmetric e c ec ce
  obtain ⟨mid,tail,eq⟩ := List.append_of_mem after
  exact ⟨mid,c,tail,eq,cS,cB,eh,ch⟩

/-- All source-context obligations have now been discharged. The nested past /
remainder replay comes from the generic order theorem; canonical convergence
identifies its states. The proof then invokes the last-bad equation induction. -/
theorem causal_from_context
    (D : MRDTSig) (order : Op D.AppOp → Op D.AppOp → RcRes)
    (certificate : EventCertificate D order) (kernels : Kernels (signatureOf D order))
    (P : OperationPolicy D.AppOp) (laws : GuardedReplay.Laws D.toUpdateSig P)
    (policy : ∀ a b, order a b = .Fst_then_snd ↔ P.before a.op b.op)
    (noChain : ∀ a b c : Op D.AppOp, ¬ (P.before a.op b.op ∧ P.before b.op c.op))
    (C : ReplayContext D.toUpdateSig) (M : MetadataDependencies C)
    (U : Set (Op D.AppOp)) (s B : D.State) (e : Op D.AppOp)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : M.Closed U) (member : e ∈ U)
    (semantic : ∀ x ∈ U, x ≠ e → ¬ paperOrder P C U e x)
    (metadata : ∀ x ∈ U, x ≠ e → ¬ M.before e x)
    (sRep : Canonical P C (U \ {e}) s)
    (bRep : Canonical P C (M.Past e \ {e}) B) :
    D.merge B s (D.update B e) = D.update s e := by
  let K := M.Past e \ {e}
  let S := U \ {e}
  have pastSubset := M.past_subset U e closed member
  have subset : K ⊆ S := fun x hx => ⟨pastSubset hx.1,hx.2⟩
  have closedK : M.Closed K :=
    M.closed_diff_of_max U (M.Past e) e pastSubset (M.past_closed e) metadata
  obtain ⟨oldS,permS,orderedS,replayS⟩ := sRep
  obtain ⟨oldB,permB,orderedB,replayB⟩ := bRep
  obtain ⟨π,perm,ordered,filteredPerm,filteredOrdered⟩ :=
    LocalCoverage.nested_enumeration P C K S subset
      (fun a b vis nc hb => closedK a b (M.covers a b vis nc) hb)
      trans irrefl noChain oldS permS
  have supportS : Supported C S := fun x hx => supported x hx.1
  have supportK : Supported C K := fun x hx => supportS x (subset hx)
  have newS := (convergence_on_guarded laws D.init supportS perm permS ordered orderedS).trans replayS
  have newB := (convergence_on_guarded laws D.init supportK filteredPerm permB
    filteredOrdered orderedB).trans replayB
  have restrictedS : (signatureOf D order).restrictedReplay π S = s := by
    calc
      _ = π.foldl D.update D.init := by
        unfold Signature.restrictedReplay signatureOf
        apply congrArg (List.foldl D.update D.init)
        apply List.filter_eq_self.mpr
        intro h hh
        exact @decide_eq_true (h ∈ S) (Classical.propDecidable (h ∈ S)) ((perm.2 h).mp hh)
      _ = s := newS
  have restrictedB : (signatureOf D order).restrictedReplay π K = B := newB
  have fresh : ∀ h ∈ π, (signatureOf D order).distinct e h := by
    intro h hh
    have hs := (perm.2 h).mp hh
    obtain ⟨r,A,head,mem⟩ := supported e member
    obtain ⟨q,F,other,mem'⟩ := supported h hs.1
    exact C.timestamps_distinct head mem other mem'
      (fun equal => hs.2 (Set.mem_singleton_iff.mpr equal.symm))
  have reset := reset_of_context D order certificate P policy C M U e member supported
    irrefl semantic metadata π perm ordered
  have equation := (signatureOf D order).causal_restrictedReplay kernels.base kernels.common
    kernels.commuting kernels.strict kernels.absorber kernels.freshBase kernels.freshStep
    K S subset e π fresh reset
  rw [restrictedS,restrictedB] at equation
  exact equation

/-- The unchanged original Raw.causal_delta field, including both reconstructed
representation premises. No merge/Join premise is added. -/
theorem raw_causal_delta
    (D : MRDTSig) (order : Op D.AppOp → Op D.AppOp → RcRes)
    (certificate : EventCertificate D order) (kernels : Kernels (signatureOf D order))
    (P : OperationPolicy D.AppOp) (laws : GuardedReplay.Laws D.toUpdateSig P)
    (policy : ∀ a b, order a b = .Fst_then_snd ↔ P.before a.op b.op)
    (noChain : ∀ a b c : Op D.AppOp, ¬ (P.before a.op b.op ∧ P.before b.op c.op))
    (R : Representation D) (canonical : ∀ C E s, R C E s → Canonical P C E s)
    (scheme : ∀ C, MetadataDependencies C) :
    ∀ C U s B e, Transitive C.vis → (∀ x, ¬ C.vis x x) → Supported C U →
      (scheme C).Closed U → e ∈ U →
      (∀ x ∈ U, x ≠ e → ¬ paperOrder P C U e x) →
      (∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x) →
      R C (U \ {e}) s → R C ((scheme C).Past e \ {e}) B →
      R C ((scheme C).Past e) (D.update B e) → R C U (D.update s e) →
      D.merge B s (D.update B e) = D.update s e := by
  intro C U s B e trans irrefl supported closed member semantic metadata hs hB _ _
  exact causal_from_context D order certificate kernels P laws policy noChain C (scheme C)
    U s B e trans irrefl supported closed member semantic metadata
    (canonical C _ _ hs) (canonical C _ _ hB)

#print axioms reset_of_context
#print axioms raw_causal_delta
end NeemExpansion.CausalCoverage

namespace NeemExpansion.Exact
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
variable {α : Type} [DecidableEq α]

theorem causal_event_certificate : CausalCoverage.EventCertificate (ORSet.D α) ORSet.order :=
  ⟨CausalEventClassification.Exact.conflict_classification,
    CausalEventClassification.Exact.absorber_classification,
    CausalEventClassification.Exact.strict_asymmetric⟩

theorem causal_kernels : CausalCoverage.Kernels (signature (α := α)) :=
  ⟨Signature.causal_base_of_diagonal _ comm diagonal,causal_common_kernel,
    causal_commuting_kernel,causal_strict_kernel,causal_absorber_kernel,fresh_base,fresh_step⟩

theorem policy_order (a b : Op (ORSet.Update α)) :
    ORSet.order a b = .Fst_then_snd ↔ (ORSet.conflict α).before a.op b.op := by
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> simp [ORSet.order,ORSet.conflict,Op.op,ite_eq_iff]
  exact eq_comm

theorem raw_causal :
    ∀ C U s B e, Transitive C.vis → (∀ x, ¬ C.vis x x) → Supported C U →
      (MetadataDependencies.ofConcrete C).Closed U → e ∈ U →
      (∀ x ∈ U, x ≠ e → ¬ paperOrder (ORSet.conflict α) C U e x) →
      (∀ x ∈ U, x ≠ e → ¬ (MetadataDependencies.ofConcrete C).before e x) →
      rawRepresentation C (U \ {e}) s →
      rawRepresentation C ((MetadataDependencies.ofConcrete C).Past e \ {e}) B →
      rawRepresentation C ((MetadataDependencies.ofConcrete C).Past e) ((ORSet.D α).update B e) →
      rawRepresentation C U ((ORSet.D α).update s e) →
      (ORSet.D α).merge B s ((ORSet.D α).update B e) = (ORSet.D α).update s e :=
  CausalCoverage.raw_causal_delta (ORSet.D α) ORSet.order causal_event_certificate causal_kernels
    (ORSet.conflict α) expandedLaws policy_order
    no_chain
    rawRepresentation (fun C E s rep => representation_canonical C E s rep.1)
    (fun C => MetadataDependencies.ofConcrete C)
end NeemExpansion.Exact

namespace NeemExpansion.Efficient
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT
open Sal.MRDTs.Instances.EfficientORSet
variable {α : Type} [DecidableEq α]

theorem causal_event_certificate : CausalCoverage.EventCertificate (D α) rc.order :=
  ⟨CausalEventClassification.Efficient.conflict_classification,
    CausalEventClassification.Efficient.absorber_classification,
    CausalEventClassification.Efficient.strict_asymmetric⟩

theorem causal_kernels : CausalCoverage.Kernels (signature (α := α)) :=
  ⟨Signature.causal_base_of_diagonal _ comm diagonal,causal_common_kernel,
    causal_commuting_kernel,causal_strict_kernel,causal_absorber_kernel,fresh_base,fresh_step⟩

theorem policy_order (a b : Event α) :
    rc.order a b = .Fst_then_snd ↔ (EfficientORSet.EventSpec.conflict α).before a.op b.op := by
  rcases a with ⟨atime,ar,ao⟩; rcases b with ⟨bt,br,bo⟩
  cases ao <;> cases bo <;> simp [rc,EfficientORSet.EventSpec.conflict,Op.op,ite_eq_iff]
  exact eq_comm

theorem raw_causal :
    ∀ C U s B e, Transitive C.vis → (∀ x, ¬ C.vis x x) → Supported C U →
      (MetadataDependencies.ofConcrete C).Closed U → e ∈ U →
      (∀ x ∈ U, x ≠ e → ¬ paperOrder (EfficientORSet.EventSpec.conflict α) C U e x) →
      (∀ x ∈ U, x ≠ e → ¬ (MetadataDependencies.ofConcrete C).before e x) →
      EfficientORSet.ConcreteRep.representation C (U \ {e}) s →
      EfficientORSet.ConcreteRep.representation C ((MetadataDependencies.ofConcrete C).Past e \ {e}) B →
      EfficientORSet.ConcreteRep.representation C ((MetadataDependencies.ofConcrete C).Past e) ((D α).update B e) →
      EfficientORSet.ConcreteRep.representation C U ((D α).update s e) →
      (D α).merge B s ((D α).update B e) = (D α).update s e :=
  CausalCoverage.raw_causal_delta (D α) rc.order causal_event_certificate causal_kernels
    (EfficientORSet.EventSpec.conflict α) expandedLaws policy_order
    (fun x y z => EfficientORSet.EventSpec.no_chain x.op y.op z.op)
    EfficientORSet.ConcreteRep.representation EfficientReplayAdapter.representation_canonical
    (fun C => MetadataDependencies.ofConcrete C)
end NeemExpansion.Efficient

#print axioms NeemExpansion.Exact.raw_causal
#print axioms NeemExpansion.Efficient.raw_causal
