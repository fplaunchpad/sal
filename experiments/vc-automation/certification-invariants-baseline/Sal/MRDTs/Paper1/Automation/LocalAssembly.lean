import Sal.MRDTs.Paper1.Automation.LocalSingleton
import Sal.MRDTs.Paper1.Automation.LocalCoverage
import Sal.MRDTs.Paper1.ConcreteJoin
import Sal.MRDTs.Paper1.GuardedConvergence
import Sal.MRDTs.Paper1.GuardedOrder

/-! Assembly of the nested-local finite equations through two independent
replays. The causal-past chronology never has to align with the nested common /
opposite chronology. All induction hypotheses remain merge equations. -/
namespace Sal.MRDTs.Paper1.Automation.Signature
open Sal.MRDTs.Foundation

structure LocalKernels (D : Signature) : Prop where
  seed : D.local_empty_sides
  common : D.local_common_opposite
  opposite : D.local_opposite_fresh
  freshBase : D.fresh_base
  freshStep : D.fresh_step
  emptyPast : D.local_empty_past
  pastSingleton : D.local_past_singleton

theorem local_two_replays (D : Signature) (kernels : D.LocalKernels)
    (L O : Set (Op D.AppOp)) (subset : L ⊆ O) (e : Op D.AppOp)
    (nested past : List (Op D.AppOp))
    (freshE : ∀ q ∈ nested, D.distinct e q)
    (outside : ∀ h ∈ past, ∀ q ∈ nested, q ∈ O → q ∉ L → D.distinct q h) :
    D.LocalEquation (D.restrictedReplay nested L) (past.foldl D.step D.init)
      (D.restrictedReplay nested O) e := by
  have freshL := D.fresh_restrictedReplay kernels.freshBase kernels.freshStep
    nested L e freshE
  apply D.local_independent_past kernels.emptyPast kernels.pastSingleton
    _ _ e freshL past
  intro h member
  exact D.local_singleton_restrictedReplay kernels.seed kernels.common kernels.opposite
    kernels.freshBase kernels.freshStep L O subset e h nested freshE (outside h member)

end Sal.MRDTs.Paper1.Automation.Signature

namespace Sal.MRDTs.Paper1.Automation.LocalAssembly
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Paper1.ConcreteMRDT Classical

/-- Forget only the query fields. No semantic assumption is added. -/
def ofMRDT (D : MRDTSig) (order : Op D.AppOp → Op D.AppOp → RcRes) : Signature :=
  ⟨D.State,D.AppOp,D.init,D.update,D.merge,order⟩

private theorem supported_distinct {D : MRDTSig}
    (C : ReplayContext D.toUpdateSig) (a b : Op D.AppOp)
    (ha : a ∈ C.events) (hb : b ∈ C.events) (ne : a ≠ b) : a.1 ≠ b.1 := by
  obtain ⟨r,A,head,member⟩ := ha
  obtain ⟨s,B,other,mem⟩ := hb
  exact C.timestamps_distinct head member other mem ne

/-- Actual nested-local equality from indexed replay evidence. The only pending
coverage input is the nested L/O replay; the K replay is completely independent.
Timestamp guards follow from the real ReplayContext and index exclusions. -/
theorem local_of_indexed_replays (D : MRDTSig)
    (order : Op D.AppOp → Op D.AppOp → RcRes)
    (kernels : (ofMRDT D order).LocalKernels)
    (C : ReplayContext D.toUpdateSig) (L K O : Set (Op D.AppOp))
    (l B b : D.State) (e : Op D.AppOp)
    (subset : L ⊆ O) (coherent : K ∩ O ⊆ L)
    (supportO : Supported C O) (supportK : Supported C K)
    (supportE : e ∈ C.events) (absent : e ∉ O)
    (nested : List (Op D.AppOp)) (nestedPerm : listPermOf nested O)
    (commonReplay : (ofMRDT D order).restrictedReplay nested L = l)
    (otherReplay : applySeq D.toUpdateSig D.init nested = b)
    (past : List (Op D.AppOp)) (pastPerm : listPermOf past K)
    (pastReplay : applySeq D.toUpdateSig D.init past = B) :
    ∀ t, D.merge l (D.merge B t (D.update B e)) b =
      D.merge B (D.merge l t b) (D.update B e) := by
  have fullFilter : nested.filter (fun h => decide (h ∈ O)) = nested := by
    apply List.filter_eq_self.mpr
    intro h member
    exact decide_eq_true ((nestedPerm.2 h).mp member)
  have otherRestricted : (ofMRDT D order).restrictedReplay nested O = b := by
    simpa only [Signature.restrictedReplay,fullFilter,ofMRDT,applySeq] using otherReplay
  have equation := Signature.local_two_replays (ofMRDT D order) kernels
    L O subset e nested past
    (fun q hq => supported_distinct C e q supportE
      (supportO q ((nestedPerm.2 q).mp hq))
      (fun equal => absent (equal ▸ ((nestedPerm.2 q).mp hq))))
    (by
      intro h hh q hq qO qL
      apply supported_distinct C q h (supportO q qO)
        (supportK h ((pastPerm.2 h).mp hh))
      intro equal
      subst q
      exact qL (coherent ⟨(pastPerm.2 h).mp hh,qO⟩))
  have pastFold : past.foldl (ofMRDT D order).step (ofMRDT D order).init = B :=
    pastReplay
  rw [commonReplay,otherRestricted,pastFold] at equation
  exact equation

private theorem restricted_perm {α : Type} (π : List α) (L O : Set α)
    (perm : listPermOf π O) (subset : L ⊆ O) :
    listPermOf (π.filter (fun h => decide (h ∈ L))) L := by
  refine ⟨perm.1.filter _,?_⟩
  intro a
  simp only [List.mem_filter,decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨(perm.2 a).mpr (subset h),h⟩

/-- Canonical-representation adapter. Convergence is the generic update-only
replay theorem; neither merge correctness nor an implementation invariant is
used to identify states. The nested replay's existence is the precise remaining
order coverage fact supplied separately. -/
theorem local_of_canonical_nested (D : MRDTSig)
    (order : Op D.AppOp → Op D.AppOp → RcRes)
    (kernels : (ofMRDT D order).LocalKernels)
    (P : OperationPolicy D.AppOp) (laws : GuardedReplay.Laws D.toUpdateSig P)
    (C : ReplayContext D.toUpdateSig) (L K O : Set (Op D.AppOp))
    (l B b : D.State) (e : Op D.AppOp)
    (subset : L ⊆ O) (coherent : K ∩ O ⊆ L)
    (supportO : Supported C O) (supportK : Supported C K)
    (supportE : e ∈ C.events) (absent : e ∉ O)
    (commonRep : Canonical P C L l) (pastRep : Canonical P C K B)
    (otherRep : Canonical P C O b)
    (nested : ∃ π, listPermOf π O ∧ respects π (paperOrder P C O) ∧
      respects (π.filter (fun h => decide (h ∈ L))) (paperOrder P C L)) :
    ∀ t, D.merge l (D.merge B t (D.update B e)) b =
      D.merge B (D.merge l t b) (D.update B e) := by
  obtain ⟨π,perm,orderedO,orderedL⟩ := nested
  obtain ⟨πL,permL,orderL,replayL⟩ := commonRep
  obtain ⟨πO,permO,orderO,replayO⟩ := otherRep
  obtain ⟨πK,permK,orderK,replayK⟩ := pastRep
  have equalL := convergence_on_guarded laws D.init
    (fun x hx => supportO x (subset hx)) (restricted_perm π L O perm subset) permL
    orderedL orderL
  have equalO := convergence_on_guarded laws D.init supportO perm permO orderedO orderO
  have replayNestedO : applySeq D.toUpdateSig D.init π = b := equalO.trans replayO
  have replayNestedL : (ofMRDT D order).restrictedReplay π L = l :=
    equalL.trans replayL
  exact local_of_indexed_replays D order kernels C L K O l B b e subset coherent
    supportO supportK supportE absent π perm replayNestedL replayNestedO πK permK replayK

/-- Full order coverage: the nested scopes alone are jointly enumerated by
an acyclic combined scope-sensitive order. The independent past replay is
then assembled from singleton equations. No alignment premise remains. -/
theorem local_from_context (D : MRDTSig)
    (order : Op D.AppOp → Op D.AppOp → RcRes)
    (kernels : (ofMRDT D order).LocalKernels)
    (P : OperationPolicy D.AppOp) (laws : GuardedReplay.Laws D.toUpdateSig P)
    (noChain : ∀ x y z : Op D.AppOp,
      ¬ (P.before x.op y.op ∧ P.before y.op z.op))
    (scheme : ∀ C, MetadataDependencies C)
    (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp))
    (l B b : D.State) (e : Op D.AppOp)
    (ctx : Raw.Context P scheme C E₁ E₂ e) (member : e ∈ E₁) (absent : e ∉ E₂)
    (commonRep : Canonical P C (E₁ ∩ E₂) l)
    (pastRep : Canonical P C ((scheme C).Past e \ {e}) B)
    (otherRep : Canonical P C E₂ b) :
    ∀ t, D.merge l (D.merge B t (D.update B e)) b =
      D.merge B (D.merge l t b) (D.update B e) := by
  have pastSubset := (scheme C).past_subset E₁ e ctx.closed₁ member
  have closedCommon : ∀ x y, C.vis x y → ¬ D.toUpdateSig.commutes x y →
      y ∈ E₁ ∩ E₂ → x ∈ E₁ ∩ E₂ := by
    intro x y vis noncomm hy
    exact ⟨ctx.closed₁ x y ((scheme C).covers x y vis noncomm) hy.1,
      ctx.closed₂ x y ((scheme C).covers x y vis noncomm) hy.2⟩
  obtain ⟨π,perm,ordered,filteredPerm,filteredOrdered⟩ :=
    LocalCoverage.nested_enumeration P C (E₁ ∩ E₂) E₂ Set.inter_subset_right
      closedCommon ctx.trans ctx.irrefl noChain otherRep.choose otherRep.choose_spec.1
  exact local_of_canonical_nested D order kernels P laws C (E₁ ∩ E₂)
    ((scheme C).Past e \ {e}) E₂ l B b e Set.inter_subset_right
    (fun x hx => ⟨pastSubset hx.1.1,hx.2⟩) ctx.supported₂
    (fun x hx => ctx.supported₁ x (pastSubset hx.1)) (ctx.supported₁ e member)
    absent commonRep pastRep otherRep ⟨π,perm,ordered,filteredOrdered⟩

/-- The exact original Raw.local_redistribute field from replay-complete
representations. The extra reconstructed-side/smaller-union evidence remains
in the unchanged field signature and is not replaced by a Join assumption. -/
theorem raw_local_redistribute (D : MRDTSig)
    (order : Op D.AppOp → Op D.AppOp → RcRes)
    (kernels : (ofMRDT D order).LocalKernels)
    (P : OperationPolicy D.AppOp) (laws : GuardedReplay.Laws D.toUpdateSig P)
    (noChain : ∀ x y z : Op D.AppOp,
      ¬ (P.before x.op y.op ∧ P.before y.op z.op))
    (R : Representation D) (canonical : ∀ C E s, R C E s → Canonical P C E s)
    (scheme : ∀ C, MetadataDependencies C) :
    ∀ C E₁ E₂ l B t b e, Raw.Context P scheme C E₁ E₂ e → e ∈ E₁ → e ∉ E₂ →
      R C (E₁ ∩ E₂) l → R C ((scheme C).Past e \ {e}) B →
      R C (E₁ \ {e}) t → R C E₂ b → R C ((scheme C).Past e) (D.update B e) →
      R C E₁ (D.merge B t (D.update B e)) →
      R C ((E₁ ∪ E₂) \ {e}) (D.merge l t b) →
      D.merge l (D.merge B t (D.update B e)) b =
        D.merge B (D.merge l t b) (D.update B e) := by
  intro C E₁ E₂ l B t b e ctx member absent hl hB _ hb _ _ _
  exact local_from_context D order kernels P laws noChain scheme C E₁ E₂
    l B b e ctx member absent (canonical C _ _ hl) (canonical C _ _ hB)
    (canonical C _ _ hb) t

end Sal.MRDTs.Paper1.Automation.LocalAssembly
