import Sal.MRDTs.Paper1.ConcreteJoin

/-! Five-VC transport when only the query boundary changes. Operational
representations, issuers and metadata dependencies are preserved exactly. -/
namespace Sal.MRDTs.Paper1.Automation.QueryLift
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.MRDTs.Paper1.ConcreteMRDT

def withQuery (D : MRDTSig) (Q V : Type) (query : D.State → Q → V) : MRDTSig where
  State := D.State
  dec_state := D.dec_state
  init := D.init
  AppOp := D.AppOp
  dec_op := D.dec_op
  Query := Q
  Value := V
  update := D.update
  query := query
  merge := D.merge

def scheme (D : MRDTSig) (Q V : Type) (query : D.State → Q → V)
    (M : ∀C:ReplayContext D.toUpdateSig,@MetadataDependencies D C)
    (C : ReplayContext (withQuery D Q V query).toUpdateSig) :
    @MetadataDependencies (withQuery D Q V query) C where
  before := (M C).before
  causal a b h := (M C).causal a b h
  covers a b h nc := (M C).covers a b h nc

theorem transport (D : MRDTSig) (Q V : Type) (query : D.State → Q → V)
    (P : OperationPolicy D.AppOp) (R : Representation D)
    (M : ∀C,MetadataDependencies C) (vc : Raw.MergeVCs P R M) :
    @Raw.MergeVCs (withQuery D Q V query) P R (scheme D Q V query M) := by
  refine ⟨vc.merge_comm,vc.init,vc.causal_delta,?_,?_⟩
  · intro C E₁ E₂ l B t b e ctx
    exact vc.local_redistribute C E₁ E₂ l B t b e
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx
    exact vc.shared C E₁ E₂ t₀ t₁ t₂ B e
      ⟨ctx.trans,ctx.irrefl,ctx.supported₁,ctx.supported₂,ctx.closed₁,ctx.closed₂,ctx.semantic,ctx.metadata⟩
end Sal.MRDTs.Paper1.Automation.QueryLift
