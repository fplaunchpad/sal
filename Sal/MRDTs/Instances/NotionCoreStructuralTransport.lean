import Sal.MRDTs.Instances.NotionCoreStructuralVC
import Sal.MRDTs.Instances.NotionCoreMRDT

/-! Exact update/merge transport from the reference transaction carrier to
structural facts. This is a noninjective homomorphism, not a query-correctness
assumption or an inverse embedding. Rendering is proved separately. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralTransport
open Sal.MRDTs.Foundation
open NotionCorePayload (Transaction)
open NotionCoreStructuralFacts (State decode ofTransactions)

def project (archive : Finset Transaction) : State := archive.biUnion decode

@[simp] theorem mem_project (archive : Finset Transaction) (fact) :
    fact ∈ project archive ↔ ∃ tx ∈ archive, fact ∈ decode tx := by
  simp [project]

@[simp] theorem project_empty : project ∅ = ∅ := by simp [project]

@[simp] theorem project_insert (archive : Finset Transaction) (tx : Transaction) :
    project (insert tx archive) = project archive ∪ decode tx := by
  ext fact
  simp only [mem_project, Finset.mem_insert, Finset.mem_union]
  aesop

@[simp] theorem project_union (left right : Finset Transaction) :
    project (left ∪ right) = project left ∪ project right := by
  ext fact
  simp only [mem_project, Finset.mem_union]
  aesop

theorem project_list (txs : List Transaction) :
    project txs.toFinset = ofTransactions txs := by
  induction txs with
  | nil => simp
  | cons tx txs ih => simp [ih, Finset.union_comm]

theorem update_commutes {Q V : Type} (query : State → Q → V)
    (archive : Finset Transaction) (event : Op Transaction) :
    project (NotionCoreMRDT.D.update archive event) =
      (NotionCoreStructuralVC.D query).update (project archive) event := by
  exact project_insert archive event.op

theorem merge_commutes {Q V : Type} (query : State → Q → V)
    (base left right : Finset Transaction) :
    project (NotionCoreMRDT.D.merge base left right) =
      (NotionCoreStructuralVC.D query).merge (project base) (project left) (project right) := by
  exact project_union left right

#print axioms update_commutes
#print axioms merge_commutes
end Sal.MRDTs.Instances.NotionCoreStructuralTransport
