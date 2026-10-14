import Sal.MRDTs.Instances.NotionCoreMRDT
import Sal.MRDTs.Instances.NotionCoreMachineHistory

/-! One-archive finite-carrier query/history correspondence. The selected
version is explicit and closed; external event labels are supplied separately.
No claim that arbitrary Sal execution maintains this coupling is made here. -/
namespace Sal.MRDTs.Instances.NotionCoreMRDTArchive
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open NotionCorePayload (Transaction reservation)
open NotionCorePayloadNetwork (State Entry)
open NotionCoreHistory (View)

local instance : Std.Total NotionCoreReconstruction.Ascending where
  total a b := by
    rcases NotionCoreSourceInvariant.before_trichotomy a.id b.id with before | same | reverse
    · exact Or.inl (Or.inl before)
    · exact Or.inl (Or.inr same.symm)
    · exact Or.inr (Or.inl reverse)

local instance : IsTrans Transaction NotionCoreReconstruction.Ascending where
  trans a b c ab bc :=
    (inferInstance : IsTrans NotionRunAllocation.Id NotionCoreSourceInvariant.Desc).trans
      c.id b.id a.id bc ab

/-- Finite image of the archived transactions selected by the version. Sorting
affects the enumeration, not which whole transaction values are stored. -/
noncomputable def carrierFor (network : State) (version : List NotionRunAllocation.Run) : Finset Transaction :=
  (NotionCoreReconstruction.transactionsFor network version).toFinset

theorem carrierFor_membership (network : State) (version : List NotionRunAllocation.Run) (tx : Transaction) :
    tx ∈ carrierFor network version ↔
      (∃ entry ∈ network.entries, entry.tx = tx) ∧ reservation tx ∈ version := by
  simp only [carrierFor,List.mem_toFinset]
  exact NotionCoreReconstruction.transactionsFor_membership network version tx

/-- Finite-store enumeration followed by the literal source sort recovers
exactly the archive's canonical transaction sequence. ID uniqueness removes
any dependence on the arbitrary Finset enumeration. -/
theorem transactions_carrierFor (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (version : List NotionRunAllocation.Run) :
    NotionCoreMRDT.transactions (carrierFor network version) =
      NotionCoreReconstruction.transactionsFor network version := by
  let canonical := NotionCoreReconstruction.transactionsFor network version
  have canonicalOrdered := NotionCoreReconstruction.transactionsFor_ordered network reachable version
  have canonicalIds : (canonical.map Transaction.id).Nodup := by
    apply List.pairwise_map.mpr
    apply canonicalOrdered.imp
    intro a b before same
    rw [same] at before
    exact NotionCoreSourceInvariant.before_asymm before before
  have canonicalUnique : canonical.Nodup := by
    apply canonicalOrdered.imp
    intro a b before same
    subst b
    exact NotionCoreSourceInvariant.before_asymm before before
  have enumeration : (carrierFor network version).toList.Perm canonical :=
    List.toFinset_toList canonicalUnique
  have permutation : (NotionCoreMRDT.transactions (carrierFor network version)).Perm canonical :=
    (List.mergeSort_perm _ _).trans enumeration
  have actualIds : ((NotionCoreMRDT.transactions (carrierFor network version)).map Transaction.id).Nodup :=
    (permutation.map Transaction.id).nodup_iff.mpr canonicalIds
  have actualSorted : (NotionCoreMRDT.transactions (carrierFor network version)).Pairwise
      NotionCoreReconstruction.Ascending :=
    List.pairwise_mergeSort' NotionCoreReconstruction.Ascending _
  have actualOrdered : (NotionCoreMRDT.transactions (carrierFor network version)).Pairwise
      (fun a b => NotionRunAllocation.Before a.id b.id) := by
    apply (actualSorted.and (List.pairwise_map.mp actualIds)).imp
    intro a b both
    rcases both.1 with before | equal
    · exact before
    · exact False.elim (both.2 equal.symm)
  exact permutation.eq_of_pairwise (fun _ _ _ _ forward reverse =>
    False.elim (NotionCoreSourceInvariant.before_asymm forward reverse)) actualOrdered canonicalOrdered

theorem observe_carrierFor (network : State) (reachable : NotionCorePayloadNetwork.Reach network)
    (version : List NotionRunAllocation.Run) :
    NotionCoreMRDT.observe (carrierFor network version) =
      (NotionCoreMachine.replay {} (NotionCoreReconstruction.transactionsFor network version) >>=
        NotionCoreMachine.render) := by
  rw [NotionCoreMRDT.observe,transactions_carrierFor network reachable version]

/-- A source transaction can be given an independent external Sal label.
Only its actual application payload is required to agree. -/
def eventHistory (transactions : List Transaction) (lift : Transaction → Op Transaction) (answer : View) :
    List (SeqLabel (Op Transaction) Unit View) :=
  transactions.map (fun tx => .update (lift tx)) ++ [.query () answer]

/-- Exact finite-carrier rendering and independent Some-valued history
admission for any closed version of one honestly issued archive. -/
theorem honest_carrier_history (network : State) (reachable : NotionCoreMachineNetwork.Reach network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (lift : Transaction → Op Transaction)
    (payload : ∀ tx ∈ NotionCoreReconstruction.transactionsFor network version, (lift tx).op = tx) :
    ∃ answer, NotionCoreMRDT.observe (carrierFor network version) = some answer ∧
      NotionCoreMRDT.spec.admits
        ((eventHistory (NotionCoreReconstruction.transactionsFor network version) lift answer).map
          NotionCoreMRDT.someLabel) := by
  obtain ⟨answer,observed,history⟩ := NotionCoreMachineHistory.honest_history_version network reachable version closed
  refine ⟨answer,?_,?_⟩
  · rw [observe_carrierFor network
      (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)) version]
    exact observed
  · apply (NotionCoreMRDT.some_admission_iff _).mpr
    have updates : ((NotionCoreReconstruction.transactionsFor network version).map
        (fun tx => SeqLabel.update (lift tx))).map NotionCoreMRDT.semanticLabel =
        (NotionCoreMachineHistory.labels (NotionCoreReconstruction.transactionsFor network version)).map
          NotionCoreSourceHistory.semanticLabel := by
      simp only [NotionCoreMachineHistory.labels,List.map_map]
      apply List.map_congr_left
      intro tx member
      simp only [Function.comp_def,NotionCoreMRDT.semanticLabel,NotionCoreSourceHistory.semanticLabel]
      have lifted : (lift tx).2.2 = tx := payload tx member
      rw [lifted]
    simpa only [eventHistory,List.map_append,List.map_cons,List.map_nil,
      NotionCoreMRDT.semanticLabel,updates] using history

#print axioms transactions_carrierFor
#print axioms observe_carrierFor
#print axioms honest_carrier_history
end Sal.MRDTs.Instances.NotionCoreMRDTArchive
