import Sal.MRDTs.Instances.NotionCoreRichSequentialCoreSimulation

/-! Whole erasure transactions preserve the direct rich state. The proof
composes actual per-instance tombstone edits inside one external update;
existing gap marks and retained physical identities survive every group. -/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
open NotionCoreSpec

private def eraseCommands (groups : List (NotionCorePayload.BlockKey × List NotionRunAllocation.Id)) :
    List NotionCoreSpec.Command :=
  groups.map fun group => .delete
    (group.2.map (NotionCorePhysicalReplay.address (NotionCoreMachine.blockName group.1)))

/-- Arbitrarily many instance groups remain one transaction. Domain
preservation is proved at each actual erase, including duplicate groups. -/
theorem erase_groups_coreBatch (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (related : Related actual abstract) (supported : SupportedBatches actual)
    (block : NotionCorePayload.BlockKey)
    (groups : List (NotionCorePayload.BlockKey × List NotionRunAllocation.Id))
    (registered : ∀ group ∈ groups, Registered actual (NotionCoreMachine.blockName group.1)) :
    ∃ core after,
      NotionCoreMachine.applyOperations actual.core
        (groups.map fun group => .erase block group.1 group.2) = some core ∧
      coreBatch abstract (eraseCommands groups) = some after ∧ Related (edited actual core) after := by
  induction groups generalizing actual abstract with
  | nil => exact ⟨actual.core,abstract,rfl,rfl,related⟩
  | cons group rest ih =>
    cases operation : NotionCoreMachine.applyOperation actual.core (.erase block group.1 group.2) with
    | none => simp [NotionCoreMachine.applyOperation] at operation
    | some mid =>
      obtain ⟨middle,first,relatedMiddle⟩ := erase_related_coreStep actual abstract related supported mid
        block group.1 group.2 (registered group (by simp)) operation
      have remaining : ∀ next ∈ rest, Registered (edited actual mid) (NotionCoreMachine.blockName next.1) := by
        intro next member
        exact (actual_erase_registration actual mid block group.1 group.2
          (registered group (by simp)) operation _).mpr (registered next (by simp [member]))
      obtain ⟨core,after,operations,commands,relatedAfter⟩ := ih (edited actual mid) middle relatedMiddle
        supported remaining
      refine ⟨core,after,?_,?_,relatedAfter⟩
      · simpa only [List.map_cons,NotionCoreMachine.applyOperations,operation,Bind.bind,Option.bind]
          using operations
      · simpa only [eraseCommands,List.map_cons,coreBatch,first,Bind.bind,Option.bind] using commands

/-- Honest canonical replay supplies every required instance registration.
No successful rich transition or query equation is assumed. -/
theorem canonical_erase_coreBatch (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List NotionCorePayload.Transaction) (tx : NotionCorePayload.Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State) (related : Related actual abstract)
    (replayed : NotionCoreMachine.replay {} pre = some actual.core)
    (block : NotionCorePayload.BlockKey)
    (groups : List (NotionCorePayload.BlockKey × List NotionRunAllocation.Id))
    (payload : tx.payload = .erase block groups) (supported : SupportedBatches actual) :
    ∃ core after, NotionCoreMachine.applyTransaction actual.core tx = some core ∧
      coreBatch abstract ((NotionCoreMachineCommands.commands tx).map
        NotionCoreSourceDocument.Command.semantic) = some after ∧ Related (edited actual core) after := by
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  have registered : ∀ group ∈ groups, Registered actual (NotionCoreMachine.blockName group.1) := by
    intro group member
    exact NotionCoreMachineCreatorPresence.canonical_required_instance_version network creators
      version closed pre suffix tx position actual.core replayed group.1
      (by simp [payload,NotionCoreCreatorNetwork.requiredBlocks]; exact Or.inr ⟨group.2,member⟩)
  obtain ⟨core,after,operations,commands,relation⟩ := erase_groups_coreBatch actual abstract related supported block groups registered
  refine ⟨core,after,?_,?_,relation⟩
  · simpa only [NotionCoreMachine.applyTransaction,NotionCorePayload.operations,payload] using operations
  · simpa only [NotionCoreMachineCommands.commands,payload,List.map_map,
      NotionCoreSourceDocument.Command.semantic,Function.comp_def,eraseCommands] using commands

#print axioms erase_groups_coreBatch
#print axioms canonical_erase_coreBatch
end Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
