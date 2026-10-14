import Sal.MRDTs.Instances.NotionCoreIncrementalCounterexample
import Sal.MRDTs.Instances.NotionCoreStructuralFacts
import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant

namespace Sal.MRDTs.Instances.NotionCoreStructuralCuts
open NotionCoreIncrementalCounterexample
open NotionCoreMachine
open NotionCorePayload (BlockKey Transaction)
open NotionCorePartition (Entry)
open NotionCoreSource (Atom)
open NotionCoreSliceForest
open NotionCoreMachinePartition (Partitioned)
open NotionCoreMachineShape
open NotionCoreMachineMarkerProgress

theorem canonical_split_records_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ∃ result, applyTransaction state tx = some result ∧
      cutRecords result.forest = cutRecords state.forest ++
        [⟨blockName (.issued tx.id),(blockName (.issued tx.id),.start)⟩,
         ⟨blockName (.issued tx.id),NotionCorePhysicalReplay.address (blockName inst) tx.id⟩] := by
  obtain ⟨created,rows,createStep,integrated,stage,rawForest,emptyTarget,_⟩ :=
    canonical_split_marker_phase_version network reachable version closed pre suffix tx position state accepted
      partitioned block inst origin payload
  let raw := putInstance created (blockName inst)
    {getInstance created (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) tx.id
  let target := blockName (.issued tx.id)
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network reachable version closed pre suffix tx position state accepted
  have freshTarget : target ∉ state.forest.map NotionCoreSliceForest.Block.id := by
    intro member
    obtain ⟨old,member,equal⟩ := List.mem_map.mp member
    exact freshBlock old member equal
  have createShape := fresh_create_shape_preserves state created (.issued tx.id) (some block)
    shapeInvariant freshInstance freshBlock createStep
  have createActive := fresh_create_active state created (.issued tx.id) (some block)
    freshInstance freshBlock createStep (blockName inst) activeInstance
  have rawShape : ShapeInvariant raw := raw_marker_shape_preserves created inst rows createShape createActive
  have freshMarker : FreshMarker state.forest marker := by
    intro old member key
    obtain ⟨ref,inTree,equal⟩ := List.mem_map.mp key
    have oldMember : old ∈ raw.forest := by rw [rawForest]; exact List.mem_append_left _ member
    exact stage.fresh (old.id,ref)
      (List.mem_flatMap.mpr ⟨old,oldMember,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩) equal
  have inactive : ∀ old ∈ state.forest, NotionCoreSliceForest.attached old.title = true →
      NotionCoreSliceForest.contains (physical raw) (NotionCoreSliceForest.titleRef old.id) marker = false := by
    intro old member attached
    apply inactive_title_rejects raw rawShape old _ attached marker
    rw [rawForest]
    exact List.mem_append_left _ member
  have existsInstance : ∃ entry ∈ raw.instances, entry.1 = marker.1 := by
    by_cases present : created.instances.any (fun entry => entry.1 == blockName inst) = true
    · have old : ∃ entry ∈ created.instances, entry.1 = blockName inst := by simpa using present
      exact (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created
        (blockName inst) (blockName inst) _ old).mpr old
    · simp [raw,putInstance,present,marker,NotionCorePhysicalReplay.address]
  have distinct : marker.1 ≠ target := marker_instance_ne_empty raw (blockName inst) target tx.id
    stage.present emptyTarget
  have present : marker ∈ (physical raw marker.1).map Atom.address :=
    List.mem_map.mpr ⟨_,stage.present,rfl⟩
  obtain ⟨selected,member,ref,refMember,contained⟩ :=
    NotionCoreMachinePartition.containing_tree_ref raw stage.partitioned stage.unique marker
      existsInstance present stage.fresh
  have witness : ∃ old ∈ state.forest, ∃ ref ∈ preorderTree old.title,
      contains (physical raw) ref marker = true := by
    rw [rawForest] at member
    rcases List.mem_append.mp member with old | newest
    · exact ⟨selected,old,ref,refMember,contained⟩
    · have eq := List.mem_singleton.mp newest
      subst selected
      have refEq : ref = titleRef target := by simpa [freshTitle,preorderTree,preorderChildren] using refMember
      rw [refEq,empty_title_rejects _ target marker emptyTarget] at contained
      contradiction
  obtain ⟨forest,atomic,records⟩ := atomicSplit_cutRecords (physical raw) marker target state.forest
    shapeInvariant.1 freshMarker freshTarget inactive emptyTarget witness
  refine ⟨{raw with forest := forest},
    split_transaction_of_atomic state created tx block inst origin rows forest payload createStep
      integrated stage rawForest atomic,?_⟩
  simpa [cutRecords,NotionCoreForestRefs.ownedRefs,preorderTree,preorderChildren,freshTitle,
    titleRef,cutRecord,List.append_assoc,marker,target] using records


def transactionRecords (tx : Transaction) : List Entry := match tx.payload with
  | .bootstrap _ => [⟨0,(0,.start)⟩]
  | .create _ => [⟨blockName (.issued tx.id),(blockName (.issued tx.id),.start)⟩]
  | .split _ inst _ =>
      [⟨blockName (.issued tx.id),(blockName (.issued tx.id),.start)⟩,
       ⟨blockName (.issued tx.id),NotionCorePhysicalReplay.address (blockName inst) tx.id⟩]
  | _ => []

private theorem record_append_title (forest : Forest) (bid : Nat) :
    cutRecords (forest ++ [⟨bid,freshTitle bid⟩]) = cutRecords forest ++ [⟨bid,(bid,.start)⟩] := by
  simp [cutRecords,NotionCoreForestRefs.ownedRefs,preorderTree,preorderChildren,freshTitle,titleRef,cutRecord]

private theorem put_forest (state : NotionCoreMachine.State) (inst : Nat) (value : Instance) :
    (putInstance state inst value).forest = state.forest := by simp [putInstance]; split <;> rfl

/-- Every canonical honest step adds its literal immutable creation/cut records.
Freshness and the actual containing interval are derived from the old archive. -/
theorem canonical_records_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (step : applyTransaction state tx = some result) :
    cutRecords result.forest = cutRecords state.forest ++ transactionRecords tx := by
  obtain ⟨checked,replayed,part,shape,roots⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed pre (tx::suffix) position
  have equal := Option.some.inj (replayed.symm.trans accepted)
  subst checked
  have creators := NotionCoreMachineNetwork.creator_reachable reachable
  cases payload : tx.payload with
  | bootstrap atoms =>
    have txEq := NotionCoreBootstrapProvenance.canonical_bootstrap_transaction_version
      network creators version pre suffix tx position atoms payload
    obtain ⟨freshInst,freshBlock⟩ := NotionCoreBootstrapProvenance.canonical_bootstrap_fresh_version
      network creators version closed pre suffix tx position atoms payload state accepted
    obtain ⟨expected,exec,_,forest,_⟩ := NotionCoreMachineBootstrap.fresh_bootstrap_preserves state atoms part freshInst freshBlock
    have same := Option.some.inj ((txEq ▸ exec).symm.trans step)
    subst expected
    rw [forest,record_append_title]
    simp [transactionRecords,payload]
  | create afterBlock =>
    obtain ⟨freshInst,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
      network creators version closed pre suffix tx position state accepted
    have createStep : applyOperation state (.create (.issued tx.id) afterBlock) = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
    have frame := (NotionCoreMachineCanonicalCreate.fresh_create_shape state result (.issued tx.id)
      afterBlock freshInst freshBlock createStep).2.1
    rw [frame,record_append_title]
    simp [transactionRecords,payload]
  | insert block inst origin atoms =>
    cases integrated : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems tx.id atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation,integrated] at step
    | some rows =>
      have same : putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows} = result := by
        simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation,integrated] using step
      rw [← same,put_forest]
      simp [transactionRecords,payload]
  | erase block inst ids =>
    have same : putInstance state (blockName inst)
      ⟨NotionCoreParentErase.erase ids (getInstance state (blockName inst)).rows,
       (getInstance state (blockName inst)).pending ++ ids⟩ = result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation] using step
    rw [← same,put_forest]
    simp [transactionRecords,payload]
  | split block inst origin =>
    obtain ⟨provider,member,root,_⟩ := NotionCoreRootCreators.canonical_selected_root_provider_version
      network creators (NotionCoreMachineHonestReplay.honest_root_provenance network reachable)
      version closed pre suffix tx position inst (by simp [NotionCoreRootCreators.selectedInstances,payload])
    have active : ActiveInstance state (blockName inst) := (roots _).mpr ⟨provider,member,inst,root,rfl⟩
    obtain ⟨expected,exec,records⟩ := canonical_split_records_version network creators version closed
      pre suffix tx position state accepted part shape block inst origin payload active
    have same := Option.some.inj (exec.symm.trans step)
    subst expected
    simpa [transactionRecords,payload] using records

private theorem replay_append (state : NotionCoreMachine.State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih => simp only [List.cons_append,replay]; cases step : applyTransaction state tx <;> simp [ih]

/-- Exact archive-derived cut records for every canonical closed-version prefix.
The maintained owner/start facts are sufficient; no interval endpoints or text
owner assignments must be replayed or merged. -/
theorem honest_records_prefix (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state) :
    cutRecords state.forest = pre.flatMap transactionRecords := by
  induction pre using List.reverseRecOn generalizing suffix state with
  | nil => simp [replay] at accepted; subst state; rfl
  | append_singleton pre tx ih =>
    have oldPosition : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix := by
      simpa [List.append_assoc] using position
    obtain ⟨old,oldReplay,_,_,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version
      network reachable version closed pre (tx::suffix) oldPosition
    have exec : applyTransaction old tx = some state := by
      simpa [replay_append,oldReplay,replay] using accepted
    rw [canonical_records_step network reachable version closed pre suffix tx oldPosition old state oldReplay exec]
    rw [ih (tx::suffix) oldPosition old oldReplay]
    simp


/-- Interpret only created/cut facts. Parent rows and deletion records are
separate components, and no transaction sorting occurs here. -/
def factRecord : NotionCoreStructuralFacts.Fact → Option Entry
  | .created block _ => some ⟨blockName block,(blockName block,.start)⟩
  | .cut inst marker target => some ⟨blockName target,NotionCorePhysicalReplay.address (blockName inst) marker⟩
  | _ => none

noncomputable def records (facts : NotionCoreStructuralFacts.State) : List Entry :=
  (facts.toList.filterMap factRecord).toFinset.toList

private theorem decode_records (tx : Transaction) :
    (NotionCoreStructuralFacts.decodeList tx).filterMap factRecord = transactionRecords tx := by
  have noBirths : ((NotionCorePayload.births tx (fun _ _ => false)).map
      (fun pair => NotionCoreStructuralFacts.Fact.birth pair.1 pair.2)).filterMap factRecord = [] := by
    simp [List.filterMap_map, Function.comp_def, factRecord]
  rw [NotionCoreStructuralFacts.decodeList,List.filterMap_append,noBirths,List.nil_append]
  cases tx with
  | mk id payload => cases payload <;> simp [NotionCoreStructuralFacts.extra,factRecord,transactionRecords,blockName,List.filterMap_map,Function.comp_def]

/-- Finite structural fact union contains exactly the archived cut records,
including every inactive title START. This statement is independent of replay. -/
theorem records_ofTransactions (txs : List Transaction) :
    (records (NotionCoreStructuralFacts.ofTransactions txs)).toFinset =
      (txs.flatMap transactionRecords).toFinset := by
  apply Finset.ext
  intro entry
  simp only [records,List.mem_toFinset,List.mem_filterMap,
    Finset.mem_toList,NotionCoreStructuralFacts.ofTransactions,List.mem_flatMap]
  constructor
  · rintro ⟨fact,⟨tx,member,decoded⟩,equal⟩
    refine ⟨tx,member,?_⟩
    rw [← decode_records]
    exact List.mem_filterMap.mpr ⟨fact,decoded,equal⟩
  · rintro ⟨tx,member,present⟩
    rw [← decode_records] at present
    obtain ⟨fact,decoded,equal⟩ := List.mem_filterMap.mp present
    exact ⟨fact,⟨tx,member,decoded⟩,equal⟩

private theorem starts_sublist (state : NotionCoreMachine.State) (refs : List (Nat × Ref)) :
    (refs.map (fun owned => owned.2.start)).Sublist
      (refs.flatMap (fun owned => NotionCoreMachineDocumentInvariant.intervalAddresses state owned.2)) := by
  induction refs with
  | nil => simp
  | cons owned rest ih =>
    simp only [List.map_cons,List.flatMap_cons,NotionCoreMachineDocumentInvariant.intervalAddresses,List.cons_append]
    exact (ih.trans (List.sublist_append_right _ _)).cons₂ _

/-- No duplicate record can occur in the actual partitioned source forest.
The proof includes empty titles and derives global uniqueness from per-instance
physical identity uniqueness. -/
theorem cutRecords_nodup (state : NotionCoreMachine.State) (part : Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup) :
    (cutRecords state.forest).Nodup := by
  have starts := (starts_sublist state (NotionCoreForestRefs.ownedRefs state.forest)).nodup
    (NotionCoreMachineDocumentInvariant.all_addresses_unique state part unique)
  apply List.Nodup.of_map Entry.start
  simpa [cutRecords,cutRecord,List.map_map,Function.comp_def] using starts

/-- The direct representation's unordered, deduplicated cut records are a
permutation of the actual replay forest's immutable starts and owners. All
structural and record completeness conditions follow from honest issuance. -/
theorem honest_records (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) :
    ∃ state, replay {} (NotionCoreReconstruction.transactionsFor network version) = some state ∧
      (records (NotionCoreStructuralFacts.ofTransactions
        (NotionCoreReconstruction.transactionsFor network version))).Perm (cutRecords state.forest) := by
  obtain ⟨state,accepted,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  refine ⟨state,accepted,?_⟩
  have actual := honest_records_prefix network reachable version closed _ [] (by simp) state accepted
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all_version network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable))
    version closed _ [] (by simp) state accepted
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact Finset.nodup_toList _
  · exact cutRecords_nodup state part unique
  · rw [actual]
    exact records_ofTransactions _

#print axioms honest_records
#print axioms records_ofTransactions
#print axioms canonical_records_step
#print axioms honest_records_prefix
#print axioms canonical_split_records_version
end Sal.MRDTs.Instances.NotionCoreStructuralCuts
