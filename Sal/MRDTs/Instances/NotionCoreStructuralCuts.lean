import Sal.MRDTs.Instances.NotionCoreIncrementalCounterexample
import Sal.MRDTs.Instances.NotionCoreStructuralFacts
import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant
import Sal.MRDTs.Instances.NotionCoreMergeFree

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
open NotionCoreSpec (Address)

/-! Merge-free shape. Without merge every chain is a lone root, or an empty
title root followed by one leaf that does not open an instance. This is the
shape the record selector relies on; merge appends live chains and leaves it. -/

def FlatBlock (block : Block) : Prop :=
  Normal block.id block.title ∧ (attached block.title = true → (active block.title).start.2 ≠ .start)

def Flat (forest : Forest) : Prop := ∀ block ∈ forest, FlatBlock block

theorem flat_nil : Flat [] := by simp [Flat]

theorem flat_append_title (forest : Forest) (bid : Nat) (flat : Flat forest) :
    Flat (forest ++ [⟨bid,freshTitle bid⟩]) := by
  intro block member
  rcases List.mem_append.mp member with old | newest
  · exact flat block old
  · have equal := List.mem_singleton.mp newest
    subst block
    exact ⟨Normal.own none,by simp [attached,freshTitle,Tree.children]⟩

/-- In a flat reachable forest the title root of an attached block is the dead
empty root of its own instance, and the active leaf lies in another instance. -/
theorem flat_attached (state : NotionCoreMachine.State) (shape : ShapeInvariant state)
    (flat : Flat state.forest) (block : Block) (member : block ∈ state.forest)
    (attachedEq : attached block.title = true) :
    physical state block.id = emptyPhysical block.id ∧ (active block.title).start.1 ≠ block.id := by
  obtain ⟨normal,act⟩ := flat block member
  rcases block with ⟨bid,tree⟩
  change Normal bid tree at normal
  cases normal with
  | own stop => simp [attached,Tree.children] at attachedEq
  | attached leaf =>
    have opens : leaf.start.2 ≠ .start := by simpa [active,Tree.children,Tree.slice] using act rfl
    have nodesEq : nodes (preorderTree (.node (titleRef bid) (.cons (.node leaf .nil) .nil))) =
        [(titleRef bid,false),(leaf,true)] := by
      simp [nodes,tagBefore,preorderTree,preorderChildren,opensInstance,opens]
    have dead : (titleRef bid,false) ∈ forestNodes state.forest :=
      List.mem_flatMap.mpr ⟨_,member,by rw [nodesEq]; simp⟩
    have live : (leaf,true) ∈ forestNodes state.forest :=
      List.mem_flatMap.mpr ⟨_,member,by rw [nodesEq]; simp⟩
    obtain ⟨_,physicalEq,lives⟩ := shape.2.2.1 _ dead
    exact ⟨physicalEq,by simpa [active,Tree.children,Tree.slice,titleRef] using lives leaf live⟩

/-- A flat block split at a containing node: the node is the last one, since
the empty title root of an attached block is dead and rejects every marker. -/
private theorem flat_split_block (physical : Nat → List Atom) (marker : Address) (bid : Nat)
    (tree title moved : Tree) (pre post : List Ref) (ref : Ref)
    (normal : Normal bid tree) (act : attached tree = true → (active tree).start.2 ≠ .start)
    (deadRejects : ∀ dead, (dead,false) ∈ nodes (preorderTree tree) → contains physical dead marker = false)
    (old : preorderTree tree = pre ++ ref :: post) (inside : contains physical ref marker = true)
    (titleChain : Chain title) (titleEq : preorderTree title = pre ++ [leftRef ref marker])
    (movedChain : Chain moved) (movedEq : preorderTree moved = rightRef ref marker :: post) :
    post = [] ∧ FlatBlock ⟨bid,title⟩ ∧ moved = .node (rightRef ref marker) .nil := by
  have movedLeaf (empty : post = []) : moved = .node (rightRef ref marker) .nil := by
    subst post
    exact chain_ext movedChain (.leaf _) (by rw [movedEq]; rfl)
  cases normal with
  | own stop =>
    have shape : pre = [] ∧ ref = ⟨(bid,.start),stop⟩ ∧ post = [] := by
      cases pre with
      | nil => simpa [preorderTree,preorderChildren,eq_comm] using old
      | cons head rest => cases rest <;> simp [preorderTree,preorderChildren] at old
    obtain ⟨rfl,rfl,rfl⟩ := shape
    have titleShape : title = .node ⟨(bid,.start),some marker⟩ .nil :=
      chain_ext titleChain (.leaf _) (by rw [titleEq]; rfl)
    subst title
    exact ⟨rfl,⟨Normal.own (some marker),by simp [attached,Tree.children]⟩,movedLeaf rfl⟩
  | attached leaf =>
    have opens : leaf.start.2 ≠ .start := act rfl
    cases pre with
    | nil =>
      have refEq : ref = titleRef bid := by
        simpa [preorderTree,preorderChildren] using (List.cons.inj old).1.symm
      have dead : (titleRef bid,false) ∈ nodes (preorderTree (.node (titleRef bid) (.cons (.node leaf .nil) .nil))) := by
        simp [nodes,tagBefore,preorderTree,preorderChildren,opensInstance,opens]
      rw [refEq,deadRejects _ dead] at inside
      contradiction
    | cons head rest =>
      cases rest with
      | nil =>
        have pieces : head = titleRef bid ∧ ref = leaf ∧ post = [] := by
          simpa [preorderTree,preorderChildren,eq_comm] using old
        obtain ⟨rfl,rfl,rfl⟩ := pieces
        have titleShape : title = .node (titleRef bid) (.cons (.node (leftRef ref marker) .nil) .nil) :=
          chain_ext titleChain (.link _ _ (.leaf _)) (by rw [titleEq]; rfl)
        subst title
        exact ⟨rfl,⟨Normal.attached _,fun _ => by simpa [active,Tree.children,Tree.slice,leftRef] using opens⟩,
          movedLeaf rfl⟩
      | cons next tail => simp [preorderTree,preorderChildren] at old

/-- An atomic split of a flat forest is flat, and its records are the old
records followed by the destination's title and marker records. -/
theorem atomicSplit_flat (physical : Nat → List Atom) (marker : Address) (target : Nat)
    (forest result : Forest) (chains : ChainForest forest) (flat : Flat forest)
    (fresh : FreshMarker forest marker) (freshTarget : target ∉ forest.map Block.id)
    (empty : physical target = emptyPhysical target) (markerEvent : marker.2 ≠ .start)
    (deadRejects : ∀ dead, (dead,false) ∈ forestNodes forest → contains physical dead marker = false)
    (accepted : atomicSplit physical marker target forest = some result) :
    Flat result ∧
      cutRecords result = cutRecords forest ++ [⟨target,(target,.start)⟩,⟨target,marker⟩] := by
  obtain ⟨before,block,after,pre,ref,post,title,moved,shape,old,inside,titleChain,titleEq,
    movedChain,movedEq,resultEq⟩ :=
    atomicSplit_result physical marker target forest result (fun b hb => (chains b hb).1)
      fresh freshTarget empty accepted
  have blockMember : block ∈ forest := by rw [shape]; simp
  obtain ⟨normal,act⟩ := flat block blockMember
  have blockDead : ∀ dead, (dead,false) ∈ nodes (preorderTree block.title) →
      contains physical dead marker = false := fun dead member =>
    deadRejects dead (List.mem_flatMap.mpr ⟨block,blockMember,member⟩)
  obtain ⟨postNil,titleFlat,movedShape⟩ := flat_split_block physical marker block.id block.title title moved
    pre post ref normal act blockDead old inside titleChain titleEq movedChain movedEq
  subst postNil movedShape
  subst resultEq
  constructor
  · intro found member
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (member | rfl | member) | rfl
    · exact flat found (by rw [shape]; simp [member])
    · exact titleFlat
    · exact flat found (by rw [shape]; simp [member])
    · exact ⟨Normal.attached _,fun _ => by simpa [active,Tree.children,Tree.slice,rightRef] using markerEvent⟩
  · rw [shape]
    simp [cutRecords,NotionCoreForestRefs.ownedRefs,old,titleEq,preorderTree,preorderChildren,
      cutRecord,leftRef,rightRef,titleRef,List.map_append,List.append_assoc]

theorem canonical_split_records_version (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (partitioned : Partitioned state) (shapeInvariant : ShapeInvariant state) (flat : Flat state.forest)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (activeInstance : ActiveInstance state (blockName inst)) :
    ∃ result, applyTransaction state tx = some result ∧ Flat result.forest ∧
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
    exact freshBlock.1 old member equal
  have createShape := fresh_create_shape_preserves state created (.issued tx.id) (some block)
    shapeInvariant partitioned freshInstance freshBlock createStep
  have createActive := fresh_create_active state created (.issued tx.id) (some block)
    freshInstance freshBlock createStep (blockName inst) activeInstance
  have rawShape : ShapeInvariant raw := raw_marker_shape_preserves created inst rows createShape createActive
  have freshMarker : FreshMarker state.forest marker := by
    intro old member key
    obtain ⟨ref,inTree,equal⟩ := List.mem_map.mp key
    have oldMember : old ∈ raw.forest := by rw [rawForest]; exact List.mem_append_left _ member
    exact stage.fresh (old.id,ref)
      (List.mem_flatMap.mpr ⟨old,oldMember,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩) equal
  have markerEvent : marker.2 ≠ .start := by
    simp [marker,NotionCorePhysicalReplay.address,NotionCorePhysicalReplay.localId]
  have deadRejects : ∀ dead, (dead,false) ∈ forestNodes state.forest →
      NotionCoreSliceForest.contains (physical raw) dead marker = false := by
    intro dead member
    apply dead_title_rejects raw rawShape dead _ marker
    rw [rawForest,NotionCoreSliceForest.forestNodes_append]
    exact List.mem_append_left _ member
  have existsInstance : ∃ entry ∈ raw.instances, entry.1 = marker.1 := by
    by_cases present : created.instances.any (fun entry => entry.1 == blockName inst) = true
    · have old : ∃ entry ∈ created.instances, entry.1 = blockName inst := by simpa using present
      exact (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created
        (blockName inst) (blockName inst) _ old).mpr old
    · simp [raw,putInstance,present,marker,NotionCorePhysicalReplay.address]
  obtain ⟨forest,atomic,_⟩ := NotionCoreMachinePartitionSplit.atomicSplit_partitioned
    raw state.forest marker target rawForest stage.partitioned stage.unique
      (fun found member => (shapeInvariant.1 found member).1)
      freshMarker freshTarget emptyTarget existsInstance stage.present stage.fresh
  obtain ⟨flatNext,records⟩ := atomicSplit_flat (physical raw) marker target state.forest forest
    shapeInvariant.1 flat freshMarker freshTarget emptyTarget markerEvent deadRejects atomic
  exact ⟨{raw with forest := forest},
    split_transaction_of_atomic state created tx block inst origin rows forest payload createStep
      integrated stage rawForest atomic,flatNext,records⟩


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

private theorem erase_groups_forest (state result : NotionCoreMachine.State) (block : BlockKey)
    (groups : List (BlockKey × List NotionRunAllocation.Id))
    (accepted : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result) :
    result.forest = state.forest := by
  induction groups generalizing state with
  | nil =>
    simp only [List.map_nil,applyOperations,Option.some.injEq] at accepted
    rw [accepted]
  | cons group rest ih =>
    cases first : applyOperation state (.erase block group.1 group.2) with
    | none => simp [applyOperations,first] at accepted
    | some middle =>
      have later : applyOperations middle (rest.map fun group => .erase block group.1 group.2) =
          some result := by simpa [applyOperations,first] using accepted
      rw [ih middle later,(NotionCoreMachineErase.erase_physical state middle block group.1 group.2 first).1]

/-- Every canonical honest merge-free step adds its literal immutable
creation/cut records and keeps the forest flat. Freshness and the actual
containing interval are derived from the old archive. The step excludes merge,
which moves records between owners. -/
theorem canonical_records_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (flat : Flat state.forest) (notMerge : NotionCoreMergeFree.NotMerge tx)
    (step : applyTransaction state tx = some result) :
    Flat result.forest ∧ cutRecords result.forest = cutRecords state.forest ++ transactionRecords tx := by
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
    exact ⟨flat_append_title _ _ flat,by simp [transactionRecords,payload]⟩
  | create afterBlock =>
    obtain ⟨freshInst,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
      network creators version closed pre suffix tx position state accepted
    have createStep : applyOperation state (.create (.issued tx.id) afterBlock) = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using step
    have frame := (NotionCoreMachineCanonicalCreate.fresh_create_shape state result (.issued tx.id)
      afterBlock freshInst freshBlock createStep).2.1
    rw [frame,record_append_title]
    exact ⟨flat_append_title _ _ flat,by simp [transactionRecords,payload]⟩
  | insert block inst origin atoms =>
    cases integrated : integrateRows (getInstance state (blockName inst)).rows
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems tx.id atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
    | none => simp [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation,integrated] at step
    | some rows =>
      have same : putInstance state (blockName inst) {getInstance state (blockName inst) with rows := rows} = result := by
        simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation,integrated] using step
      rw [← same,put_forest]
      exact ⟨flat,by simp [transactionRecords,payload]⟩
  | erase block groups =>
    have ops : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload] using step
    rw [erase_groups_forest state result block groups ops]
    exact ⟨flat,by simp [transactionRecords,payload]⟩
  | split block inst origin =>
    obtain ⟨provider,member,root,_⟩ := NotionCoreRootCreators.canonical_selected_root_provider_version
      network creators (NotionCoreMachineHonestReplay.honest_root_provenance network reachable)
      version closed pre suffix tx position inst (by simp [NotionCoreRootCreators.selectedInstances,payload])
    have active : ActiveInstance state (blockName inst) := (roots _).mpr ⟨provider,member,inst,root,rfl⟩
    obtain ⟨expected,exec,flatNext,records⟩ := canonical_split_records_version network creators version closed
      pre suffix tx position state accepted part shape flat block inst origin payload active
    have same := Option.some.inj (exec.symm.trans step)
    subst expected
    exact ⟨flatNext,by simpa [transactionRecords,payload] using records⟩
  | merge source inst stop => exact False.elim (notMerge source inst stop payload)

private theorem replay_append (state : NotionCoreMachine.State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih => simp only [List.cons_append,replay]; cases step : applyTransaction state tx <;> simp [ih]

/-- Exact archive-derived cut records for every canonical closed-version prefix
of a merge-free network, which also keeps every prefix forest flat. The
maintained owner/start facts are sufficient; no interval endpoints or text owner
assignments must be replayed or merged. A merge would move records to a new
owner, so the statement covers the merge-free fragment. -/
theorem honest_records_prefix (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (free : NotionCoreMergeFree.MergeFree network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state) :
    Flat state.forest ∧ cutRecords state.forest = pre.flatMap transactionRecords := by
  induction pre using List.reverseRecOn generalizing suffix state with
  | nil => simp [replay] at accepted; subst state; exact ⟨flat_nil,rfl⟩
  | append_singleton pre tx ih =>
    have oldPosition : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix := by
      simpa [List.append_assoc] using position
    obtain ⟨old,oldReplay,_,_,_⟩ := NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version
      network reachable version closed pre (tx::suffix) oldPosition
    have exec : applyTransaction old tx = some state := by
      simpa [replay_append,oldReplay,replay] using accepted
    have notMerge := NotionCoreMergeFree.transactionsFor network free version tx (by rw [oldPosition]; simp)
    obtain ⟨oldFlat,oldRecords⟩ := ih (tx::suffix) oldPosition old oldReplay
    obtain ⟨flatNext,records⟩ := canonical_records_step network reachable version closed pre suffix tx oldPosition
      old state oldReplay oldFlat notMerge exec
    refine ⟨flatNext,?_⟩
    rw [records,oldRecords]
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
  | mk id payload =>
    cases payload <;> simp [NotionCoreStructuralFacts.extra,factRecord,transactionRecords,blockName]
    intro fact _ _ _ _ _ decoded
    subst decoded
    rfl

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
structural and record completeness conditions follow from honest issuance. It
covers the merge-free fragment: a merge changes the owner of every record it
moves, and which records move depends on replay order. -/
theorem honest_records (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (free : NotionCoreMergeFree.MergeFree network)
    (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version) :
    ∃ state, replay {} (NotionCoreReconstruction.transactionsFor network version) = some state ∧
      (records (NotionCoreStructuralFacts.ofTransactions
        (NotionCoreReconstruction.transactionsFor network version))).Perm (cutRecords state.forest) := by
  obtain ⟨state,accepted,part,_,_⟩ := NotionCoreMachineHonestReplay.honest_reconstruct_version network reachable version closed
  refine ⟨state,accepted,?_⟩
  have actual := (honest_records_prefix network reachable free version closed _ [] (by simp) state accepted).2
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
