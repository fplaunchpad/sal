import Sal.MRDTs.Instances.NotionCoreMachinePartitionSplit
import Sal.MRDTs.Instances.NotionCoreSearchLabels
import Sal.MRDTs.Instances.NotionCoreMachineHonestReplay
import Sal.MRDTs.Instances.NotionCoreMachineDocumentInvariant

/-! Search labels attached to actual retained slice starts. The relation keeps
pairwise separation by distinct addresses: an image set alone would forget
collisions. Moving a slice changes its block owner, never its label. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineSearchLabels
open NotionCoreSpec (Address)
open NotionCoreSliceForest
open NotionCoreForestRefs
open NotionCoreSearchLabels

def Starts (forest : Forest) : Set Address :=
  {address | ∃ owned ∈ ownedRefs forest, owned.2.start = address}

abbrev Labels := Address → List Nat

def Good (starts : Set Address) (labels : Labels) : Prop :=
  (∀ a ∈ starts, Canonical (labels a)) ∧
  (∀ a ∈ starts, ∀ b ∈ starts, a.1 = b.1 → a ≠ b →
    Separated (printable (labels a)) (printable (labels b)))

def splitLabels (labels : Labels) (selected marker : Address) : Labels :=
  fun a => if a = marker then (splitLabel (labels selected)).2
    else if a = selected then (splitLabel (labels selected)).1 else labels a

/-- Literal duplicate-label rejection follows from address-sensitive separation,
not merely from prefix-freedom of the set of label values. -/
theorem no_collision {starts labels} (good : Good starts labels)
    {a b : Address} (ha : a ∈ starts) (hb : b ∈ starts) (inst : a.1 = b.1)
    (same : labels a = labels b) : a = b := by
  by_contra distinct
  have separated := good.2 a ha b hb inst distinct
  apply separated.1
  rw [same]

theorem split_good {starts : Set Address} {labels : Labels} (good : Good starts labels)
    {selected marker : Address} (member : selected ∈ starts) (fresh : marker ∉ starts)
    (inst : selected.1 = marker.1) :
    Good (starts ∪ {marker}) (splitLabels labels selected marker) := by
  have different : selected ≠ marker := by intro eq; exact fresh (eq ▸ member)
  obtain ⟨lc,rc,_,_,lp,rp⟩ := canonical_split (good.1 selected member)
  constructor
  · intro a ha
    rcases ha with ha | hm
    · have am : a ≠ marker := by intro eq; exact fresh (eq ▸ ha)
      by_cases chosen : a = selected
      · subst a; simpa [splitLabels,different] using lc
      · simpa [splitLabels,am,chosen] using good.1 a ha
    · have equal : a = marker := hm
      subst a
      simpa [splitLabels] using rc
  · intro a ha b hb sameInst distinct
    rcases ha with ha | am <;> rcases hb with hb | bm
    · have an : a ≠ marker := by intro eq; exact fresh (eq ▸ ha)
      have bn : b ≠ marker := by intro eq; exact fresh (eq ▸ hb)
      by_cases ac : a = selected <;> by_cases bc : b = selected
      · exact False.elim (distinct (ac.trans bc.symm))
      · subst a
        simp only [splitLabels,if_neg an,if_neg bn,ite_true,if_neg bc]
        rw [lp]
        exact (separated_extend (good.2 b hb selected member sameInst.symm bc) false).symm
      · subst b
        simp only [splitLabels,if_neg an,if_neg bn,ite_true,if_neg ac]
        rw [lp]
        exact separated_extend (good.2 a ha selected member sameInst ac) false
      · simpa [splitLabels,an,bn,ac,bc] using good.2 a ha b hb sameInst distinct
    · have eq : b = marker := bm
      subst b
      have an : a ≠ marker := by intro eq; exact fresh (eq ▸ ha)
      by_cases ac : a = selected
      · subst a
        simp only [splitLabels,if_neg different,ite_true]
        rw [lp,rp]
        exact siblings_separated _
      · simp only [splitLabels,if_neg an,if_neg ac,ite_true]
        rw [rp]
        exact separated_extend (good.2 a ha selected member (sameInst.trans inst.symm) ac) true
    · have eq : a = marker := am
      subst a
      have bn : b ≠ marker := by intro eq; exact fresh (eq ▸ hb)
      by_cases bc : b = selected
      · subst b
        simp only [splitLabels,if_neg different,ite_true]
        rw [lp,rp]
        exact (siblings_separated _).symm
      · simp only [splitLabels,if_neg bn,if_neg bc,ite_true]
        rw [rp]
        exact (separated_extend (good.2 b hb selected member (sameInst.symm.trans inst.symm) bc) true).symm
    · have ae : a = marker := am
      have be : b = marker := bm
      exact False.elim (distinct (ae.trans be.symm))

def addRootLabels (labels : Labels) (inst : Nat) : Labels :=
  fun a => if a = (inst,.start) then [] else labels a

theorem add_root_good {starts : Set Address} {labels : Labels} (good : Good starts labels)
    (inst : Nat) (fresh : ∀ a ∈ starts, a.1 ≠ inst) :
    Good (starts ∪ {(inst,.start)}) (addRootLabels labels inst) := by
  have different : ∀ a ∈ starts, a ≠ (inst,.start) := by
    intro a member equal
    exact fresh a member (congrArg Prod.fst equal)
  constructor
  · intro a ha
    rcases ha with old | new
    · simpa [addRootLabels,different a old] using good.1 a old
    · have equal : a = (inst,.start) := new
      subst a
      simpa [addRootLabels] using Canonical.nil
  · intro a ha b hb same distinct
    rcases ha with olda | newa <;> rcases hb with oldb | newb
    · simpa [addRootLabels,different a olda,different b oldb] using good.2 a olda b oldb same distinct
    · have equal : b = (inst,.start) := newb
      exact False.elim (fresh a olda (same.trans (congrArg Prod.fst equal)))
    · have equal : a = (inst,.start) := newa
      exact False.elim (fresh b oldb (same.symm.trans (congrArg Prod.fst equal)))
    · have ae : a = (inst,.start) := newa
      have be : b = (inst,.start) := newb
      exact False.elim (distinct (ae.trans be.symm))

theorem starts_create (forest : Forest) (inst : Nat) :
    Starts (forest ++ [⟨inst,freshTitle inst⟩]) = Starts forest ∪ {(inst,.start)} := by
  ext address
  simp only [Starts,ownedRefs_create,List.mem_append,List.mem_singleton,Set.mem_union,Set.mem_singleton_iff]
  simp only [titleRef]
  aesop

/-- Actual new-instance storage freshness supplies label-root freshness. -/
theorem create_labels (state : NotionCoreMachine.State)
    (part : NotionCoreMachinePartition.Partitioned state) (labels : Labels)
    (good : Good (Starts state.forest) labels) (inst : Nat)
    (fresh : ∀ entry ∈ state.instances, entry.1 ≠ inst) :
    Good (Starts (state.forest ++ [⟨inst,freshTitle inst⟩])) (addRootLabels labels inst) := by
  rw [starts_create]
  apply add_root_good good inst
  intro a member same
  obtain ⟨owned,member,equal⟩ := member
  obtain ⟨entry,stored,instEq⟩ := part.refsExist owned member
  exact fresh entry stored (instEq.trans ((congrArg Prod.fst equal).trans same))

theorem starts_list (forest : Forest) (address : Address) :
    address ∈ Starts forest ↔ address ∈ (ownedRefs forest).map (fun owned => owned.2.start) := by
  simp [Starts]

/-- Couple the actual recursive split/detach/move result to label splitting.
The selected slice is recovered from source traversal, never supplied by caller. -/
theorem atomicSplit_labels (physical : Nat → List NotionCoreSource.Atom)
    (marker : Address) (target : Nat) (forest : Forest)
    (chains : ∀ block ∈ forest, Chain block.title) (fresh : FreshMarker forest marker)
    (freshTarget : target ∉ forest.map Block.id)
    (empty : physical target = emptyPhysical target)
    (witness : ∃ block ∈ forest, ∃ ref ∈ preorderTree block.title, contains physical ref marker = true)
    (labels : Labels) (good : Good (Starts (forest ++ [⟨target,freshTitle target⟩])) labels)
    (markerFresh : marker ∉ Starts (forest ++ [⟨target,freshTitle target⟩])) :
    ∃ result selected,
      atomicSplit physical marker target forest = some result ∧
      selected ∈ Starts (forest ++ [⟨target,freshTitle target⟩]) ∧
      (∃ owned ∈ ownedRefs forest, owned.2.start = selected ∧ contains physical owned.2 marker = true) ∧
      Good (Starts result) (splitLabels labels selected marker) := by
  obtain ⟨result,accepted⟩ :=
    NotionCoreMachinePartitionSplit.atomicSplit_progress physical marker target forest chains fresh empty witness
  obtain ⟨before,owner,pre,ref,post,after,old,contained,new⟩ :=
    NotionCoreMachinePartitionSplit.atomicSplit_refs physical marker target forest result chains fresh freshTarget
      empty accepted
  have member : ref.start ∈ Starts (forest ++ [⟨target,freshTitle target⟩]) := by
    refine ⟨(owner,ref),?_,rfl⟩
    rw [old]
    simp
  have inst : ref.start.1 = marker.1 := by
    simp only [contains,Bool.and_eq_true] at contained
    exact of_decide_eq_true contained.1
  have starts : Starts result = Starts (forest ++ [⟨target,freshTitle target⟩]) ∪ {marker} := by
    ext address
    rw [Set.mem_union,starts_list,starts_list,new,old]
    simp only [List.map_append,List.map_cons,List.map_map,List.mem_append,List.mem_cons,
      List.map_nil,List.not_mem_nil,Set.mem_singleton_iff,Function.comp_def,leftRef,rightRef]
    tauto
  have oldMember : (owner,ref) ∈ ownedRefs forest := by
    have extended : (owner,ref) ∈ ownedRefs (forest ++ [⟨target,freshTitle target⟩]) := by rw [old]; simp
    rw [ownedRefs_create] at extended
    rcases List.mem_append.mp extended with prior | newest
    · exact prior
    · have equal := List.mem_singleton.mp newest
      have refEqual : ref = titleRef target := (Prod.mk.inj equal).2
      rw [refEqual,empty_title_rejects physical target marker empty] at contained
      contradiction
  refine ⟨result,ref.start,accepted,member,⟨(owner,ref),oldMember,rfl,contained⟩,?_⟩
  rw [starts]
  exact split_good good member markerFresh inst

theorem starts_iff (forest : Forest) (address : Address) :
    address ∈ Starts forest ↔ ∃ ref ∈ forestRefs forest, ref.start = address := by
  have refs := ownedRefs_refs forest
  constructor
  · rintro ⟨owned,member,equal⟩
    exact ⟨owned.2,refs ▸ List.mem_map.mpr ⟨owned,member,rfl⟩,equal⟩
  · rintro ⟨ref,member,equal⟩
    rw [← refs] at member
    obtain ⟨owned,ownedMember,same⟩ := List.mem_map.mp member
    exact ⟨owned,ownedMember,same ▸ equal⟩

/-- Merge moves slices between blocks; the set of slice starts is unchanged. -/
theorem starts_merge (forest : Forest) (source : Nat) (anchor : NotionCoreSliceForest.Anchor)
    (unique : (forest.map Block.id).Nodup) :
    Starts (mergeForest forest source anchor) = Starts forest := by
  ext address
  rw [starts_iff,starts_iff]
  have perm := mergeForest_refs forest source anchor unique
  constructor
  · rintro ⟨ref,member,equal⟩
    exact ⟨ref,perm.subset member,equal⟩
  · rintro ⟨ref,member,equal⟩
    exact ⟨ref,perm.symm.subset member,equal⟩

open NotionCoreMachine
open NotionCoreMachineShape
open NotionCorePayload (BlockKey Transaction)
open NotionCoreMachineMarkerProgress

/-- Label preservation for the actual canonical split transaction. Fresh title,
marker and selected old slice are derived from the existing issuance/replay
proofs, with address-sensitive label preservation on that same result. -/
theorem canonical_split_labels (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreCreatorNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (part : NotionCoreMachinePartition.Partitioned state) (shape : ShapeInvariant state)
    (block inst : BlockKey) (origin : NotionCoreOriginTree.Origin)
    (payload : tx.payload = .split block inst origin)
    (labels : Labels) (good : Good (Starts state.forest) labels) :
    ∃ result nextLabels, applyTransaction state tx = some result ∧ Good (Starts result.forest) nextLabels ∧
      ∃ owned ∈ ownedRefs state.forest, contains (physical result) owned.2
        (NotionCorePhysicalReplay.address (blockName inst) tx.id) = true ∧
        nextLabels = splitLabels (addRootLabels labels (blockName (.issued tx.id))) owned.2.start
          (NotionCorePhysicalReplay.address (blockName inst) tx.id) := by
  obtain ⟨created,rows,createStep,integrated,stage,rawForest,emptyTarget,_⟩ :=
    canonical_split_marker_phase_version network reachable version closed pre suffix tx position state accepted
      part block inst origin payload
  let raw := putInstance created (blockName inst) {getInstance created (blockName inst) with rows := rows}
  let marker := NotionCorePhysicalReplay.address (blockName inst) tx.id
  let target := blockName (.issued tx.id)
  obtain ⟨freshInstance,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
    network reachable version closed pre suffix tx position state accepted
  have freshTarget : target ∉ state.forest.map Block.id := by
    intro member
    obtain ⟨old,member,equal⟩ := List.mem_map.mp member
    exact freshBlock.1 old member equal
  have freshMarker : FreshMarker state.forest marker := by
    intro old member key
    obtain ⟨ref,inTree,equal⟩ := List.mem_map.mp key
    have oldMember : old ∈ raw.forest := by rw [rawForest]; exact List.mem_append_left _ member
    exact stage.fresh (old.id,ref)
      (List.mem_flatMap.mpr ⟨old,oldMember,List.mem_map.mpr ⟨ref,inTree,rfl⟩⟩) equal
  have existsInstance : ∃ entry ∈ raw.instances, entry.1 = marker.1 := by
    by_cases present : created.instances.any (fun entry => entry.1 == blockName inst) = true
    · have old : ∃ entry ∈ created.instances, entry.1 = blockName inst := by simpa using present
      exact (NotionCoreMachinePartitionUpdates.putInstance_exists_iff created
        (blockName inst) (blockName inst) _ old).mpr old
    · simp [raw,putInstance,present,marker,NotionCorePhysicalReplay.address]
  have present : marker ∈ (physical raw marker.1).map NotionCoreSource.Atom.address :=
    List.mem_map.mpr ⟨NotionCorePartition.boundary marker,stage.present,rfl⟩
  obtain ⟨old,member,ref,refMember,contained⟩ :=
    NotionCoreMachinePartition.containing_tree_ref raw stage.partitioned stage.unique marker existsInstance present stage.fresh
  have witness : ∃ old ∈ state.forest, ∃ ref ∈ preorderTree old.title, contains (physical raw) ref marker = true := by
    rw [rawForest] at member
    rcases List.mem_append.mp member with prior | newest
    · exact ⟨old,prior,ref,refMember,contained⟩
    · have equal := List.mem_singleton.mp newest
      subst old
      have refEq : ref = titleRef target := by simpa [freshTitle,preorderTree,preorderChildren] using refMember
      rw [refEq,empty_title_rejects _ target marker emptyTarget] at contained
      contradiction
  have rootGood := create_labels state part labels good target freshInstance
  have markerFresh : marker ∉ Starts (state.forest ++ [⟨target,freshTitle target⟩]) := by
    intro member
    obtain ⟨owned,member,equal⟩ := member
    exact stage.fresh owned (by simpa only [rawForest] using member) equal
  obtain ⟨forest,selected,atomic,_,selectedRef,finalLabels⟩ := atomicSplit_labels (physical raw) marker target state.forest
    (fun found member => (shape.1 found member).1) freshMarker freshTarget emptyTarget witness (addRootLabels labels target) rootGood markerFresh
  refine ⟨{raw with forest := forest},splitLabels (addRootLabels labels target) selected marker,
    split_transaction_of_atomic state created tx block inst origin rows forest payload createStep
      integrated stage rawForest atomic,finalLabels,?_⟩
  obtain ⟨owned,member,equal,contained⟩ := selectedRef
  exact ⟨owned,member,by simpa [physical] using contained,by rw [equal]⟩

private theorem insert_forest (state result : NotionCoreMachine.State) (block inst : BlockKey)
    (first : NotionRunAllocation.Id) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (accepted : applyOperation state (.insert block inst first origin atoms) = some result) :
    result.forest = state.forest := by
  cases rows : integrateRows (getInstance state (blockName inst)).rows
      (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun item => decide (item ∈ (getInstance state (blockName inst)).pending)))) with
  | none => simp [applyOperation,rows] at accepted
  | some table =>
    have equal : result = putInstance state (blockName inst)
        {getInstance state (blockName inst) with rows := table} := by
      simpa [applyOperation,rows] using accepted.symm
    rw [equal]
    unfold putInstance
    split <;> rfl

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

/-- The source label lifecycle, attached to actual interpreter states. Split
routing witnesses an old stored ref containing the newly integrated marker. -/
def Update (state result : NotionCoreMachine.State) (tx : Transaction)
    (labels nextLabels : Labels) : Prop := match tx.payload with
  | .bootstrap _ => nextLabels = addRootLabels labels 0
  | .create _ => nextLabels = addRootLabels labels (blockName (.issued tx.id))
  | .insert .. | .erase .. | .merge .. => nextLabels = labels
  | .split _ inst _ => ∃ owned ∈ ownedRefs state.forest,
      contains (physical result) owned.2 (NotionCorePhysicalReplay.address (blockName inst) tx.id) = true ∧
      nextLabels = splitLabels (addRootLabels labels (blockName (.issued tx.id))) owned.2.start
        (NotionCorePhysicalReplay.address (blockName inst) tx.id)

inductive LabeledReplay : List Transaction → NotionCoreMachine.State → Labels → Prop
  | initial : LabeledReplay [] {} (fun _ => [])
  | step {txs state labels tx result nextLabels} : LabeledReplay txs state labels →
      applyTransaction state tx = some result → Update state result tx labels nextLabels →
      LabeledReplay (txs ++ [tx]) result nextLabels

/-- Every actual accepted canonical step has a source-lifecycle labeling. Honest
replay supplies the acceptance used here; no label guard is added to issuance. -/
theorem canonical_labels_step (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction) (tx : Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix)
    (state result : NotionCoreMachine.State) (accepted : replay {} pre = some state)
    (operation : applyTransaction state tx = some result)
    (labels : Labels) (good : Good (Starts state.forest) labels) :
    ∃ nextLabels, Good (Starts result.forest) nextLabels ∧ Update state result tx labels nextLabels := by
  obtain ⟨checked,checkedReplay,part,shape,rootActive⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed pre (tx :: suffix) position
  have same : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  have creator := NotionCoreMachineNetwork.creator_reachable reachable
  cases payload : tx.payload with
  | bootstrap atoms =>
    have txEq := NotionCoreBootstrapProvenance.canonical_bootstrap_transaction_version
      network creator version pre suffix tx position atoms payload
    obtain ⟨freshInst,freshBlock⟩ := NotionCoreBootstrapProvenance.canonical_bootstrap_fresh_version
      network creator version closed pre suffix tx position atoms payload state accepted
    obtain ⟨next,step,_,forest,_⟩ := NotionCoreMachineBootstrap.fresh_bootstrap_preserves state atoms part freshInst freshBlock
    have equal : next = result := Option.some.inj (step.symm.trans (txEq ▸ operation))
    subst next
    refine ⟨addRootLabels labels 0,?_,?_⟩
    · rw [forest]
      exact create_labels state part labels good 0 freshInst
    · simp [Update,payload]
  | create afterBlock =>
    have op : applyOperation state (.create (.issued tx.id) afterBlock) = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using operation
    obtain ⟨freshInst,freshBlock⟩ := NotionCoreMachineCanonicalCreate.canonical_destination_fresh_version
      network creator version closed pre suffix tx position state accepted
    have forest := (NotionCoreMachineCanonicalCreate.fresh_create_shape state result (.issued tx.id) afterBlock
      freshInst freshBlock op).2.1
    refine ⟨addRootLabels labels (blockName (.issued tx.id)),?_,?_⟩
    · rw [forest]
      exact create_labels state part labels good _ freshInst
    · simp [Update,payload]
  | insert block inst origin atoms =>
    have op : applyOperation state (.insert block inst tx.id origin atoms) = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations] using operation
    refine ⟨labels,?_,?_⟩
    · rw [insert_forest state result block inst tx.id origin atoms op]
      exact good
    · simp [Update,payload]
  | erase block groups =>
    have ops : applyOperations state (groups.map fun group => .erase block group.1 group.2) = some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload] using operation
    refine ⟨labels,?_,?_⟩
    · rw [erase_groups_forest state result block groups ops]
      exact good
    · simp [Update,payload]
  | merge source inst stop =>
    have op : some {state with forest := mergeForest state.forest (blockName source) (mergeAnchor inst stop)} =
        some result := by
      simpa [applyTransaction,NotionCorePayload.operations,payload,applyOperations,applyOperation] using operation
    refine ⟨labels,?_,?_⟩
    · rw [← Option.some.inj op]
      change Good (Starts (mergeForest state.forest _ _)) labels
      rw [starts_merge state.forest _ _ shape.2.1]
      exact good
    · simp [Update,payload]
  | split block inst origin =>
    obtain ⟨next,nextLabels,step,goodNext,lifecycle⟩ := canonical_split_labels network creator version closed
      pre suffix tx position state accepted part shape block inst origin payload labels good
    have equal : next = result := Option.some.inj (step.symm.trans operation)
    refine ⟨nextLabels,equal ▸ goodNext,?_⟩
    simpa only [Update,payload,equal] using lifecycle

private theorem replay_append (state : NotionCoreMachine.State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a >>= fun next => replay next b) := by
  induction a generalizing state with
  | nil => rfl
  | cons tx rest ih =>
    simp only [List.cons_append,replay]
    cases step : applyTransaction state tx <;> simp [ih]

/-- Duplicate-label exclusion at every actual prefix of every closed version of
an honest archive. Successful interpreter replay is derived independently. -/
theorem honest_prefix_labels (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix) :
    ∃ state labels, replay {} pre = some state ∧ Good (Starts state.forest) labels ∧
      LabeledReplay pre state labels := by
  induction pre using List.reverseRecOn generalizing suffix with
  | nil =>
    refine ⟨{},fun _ => [],rfl,⟨?_,?_⟩,LabeledReplay.initial⟩ <;> simp [Starts,ownedRefs]
  | append_singleton pre tx ih =>
    have earlier : NotionCoreReconstruction.transactionsFor network version = pre ++ tx :: suffix := by
      simpa [List.append_assoc] using position
    obtain ⟨state,labels,replayed,good,labeled⟩ := ih (tx :: suffix) earlier
    obtain ⟨result,resultReplay,_,_,_⟩ :=
      NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed
        (pre ++ [tx]) suffix position
    have op : applyTransaction state tx = some result := by
      rw [replay_append,replayed] at resultReplay
      simpa [replay] using resultReplay
    obtain ⟨nextLabels,nextGood,lifecycle⟩ := canonical_labels_step network reachable version closed pre suffix tx earlier
      state result replayed op labels good
    exact ⟨result,nextLabels,resultReplay,nextGood,LabeledReplay.step labeled op lifecycle⟩

private theorem starts_sublist (state : NotionCoreMachine.State) (refs : List (Nat × Ref)) :
    List.Sublist (refs.map (fun owned => owned.2.start))
      (refs.flatMap (fun owned => NotionCoreMachineDocumentInvariant.intervalAddresses state owned.2)) := by
  induction refs with
  | nil => simp
  | cons owned rest ih =>
    simp only [List.map_cons,List.flatMap_cons,NotionCoreMachineDocumentInvariant.intervalAddresses,List.cons_append]
    exact (ih.trans (List.sublist_append_right _ _)).cons₂ _

def mappingKeys (forest : Forest) (labels : Labels) : List (Nat × List Nat) :=
  (ownedRefs forest).map (fun owned => (owned.2.start.1, labels owned.2.start))

/-- The runtime mapping iterates nodes, not a set. Actual partition/physical
uniqueness rules out duplicate addresses, and Good rules out different-address
label collisions; together they establish multiplicity-sensitive key Nodup. -/
theorem mapping_keys_unique (state : NotionCoreMachine.State)
    (part : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map NotionCoreSource.Atom.address).Nodup)
    (labels : Labels) (good : Good (Starts state.forest) labels) :
    (mappingKeys state.forest labels).Nodup := by
  have startsND := (starts_sublist state (ownedRefs state.forest)).nodup
    (NotionCoreMachineDocumentInvariant.all_addresses_unique state part unique)
  have refsND := List.Nodup.of_map (fun owned : Nat × Ref => owned.2.start) startsND
  apply List.Nodup.map_on _ refsND
  intro a ha b hb same
  have addr : a.2.start = b.2.start := no_collision (starts := Starts state.forest) (labels := labels) (a := a.2.start) (b := b.2.start) good ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    (Prod.mk.inj same).1 (Prod.mk.inj same).2
  exact List.inj_on_of_nodup_map startsND ha hb addr

/-- Every honest closed-version prefix admits the literal source-lifecycle
labels with no duplicate runtime mapping key. The remaining external boundary
is extracting this ghost labeling from JavaScript strings and node fields. -/
theorem honest_mapping_guard (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (version : List NotionRunAllocation.Run)
    (closed : NotionCoreIssuance.Closed (NotionCorePayloadNetwork.forget network).records version)
    (pre suffix : List Transaction)
    (position : NotionCoreReconstruction.transactionsFor network version = pre ++ suffix) :
    ∃ state labels, replay {} pre = some state ∧ Good (Starts state.forest) labels ∧
      (mappingKeys state.forest labels).Nodup ∧ LabeledReplay pre state labels := by
  obtain ⟨state,labels,accepted,good,labeled⟩ := honest_prefix_labels network reachable version closed pre suffix position
  obtain ⟨checked,checkedReplay,part,_,_⟩ :=
    NotionCoreMachineHonestReplay.honest_prefix_reconstruct_version network reachable version closed pre suffix position
  have equal : checked = state := Option.some.inj (checkedReplay.symm.trans accepted)
  subst checked
  have unique := NotionCoreMachineVersionTables.version_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)) version closed pre suffix position state accepted
  exact ⟨state,labels,accepted,good,mapping_keys_unique state part unique labels good,labeled⟩

namespace SPOT
private def marker : Address := (0,.event (0,1))
private def before : Forest := [⟨0,freshTitle 0⟩]
private def physical (inst : Nat) : List NotionCoreSource.Atom :=
  if inst = 0 then [NotionCorePartition.boundary (0,.start),NotionCorePartition.boundary marker]
  else emptyPhysical inst
private def after : Forest := [⟨0,.node ⟨(0,.start),some marker⟩ .nil⟩,
  ⟨1,.node (titleRef 1) (.cons (.node ⟨marker,none⟩ .nil) .nil)⟩]
private def labels : Labels := splitLabels (addRootLabels (fun _ => []) 1) (0,.start) marker

/-- Hand-derived literal atomic split and labels: the moved right interval keeps
R; the unused fresh title is root in its own instance. No constant-label guard. -/
theorem split_label_control : atomicSplit physical marker 1 before = some after ∧
    labels (0,.start) = [15] ∧ labels marker = [47] ∧ labels (1,.start) = [] ∧
    labels marker ≠ labels (0,.start) ∧ (mappingKeys after labels).Nodup ∧
    ¬ (mappingKeys after (fun _ => [])).Nodup := by decide
end SPOT

#print axioms no_collision
#print axioms split_good
#print axioms atomicSplit_labels
#print axioms canonical_split_labels
#print axioms honest_prefix_labels
#print axioms honest_mapping_guard
end Sal.MRDTs.Instances.NotionCoreMachineSearchLabels
