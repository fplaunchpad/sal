import Sal.MRDTs.Instances.NotionCoreMachineDisplay
import Sal.MRDTs.Instances.NotionCoreMachinePartition
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! Same-state materialization into the existing source document, in actual
DISPLAY order. This is a projection, not a new interpreter. Transition/history
refinement and absence of pending tombstones at honest fresh births are separate. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocument
open NotionCoreMachine
open NotionCoreSliceForest (Normal NormalForest attached active profile)
open NotionCoreSource (Atom Slice Block)

/-- Retain the unused own-title anchor through the existing attached shape. -/
def materializeBlock (state : State) (block : NotionCoreSliceForest.Block) : Option Block := do
  let ref := active block.title
  let atoms ← sliceAtoms state ref
  pure ⟨block.id,if attached block.title then .attached block.id else .own,⟨ref.start,atoms⟩⟩

def materializeDocument (state : State) : Option NotionCoreSourceDocument.Document :=
  state.display.mapM fun bid => do
    let block ← state.forest.find? (fun block => block.id == bid)
    materializeBlock state block

theorem materialized_atoms (state : State) (block : NotionCoreSliceForest.Block) (source : Block)
    (accepted : materializeBlock state block = some source) :
    sliceAtoms state (active block.title) = some source.active.atoms ∧ source.id = block.id := by
  cases selected : sliceAtoms state (active block.title) with
  | none => simp [materializeBlock,selected] at accepted
  | some atoms =>
    simp [materializeBlock,selected] at accepted
    subst source
    exact ⟨rfl,rfl⟩

theorem atom_slots_text (atoms : List Atom) :
    NotionCoreSpec.text (atoms.map Atom.slot) = atoms.flatMap atomText := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    cases atom with
    | mk address kind => cases kind with
      | split => simp [Atom.slot,atomText,ih]
      | text value deleted => cases deleted <;> simp [Atom.slot,atomText,ih]

theorem projected_text (source : Block) :
    NotionCoreSpec.text source.project.slots = source.active.atoms.flatMap atomText := by
  cases source with
  | mk id shape slice =>
    cases shape <;> simp [Block.project,Slice.slots,Slice.anchor,NotionCoreSpec.root,atom_slots_text]

theorem materialized_tree_atoms (state : State) (block : NotionCoreSliceForest.Block) (source : Block)
    (normal : Normal block.id block.title)
    (empty : attached block.title = true → physical state block.id = NotionCoreSliceForest.emptyPhysical block.id)
    (titleExists : attached block.title = true → state.instances.any (fun entry => entry.1 == block.id) = true)
    (accepted : materializeBlock state block = some source) :
    treeAtoms state block.title = some source.active.atoms := by
  have extracted := (materialized_atoms state block source accepted).1
  cases block with
  | mk bid tree =>
    change Normal bid tree at normal
    cases normal with
    | own stop =>
      simp only [active,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice] at extracted
      simp [treeAtoms,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
        extracted]
    | attached ref =>
      have root := NotionCoreMachineSlices.empty_title_atoms state bid (titleExists rfl) (empty rfl)
      simp only [active,NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice] at extracted
      simp [treeAtoms,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,root,extracted]

/-- Checked active extraction plus empty-title preservation produces the same
block text as the independently defined existing document projection. -/
theorem materialized_block_text (state : State) (block : NotionCoreSliceForest.Block) (source : Block)
    (found : state.forest.find? (fun old => old.id == block.id) = some block)
    (normal : Normal block.id block.title)
    (empty : attached block.title = true → physical state block.id = NotionCoreSliceForest.emptyPhysical block.id)
    (titleExists : attached block.title = true → state.instances.any (fun entry => entry.1 == block.id) = true)
    (accepted : materializeBlock state block = some source) :
    blockText state block.id = some (NotionCoreSpec.text source.project.slots) := by
  have tree := materialized_tree_atoms state block source normal empty titleExists accepted
  simp [blockText,found,tree,projected_text]

private theorem selected_block_text (state : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (normal : NormalForest state.forest)
    (empty : NotionCoreSliceForest.EmptyInactive (physical state) (profile state.forest))
    (bid : Nat) (source : Block)
    (accepted : (do let block ← state.forest.find? (fun old : NotionCoreSliceForest.Block => old.id == bid)
                    materializeBlock state block) = some source) :
    (do pure (bid, ← blockText state bid)) = some (source.id,NotionCoreSpec.text source.project.slots) := by
  cases found : state.forest.find? (fun old : NotionCoreSliceForest.Block => old.id == bid) with
  | none => simp [found] at accepted
  | some block =>
    have member := List.mem_of_find?_eq_some found
    have name : block.id = bid := by simpa using List.find?_some found
    have decoded : materializeBlock state block = some source := by simpa [found] using accepted
    have rootName : block.title.slice.start.1 = block.id := by
      have statement (bid : Nat) (tree : NotionCoreSliceForest.Tree) (h : Normal bid tree) :
          tree.slice.start.1 = bid := by cases h <;> rfl
      exact statement block.id block.title (normal block member)
    have titleMember : (block.id,block.title.slice) ∈ NotionCoreForestRefs.ownedRefs state.forest := by
      apply List.mem_flatMap.mpr
      refine ⟨block,member,List.mem_map.mpr ⟨block.title.slice,?_,rfl⟩⟩
      cases block.title; simp [NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.Tree.slice]
    have stored : state.instances.any (fun entry => entry.1 == block.id) = true := by
      simpa [rootName] using partitioned.refsExist _ titleMember
    have titleEmpty : attached block.title = true → physical state block.id = NotionCoreSliceForest.emptyPhysical block.id :=
      fun inactive => empty _ (List.mem_map.mpr ⟨block,member,rfl⟩) inactive
    have rendered := materialized_block_text state block source (name ▸ found) (normal block member) titleEmpty
      (fun _ => stored) decoded
    have sourceName := (materialized_atoms state block source decoded).2
    have rendered' : blockText state bid = some (NotionCoreSpec.text source.project.slots) := name ▸ rendered
    rw [rendered']
    simp [sourceName,name]

/-- Successful display-ordered materialization implies exact actual rendering.
No rendering equation or observation match is supplied as a premise. -/
theorem materialized_render (state : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (normal : NormalForest state.forest)
    (empty : NotionCoreSliceForest.EmptyInactive (physical state) (profile state.forest))
    (document : NotionCoreSourceDocument.Document)
    (accepted : materializeDocument state = some document) :
    render state = some (NotionCoreSpec.view (NotionCoreSourceDocument.project document)) := by
  have sequence : ∀ (ids : List Nat) (doc : List Block),
      ids.mapM (fun bid => do
        let block ← state.forest.find? (fun old : NotionCoreSliceForest.Block => old.id == bid)
        materializeBlock state block) = some doc →
      ids.mapM (fun bid => do pure (bid, ← blockText state bid)) =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) := by
    intro ids
    induction ids with
    | nil => intro doc h; simp at h; subst doc; rfl
    | cons bid rest ih =>
      intro doc h
      cases first : (do let block ← state.forest.find? (fun old : NotionCoreSliceForest.Block => old.id == bid)
                        materializeBlock state block) with
      | none =>
        rw [List.mapM_cons,first] at h
        simp at h
      | some source =>
        cases tail : rest.mapM (fun bid => do
            let block ← state.forest.find? (fun old : NotionCoreSliceForest.Block => old.id == bid)
            materializeBlock state block) with
        | none =>
          rw [List.mapM_cons,first,tail] at h
          simp at h
        | some suffix =>
          have same : source :: suffix = doc := by
            rw [List.mapM_cons,first,tail] at h
            simpa using h
          subst doc
          have output := selected_block_text state partitioned normal empty bid source first
          have following := ih suffix tail
          rw [List.mapM_cons,output,following]
          simp [NotionCoreSpec.view,NotionCoreSourceDocument.project]
  exact sequence state.display document accepted

theorem materializeBlock_total (state : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest)
    (normal : Normal block.id block.title) : ∃ source, materializeBlock state block = some source := by
  have activeMember : active block.title ∈ NotionCoreSliceForest.preorderTree block.title := by
    have statement (bid : Nat) (tree : NotionCoreSliceForest.Tree) (h : Normal bid tree) :
        active tree ∈ NotionCoreSliceForest.preorderTree tree := by
      cases h <;> simp [active,NotionCoreSliceForest.preorderTree,NotionCoreSliceForest.preorderChildren,
        NotionCoreSliceForest.Tree.children,NotionCoreSliceForest.Tree.slice]
    exact statement block.id block.title normal
  have owned : (block.id,active block.title) ∈ NotionCoreForestRefs.ownedRefs state.forest :=
    List.mem_flatMap.mpr ⟨block,member,List.mem_map.mpr ⟨active block.title,activeMember,rfl⟩⟩
  obtain ⟨atoms,extracted⟩ := NotionCoreMachinePartition.ref_extracts state partitioned unique _ owned
  exact ⟨⟨block.id,if attached block.title then .attached block.id else .own,
    ⟨(active block.title).start,atoms⟩⟩,by simp [materializeBlock,extracted]⟩

/-- Display alignment and actual represented endpoints make materialization
total; no successful projection or rendering result is assumed. -/
theorem materializeDocument_total (state : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (normal : NormalForest state.forest) (aligned : NotionCoreMachineDisplay.Aligned state) :
    ∃ document, materializeDocument state = some document := by
  have each : ∀ bid ∈ state.display, ∃ source,
      (do let block ← state.forest.find? (fun old => old.id == bid)
          materializeBlock state block) = some source := by
    intro bid displayed
    have named : bid ∈ state.forest.map NotionCoreSliceForest.Block.id := aligned.2.mem_iff.mp displayed
    cases found : state.forest.find? (fun old => old.id == bid) with
    | none =>
      obtain ⟨block,member,equal⟩ := List.mem_map.mp named
      have rejected := List.find?_eq_none.mp found block member
      exact False.elim (rejected (by simpa using equal))
    | some block =>
      have member := List.mem_of_find?_eq_some found
      obtain ⟨source,selected⟩ := materializeBlock_total state partitioned unique block member (normal block member)
      exact ⟨source,by simp [selected]⟩
  have sequence : ∀ ids : List Nat,
      (∀ bid ∈ ids, ∃ source,
        (do let block ← state.forest.find? (fun old => old.id == bid)
            materializeBlock state block) = some source) →
      ∃ doc, ids.mapM (fun bid => do
        let block ← state.forest.find? (fun old => old.id == bid)
        materializeBlock state block) = some doc := by
    intro ids
    induction ids with
    | nil => intro _; exact ⟨[],rfl⟩
    | cons bid rest ih =>
      intro possible
      obtain ⟨source,head⟩ := possible bid (by simp)
      obtain ⟨suffix,tail⟩ := ih (fun name member => possible name (List.mem_cons_of_mem _ member))
      refine ⟨source::suffix,?_⟩
      rw [List.mapM_cons,head,tail]
      rfl
  exact sequence state.display each

theorem materialized_named_id (state : State) (bid : Nat) (source : Block)
    (accepted : (do let block ← state.forest.find? (fun old => old.id == bid)
                    materializeBlock state block) = some source) : source.id = bid := by
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none => simp [found] at accepted
  | some block =>
    have name : block.id = bid := by simpa using List.find?_some found
    have selected : materializeBlock state block = some source := by simpa [found] using accepted
    exact (materialized_atoms state block source selected).2.trans name

theorem materialized_ids (state : State) (document : NotionCoreSourceDocument.Document)
    (accepted : materializeDocument state = some document) : document.map Block.id = state.display := by
  have sequence : ∀ (ids : List Nat) (doc : List Block),
      ids.mapM (fun bid => do
        let block ← state.forest.find? (fun old => old.id == bid)
        materializeBlock state block) = some doc → doc.map Block.id = ids := by
    intro ids
    induction ids with
    | nil => intro doc h; simp at h; subst doc; rfl
    | cons bid rest ih =>
      intro doc h
      cases first : (do let block ← state.forest.find? (fun old : NotionCoreSliceForest.Block => old.id == bid)
                        materializeBlock state block) with
      | none => rw [List.mapM_cons,first] at h; simp at h
      | some source =>
        cases tail : rest.mapM (fun bid => do
            let block ← state.forest.find? (fun old : NotionCoreSliceForest.Block => old.id == bid)
            materializeBlock state block) with
        | none => rw [List.mapM_cons,first,tail] at h; simp at h
        | some suffix =>
          have same : source::suffix = doc := by
            rw [List.mapM_cons,first,tail] at h
            simpa using h
          subst doc
          simp [materialized_named_id state bid source first,ih suffix tail]
  exact sequence state.display document accepted

/-- Honest actual reconstruction admits this same-state source-document
projection and agrees with its independent semantic observation. No transition
simulation or document-history refinement is claimed by this endpoint theorem. -/
theorem honest_document (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session) :
    ∃ state document, NotionCoreReconstruction.reconstruct network peer = some state ∧
      materializeDocument state = some document ∧
      render state = some (NotionCoreSpec.view (NotionCoreSourceDocument.project document)) := by
  obtain ⟨state,accepted,part,shape,_⟩ :=
    NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)) peer
    (NotionCoreReconstruction.transactions network peer) [] (by simp) state accepted
  have aligned := NotionCoreMachineDisplay.reconstructed_aligned network peer state accepted
  obtain ⟨document,materialized⟩ := materializeDocument_total state part unique shape.1 aligned
  exact ⟨state,document,accepted,materialized,materialized_render state part shape.1 shape.2.2 document materialized⟩

private def cut : NotionCorePayload.Transaction :=
  ⟨⟨3,[83]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def fixture := replay {} [NotionCorePayload.bootstrap [97,98],cut]

/-- Literal split fixture retains the attached block's empty own root in the
projected slots while its visible text is only the inherited b. -/
theorem projection_control :
    (fixture >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) =
        some [(0,[97]),(blockName (.issued ⟨3,[83]⟩),[98])] ∧
    (fixture >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) ≠
        some [(0,[97,98]),(blockName (.issued ⟨3,[83]⟩),[])] := by decide +kernel

#print axioms honest_document
#print axioms materializeDocument_total
#print axioms materialized_ids
#print axioms projection_control
#print axioms materialized_tree_atoms
#print axioms materialized_render
end Sal.MRDTs.Instances.NotionCoreMachineDocument
