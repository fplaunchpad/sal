import Sal.MRDTs.Instances.NotionCoreMachineDisplay
import Sal.MRDTs.Instances.NotionCoreMachinePartition
import Sal.MRDTs.Instances.NotionCoreMachineDeleteTotal
import Sal.MRDTs.Instances.NotionCoreSourceDocument

/-! Same-state materialization into the source document, in actual DISPLAY
order. A stored block materializes every slice of its chain in preorder; a
display entry whose block has been merged away materializes as a tombstone
with no slices. This is a projection, not a new interpreter. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineDocument
open NotionCoreMachine
open NotionCoreSource (Atom Slice Block)

/-- A stored block keeps its name, its own instance and every extracted slice
of its chain. -/
def materializeBlock (state : State) (block : NotionCoreSliceForest.Block) : Option Block := do
  let slices ← NotionCoreMachineClient.materialize state block.title
  pure ⟨block.id, block.id, slices⟩

/-- A display entry materializes its stored block, or a tombstone when the
block has been merged away. -/
def materializeEntry (state : State) (bid : Nat) : Option Block :=
  match state.forest.find? (fun block => block.id == bid) with
  | some block => materializeBlock state block
  | none => some ⟨bid, bid, []⟩

def materializeDocument (state : State) : Option NotionCoreSourceDocument.Document :=
  state.display.mapM (materializeEntry state)

theorem materialized_slices (state : State) (block : NotionCoreSliceForest.Block) (source : Block)
    (accepted : materializeBlock state block = some source) :
    NotionCoreMachineClient.materialize state block.title = some source.slices ∧
      source.id = block.id ∧ source.inst = block.id := by
  cases selected : NotionCoreMachineClient.materialize state block.title with
  | none => simp [materializeBlock, selected] at accepted
  | some slices =>
    simp [materializeBlock, selected] at accepted
    subst source
    exact ⟨rfl, rfl, rfl⟩

theorem materializeEntry_stored (state : State) (bid : Nat) (block : NotionCoreSliceForest.Block)
    (found : state.forest.find? (fun old => old.id == bid) = some block) :
    materializeEntry state bid = materializeBlock state block := by
  simp [materializeEntry, found]

theorem materializeEntry_tombstone (state : State) (bid : Nat)
    (absent : state.forest.find? (fun old => old.id == bid) = none) :
    materializeEntry state bid = some ⟨bid, bid, []⟩ := by
  simp [materializeEntry, absent]

theorem atom_slots_text (atoms : List Atom) :
    NotionCoreSpec.text (atoms.map Atom.slot) = atoms.flatMap atomText := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    cases atom with
    | mk address kind => cases kind with
      | split => simp [Atom.slot,atomText,ih]
      | text value deleted => cases deleted <;> simp [Atom.slot,atomText,ih]

theorem slice_text (slice : Slice) :
    NotionCoreSpec.text slice.slots = slice.atoms.flatMap atomText := by
  simp [Slice.slots, Slice.anchor, atom_slots_text]

theorem projected_text (source : Block) :
    NotionCoreSpec.text source.project.slots =
      (source.slices.flatMap Slice.atoms).flatMap atomText := by
  simp only [NotionCoreSourceDocument.project_slots, Block.slots]
  induction source.slices with
  | nil => rfl
  | cons slice rest ih => simp [ih, slice_text]

private theorem mapM_atoms (state : State) (refs : List NotionCoreSliceForest.Ref) (slices : List Slice)
    (accepted : refs.mapM (fun ref => do pure (⟨ref.start, ← sliceAtoms state ref⟩ : Slice)) = some slices) :
    refs.mapM (sliceAtoms state) = some (slices.map Slice.atoms) ∧ slices.length = refs.length := by
  induction refs generalizing slices with
  | nil => simp at accepted; subst slices; simp
  | cons ref rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨head, headRead, laterRead⟩ := Option.bind_eq_some_iff.mp accepted
    cases extracted : sliceAtoms state ref with
    | none => simp [extracted] at headRead
    | some atoms =>
      have headEq : head = ⟨ref.start, atoms⟩ := by simpa [extracted] using headRead.symm
      subst head
      obtain ⟨tail, following, same⟩ := Option.bind_eq_some_iff.mp laterRead
      have equal := Option.some.inj same
      subst slices
      obtain ⟨atomsTail, lengthTail⟩ := ih tail following
      simp [List.mapM_cons, extracted, atomsTail, lengthTail]

/-- Checked extraction of every slice gives the tree's atoms in preorder. -/
theorem materialized_tree_atoms (state : State) (block : NotionCoreSliceForest.Block) (source : Block)
    (accepted : materializeBlock state block = some source) :
    treeAtoms state block.title = some (source.slices.flatMap Slice.atoms) := by
  have extracted := (materialized_slices state block source accepted).1
  have atoms := (mapM_atoms state _ _ extracted).1
  simp [treeAtoms, atoms, List.flatMap_def]

/-- Checked chain extraction produces the same block text as the independently
defined document projection. -/
theorem materialized_block_text (state : State) (block : NotionCoreSliceForest.Block) (source : Block)
    (found : state.forest.find? (fun old => old.id == block.id) = some block)
    (accepted : materializeBlock state block = some source) :
    blockText state block.id = some (NotionCoreSpec.text source.project.slots) := by
  have tree := materialized_tree_atoms state block source accepted
  rw [projected_text]
  simp [blockText, found, tree]

/-- A stored block materializes alive. -/
theorem materialized_alive (state : State) (block : NotionCoreSliceForest.Block) (source : Block)
    (accepted : materializeBlock state block = some source) : source.alive = true := by
  have extracted := (materialized_slices state block source accepted).1
  have length := (mapM_atoms state _ _ extracted).2
  rw [NotionCoreSliceForest.preorderTree_eq] at length
  cases slices : source.slices with
  | nil => simp [slices] at length
  | cons _ _ => simp [Block.alive, slices]

private theorem entry_render (state : State) (bid : Nat) (source : Block)
    (accepted : materializeEntry state bid = some source) :
    source.id = bid ∧
    (source.alive = true ↔ (state.forest.any fun block => block.id == bid) = true) ∧
    (source.alive = true → blockText state bid = some (NotionCoreSpec.text source.project.slots)) := by
  cases found : state.forest.find? (fun old => old.id == bid) with
  | none =>
    rw [materializeEntry_tombstone state bid found] at accepted
    cases accepted
    refine ⟨rfl, ?_, fun dead => by simp [Block.alive] at dead⟩
    simp only [Block.alive, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, false_iff]
    intro present
    obtain ⟨block, member, equal⟩ := List.any_eq_true.mp present
    exact List.find?_eq_none.mp found block member equal
  | some block =>
    rw [materializeEntry_stored state bid block found] at accepted
    have name : block.id = bid := by simpa using List.find?_some found
    have parts := materialized_slices state block source accepted
    refine ⟨parts.2.1.trans name, ?_, ?_⟩
    · have present : (state.forest.any fun old => old.id == bid) = true :=
        List.any_eq_true.mpr ⟨block, List.mem_of_find?_eq_some found, by simp [name]⟩
      simp [present, materialized_alive state block source accepted]
    · intro _
      rw [← name]
      exact materialized_block_text state block source (name ▸ found) accepted

/-- Successful display-ordered materialization implies exact actual rendering:
merged-away display entries are tombstones on both sides. No rendering
equation or observation match is supplied as a premise. -/
theorem materialized_render (state : State) (document : NotionCoreSourceDocument.Document)
    (accepted : materializeDocument state = some document) :
    render state = some (NotionCoreSpec.view (NotionCoreSourceDocument.project document)) := by
  have sequence : ∀ (ids : List Nat) (doc : List Block),
      ids.mapM (materializeEntry state) = some doc →
      (ids.filter fun bid => state.forest.any fun block => block.id == bid).mapM
          (fun bid => do pure (bid, ← blockText state bid)) =
        some (NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) := by
    intro ids
    induction ids with
    | nil => intro doc h; simp at h; subst doc; rfl
    | cons bid rest ih =>
      intro doc h
      cases first : materializeEntry state bid with
      | none => simp [List.mapM_cons, first] at h
      | some source =>
        cases tail : rest.mapM (materializeEntry state) with
        | none => simp [List.mapM_cons, first, tail] at h
        | some suffix =>
          have same : source :: suffix = doc := by simpa [List.mapM_cons, first, tail] using h
          subst doc
          obtain ⟨name, alive, text⟩ := entry_render state bid source first
          have following := ih suffix tail
          by_cases present : (state.forest.any fun block => block.id == bid) = true
          · have live := alive.mpr present
            simp only [List.filter_cons, present, ↓reduceIte, List.mapM_cons, text live, following]
            simp [NotionCoreSpec.view, NotionCoreSourceDocument.project, live, name]
          · have dead : source.alive = false := by
              cases h : source.alive
              · rfl
              · exact absurd (alive.mp h) present
            simp only [List.filter_cons, present, Bool.false_eq_true, ↓reduceIte, following]
            simp [NotionCoreSpec.view, NotionCoreSourceDocument.project, dead]
  exact sequence state.display document accepted

theorem materializeBlock_total (state : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup)
    (block : NotionCoreSliceForest.Block) (member : block ∈ state.forest) :
    ∃ source, materializeBlock state block = some source := by
  obtain ⟨slices, materialized⟩ :=
    NotionCoreMachineDeleteTotal.materialize_total state partitioned unique block member
  exact ⟨⟨block.id, block.id, slices⟩, by simp [materializeBlock, materialized]⟩

/-- Represented endpoints make materialization total, tombstones included;
no successful projection or rendering result is assumed. -/
theorem materializeDocument_total (state : State)
    (partitioned : NotionCoreMachinePartition.Partitioned state)
    (unique : ∀ inst, ((physical state inst).map Atom.address).Nodup) :
    ∃ document, materializeDocument state = some document := by
  have each : ∀ bid ∈ state.display, ∃ source, materializeEntry state bid = some source := by
    intro bid _
    cases found : state.forest.find? (fun old => old.id == bid) with
    | none => exact ⟨_, materializeEntry_tombstone state bid found⟩
    | some block =>
      rw [materializeEntry_stored state bid block found]
      exact materializeBlock_total state partitioned unique block (List.mem_of_find?_eq_some found)
  have sequence : ∀ ids : List Nat,
      (∀ bid ∈ ids, ∃ source, materializeEntry state bid = some source) →
      ∃ doc, ids.mapM (materializeEntry state) = some doc := by
    intro ids
    induction ids with
    | nil => intro _; exact ⟨[], rfl⟩
    | cons bid rest ih =>
      intro possible
      obtain ⟨source, head⟩ := possible bid (by simp)
      obtain ⟨suffix, tail⟩ := ih (fun name member => possible name (List.mem_cons_of_mem _ member))
      exact ⟨source :: suffix, by rw [List.mapM_cons, head, tail]; rfl⟩
  exact sequence state.display each

theorem materialized_named_id (state : State) (bid : Nat) (source : Block)
    (accepted : materializeEntry state bid = some source) : source.id = bid :=
  (entry_render state bid source accepted).1

theorem materialized_ids (state : State) (document : NotionCoreSourceDocument.Document)
    (accepted : materializeDocument state = some document) : document.map Block.id = state.display := by
  have sequence : ∀ (ids : List Nat) (doc : List Block),
      ids.mapM (materializeEntry state) = some doc → doc.map Block.id = ids := by
    intro ids
    induction ids with
    | nil => intro doc h; simp at h; subst doc; rfl
    | cons bid rest ih =>
      intro doc h
      cases first : materializeEntry state bid with
      | none => simp [List.mapM_cons, first] at h
      | some source =>
        cases tail : rest.mapM (materializeEntry state) with
        | none => simp [List.mapM_cons, first, tail] at h
        | some suffix =>
          have same : source :: suffix = doc := by simpa [List.mapM_cons, first, tail] using h
          subst doc
          simp [materialized_named_id state bid source first, ih suffix tail]
  exact sequence state.display document accepted

/-- Honest actual reconstruction admits this same-state source-document
projection and agrees with its independent semantic observation. No transition
simulation or document-history refinement is claimed by this endpoint theorem. -/
theorem honest_document (network : NotionCorePayloadNetwork.State)
    (reachable : NotionCoreMachineNetwork.Reach network) (peer : NotionRunAllocation.Session) :
    ∃ state document, NotionCoreReconstruction.reconstruct network peer = some state ∧
      materializeDocument state = some document ∧
      render state = some (NotionCoreSpec.view (NotionCoreSourceDocument.project document)) := by
  obtain ⟨state,accepted,part,_,_⟩ :=
    NotionCoreMachineHonestReplay.honest_reconstruct network reachable peer
  have unique := NotionCoreMachineMarkerProgress.canonical_physical_unique_all network
    (NotionCoreCreatorNetwork.payload_reachable (NotionCoreMachineNetwork.creator_reachable reachable)) peer
    (NotionCoreReconstruction.transactions network peer) [] (by simp) state accepted
  obtain ⟨document,materialized⟩ := materializeDocument_total state part unique
  exact ⟨state,document,accepted,materialized,materialized_render state document materialized⟩

private def cut : NotionCorePayload.Transaction :=
  ⟨⟨3,[83]⟩,.split .initial .initial (.item ⟨1,[65]⟩)⟩
private def fixture := replay {} [NotionCorePayload.bootstrap [97,98],cut]

/-- Literal split fixture retains the destination's empty title root in the
projected slots while its visible text is only the inherited b. -/
theorem projection_control :
    (fixture >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) =
        some [(0,[97]),(blockName (.issued ⟨3,[83]⟩),[98])] ∧
    (fixture >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) ≠
        some [(0,[97,98]),(blockName (.issued ⟨3,[83]⟩),[])] := by decide +kernel

private def back : NotionCorePayload.Transaction := ⟨⟨4,[83]⟩,.merge (.issued ⟨3,[83]⟩) .initial⟩
private def merged := replay {} [NotionCorePayload.bootstrap [97,98],cut,back]

/-- After the split destination is merged back, its display entry is a
tombstone and the absorbing block's chain projects both halves, ab. -/
theorem merge_projection_control :
    (merged >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) =
        some [(0,[97,98])] ∧
    (merged >>= materializeDocument).map (fun doc => doc.map Block.alive) = some [true,false] ∧
    (merged >>= materializeDocument).map
      (fun doc => NotionCoreSpec.view (NotionCoreSourceDocument.project doc)) ≠
        some [(0,[97]),(blockName (.issued ⟨3,[83]⟩),[98])] := by decide +kernel

#print axioms honest_document
#print axioms materializeDocument_total
#print axioms materialized_ids
#print axioms projection_control
#print axioms merge_projection_control
#print axioms materialized_tree_atoms
#print axioms materialized_render
end Sal.MRDTs.Instances.NotionCoreMachineDocument
