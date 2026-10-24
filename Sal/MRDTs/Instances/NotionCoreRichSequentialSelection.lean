import Sal.MRDTs.Instances.NotionCoreRichSequentialRefinement
import Sal.MRDTs.Instances.NotionCoreAtomicFormattingPlanner
import Sal.MRDTs.Instances.NotionCoreRichProtocolFormatFacts
import Sal.MRDTs.Instances.NotionCoreRichPlainReach

/-! Clipped Nat positional selections in the repaired typed caller. This
supported API uses before-item/END maximal runs and live displayed blocks.
Unlike the earlier strict selection helper, oversized upper bounds clip.
The cached JavaScript's raw dead-block/negative-index entry points are outside
this typed API; a visible UI selection cannot name a removed block. -/
namespace Sal.MRDTs.Instances.NotionCoreRichSequential.Selection
open NotionCoreRichSequential.Refinement
open NotionCoreSpec
open NotionCoreFormattingSource (Character Positioned)
open NotionCoreOriginTree (preorder)

/-- Independent direct-state positional read, with JavaScript slice's Nat
clipping behavior. Empty/reversed selections remain empty; issuance rejects
those observations. -/
def selectRich (abstract : State) (bid start stop : Nat) : Option (List RichChar) := do
  let view ← render abstract
  let characters ← view.lookup bid
  pure ((characters.drop start).take (stop-start))

def selectedAddresses (abstract : State) (bid start stop : Nat) : Option (List Address) :=
  (selectRich abstract bid start stop).map (List.map (·.address))

def selectedVerdict (abstract : State) (bid start stop : Nat) : Option Bool :=
  (selectRich abstract bid start stop).map (fun characters => !(characters.all (·.bold)))

def coordinate (actual : NotionCoreAtomicFormattingMachine.State) (address : Address) : Nat :=
  ((NotionCoreRichCoordinates.physicalSlots address.1
    (NotionCoreAtomicFormattingMachine.instanceForest actual address.1)).map Slot.address).findIdx?
      (fun old => old == address) |>.getD 0

private theorem mapM_member {α β : Type} (xs : List α) (f : α → Option β) (ys : List β)
    (h : xs.mapM f = some ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; simp at hy
  | cons x rest ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at h
    | some first =>
      cases ht : rest.mapM f with
      | none => simp [List.mapM_cons,hx,ht] at h
      | some tail =>
        have same : first :: tail = ys := by simpa [List.mapM_cons,hx,ht] using h
        subst ys
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x,by simp,hx⟩
        · obtain ⟨z,hz,hf⟩ := ih tail ht hy
          exact ⟨z,by simp [hz],hf⟩

private theorem physical_position (actual : NotionCoreAtomicFormattingMachine.State)
    (inst : Nat) (atom : NotionCoreSource.Atom)
    (physical : atom ∈ NotionCoreMachine.physical actual.core inst)
    (value : Nat) (live : atom.kind = .text value false) :
    ∃ p ∈ NotionCoreFormattingPlanner.visible (NotionCoreAtomicFormattingMachine.instanceForest actual inst),
      NotionCorePhysicalReplay.address inst p.item.id = atom.address := by
  simp only [NotionCoreMachine.physical,NotionCorePhysicalReplay.physical,List.mem_cons,List.mem_map] at physical
  rcases physical with rfl | ⟨item,member,rfl⟩
  · simp [NotionCorePhysicalReplay.start,NotionCorePartition.boundary] at live
  · have hforest : item ∈ preorder (NotionCoreAtomicFormattingMachine.instanceForest actual inst) := by
      rw [NotionCoreAtomicFormattingMachine.instanceForest_traversal]
      exact member
    rw [← NotionCoreFormattingSource.walk_items] at hforest
    obtain ⟨position,hp,equal⟩ := List.mem_map.mp hforest
    have itemlive : item.kind = .text value false := by
      cases hk : item.kind <;> simp_all [NotionCorePhysicalReplay.atom]
    refine ⟨position,List.mem_filter.mpr ⟨hp,?_⟩,?_⟩
    · simp [NotionCoreFormattingPlanner.live,equal,itemlive]
    · simp [equal]

/-- Every displayed live slot has an actual live physical source position.
The source position, registration and identity are derived from materialized
slice extraction rather than supplied as DisplayCoordinates. -/
theorem visible_position {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (block : Block) (hb : block ∈ abstract.document)
    (alive : block.alive = true) (slot : Slot) (hs : slot ∈ block.slots) (live : slot.visible = true) :
    Registered actual slot.address.1 ∧
      ∃ p ∈ NotionCoreFormattingPlanner.visible
          (NotionCoreAtomicFormattingMachine.instanceForest actual slot.address.1),
        NotionCorePhysicalReplay.address slot.address.1 p.item.id = slot.address := by
  obtain ⟨source,hmat,hdoc⟩ := related.document
  rw [hdoc] at hb
  obtain ⟨sourceBlock,hblock,rfl⟩ := List.mem_map.mp hb
  obtain ⟨bid,_,hentry⟩ := mapM_member actual.core.display
    (NotionCoreMachineDocument.materializeEntry actual.core) source hmat hblock
  cases hfound : actual.core.forest.find? (fun old => old.id == bid) with
  | none =>
    rw [NotionCoreMachineDocument.materializeEntry_tombstone actual.core bid hfound] at hentry
    cases hentry
    simp [NotionCoreSource.Block.project,NotionCoreSource.Block.alive] at alive
  | some actualBlock =>
    have hblockmat : NotionCoreMachineDocument.materializeBlock actual.core actualBlock = some sourceBlock := by
      simpa only [NotionCoreMachineDocument.materializeEntry,hfound] using hentry
    have hslices := (NotionCoreMachineDocument.materialized_slices actual.core actualBlock sourceBlock hblockmat).1
    change slot ∈ sourceBlock.slices.flatMap NotionCoreSource.Slice.slots at hs
    obtain ⟨slice,hinslice,hslot⟩ := List.mem_flatMap.mp hs
    simp only [NotionCoreSource.Slice.slots,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hslot
    rcases hslot with hanchor | hatom | hclose
    · subst slot; simp [NotionCoreSource.Slice.anchor] at live
    · obtain ⟨atom,member,rfl⟩ := List.mem_map.mp hatom
      have stored := NotionCoreMachineClient.materialized_storage actual.core _ _ hslices slice hinslice
      have physical := NotionCoreMachineClient.materialized_physical actual.core _ _ hslices slice hinslice
      cases hk : atom.kind with
      | split => simp [NotionCoreSource.Atom.slot,hk] at live
      | text value deleted =>
        cases deleted with
        | true => simp [NotionCoreSource.Atom.slot,hk] at live
        | false =>
          have physicalPosition := physical_position actual slice.start.1 atom (physical.2 atom member) value hk
          have same := stored.2 atom member
          simp only [NotionCoreSource.Atom.slot,hk]
          rw [same]
          exact ⟨stored.1,physicalPosition⟩
    · subst slot; simp [NotionCoreSource.Slice.close] at live

private theorem mem_eraseDups (items : List Nat) (value : Nat) :
    value ∈ items.eraseDups ↔ value ∈ items := by
  have loop : ∀ (rest seen : List Nat),
      value ∈ List.eraseDupsBy.loop (· == ·) rest seen ↔ value ∈ rest ∨ value ∈ seen := by
    intro rest
    induction rest with
    | nil => intro seen; simp [List.eraseDupsBy.loop]
    | cons first rest ih =>
      intro seen
      simp only [List.eraseDupsBy.loop]
      cases found : seen.any (fun old => first == old) with
      | false => simp only [ih,List.mem_cons]; tauto
      | true =>
        have member : first ∈ seen := by
          obtain ⟨old,inside,equal⟩ := List.any_eq_true.mp found
          exact (beq_iff_eq.mp equal) ▸ inside
        simp only [ih,List.mem_cons]
        constructor
        · tauto
        · rintro ((rfl | h) | h)
          · exact Or.inr member
          · exact Or.inl h
          · exact Or.inr h
  simpa only [List.eraseDups,List.eraseDupsBy,List.not_mem_nil,or_false] using loop items []

/-- The generic planner's coordinate premise follows from the global rich
relation, including all unselected visible blocks and moved slice suffixes. -/
theorem displayCoordinates {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) :
    NotionCoreFormattingPlanner.DisplayCoordinates abstract.document
      (NotionCoreAtomicFormattingMachine.instanceForest actual) NotionCorePhysicalReplay.address
      (coordinate actual) ((actual.core.instances.map Prod.fst).eraseDups) := by
  intro block hb alive slot hs live
  obtain ⟨stored,p,hp,identity⟩ := visible_position related block hb alive slot hs live
  obtain ⟨entry,member,same⟩ := stored
  refine ⟨?_,related.unique _,p,hp,identity,?_⟩
  · exact (mem_eraseDups _ _).mpr (List.mem_map.mpr ⟨entry,member,same⟩)
  · have walkMember := (List.mem_filter.mp hp).1
    have hentry := NotionCoreFormattingPlanner.anchor_before_entry _ (related.unique _) p walkMember
    have hposition := NotionCoreRichCoordinates.endpoint_before slot.address.1
      (NotionCoreAtomicFormattingMachine.instanceForest actual slot.address.1) p.item.id (fun _ => false) (fun _ => false)
    rw [hentry] at hposition
    change ((NotionCoreRichCoordinates.physicalSlots slot.address.1
      (NotionCoreAtomicFormattingMachine.instanceForest actual slot.address.1)).map Slot.address).findIdx?
      (fun a => a == NotionCorePhysicalReplay.address slot.address.1 p.item.id) = some p.entry at hposition
    rw [identity] at hposition
    exact congrArg (fun result : Option Nat => result.getD 0) hposition

/-- Exact source coverage on the entire visible document, obtained from
physical provenance and the repaired maximal-run compiler. -/
theorem planned_exact {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (targets : List Address) (priority : NotionRunAllocation.Id) (value : Bool) :
    ∀ block ∈ abstract.document, block.alive = true → ∀ slot ∈ block.slots, slot.visible = true →
      NotionCoreAtomicFormatting.covers (NotionCoreAtomicFormattingMachine.instanceForest actual)
        (NotionCoreAtomicFormatting.planned (NotionCoreAtomicFormattingMachine.instanceForest actual)
          targets ((actual.core.instances.map Prod.fst).eraseDups) priority value)
        slot.address.1 (coordinate actual slot.address) = targets.contains slot.address :=
  NotionCoreAtomicFormatting.planned_exact_coverage _ _ _ _ _ _ _ (displayCoordinates related)

private def neutralAtom (atom : NotionCoreAtomicFormattingMachine.RichAtom) : RichChar :=
  ⟨atom.address,atom.value,atom.bold⟩

private theorem mapM_result_map {α β γ : Type} (items : List α) (f : α → Option β) (g : β → γ) :
    (items.mapM f).map (List.map g) = items.mapM (fun x => (f x).map g) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    rw [List.mapM_cons,List.mapM_cons]
    cases head : f first <;> cases tail : rest.mapM f <;>
      simp only [tail,Option.map_none,Option.map_some] at ih ⊢ <;>
      rw [← ih] <;> rfl

private theorem source_render_blocks (actual : NotionCoreAtomicFormattingMachine.State) :
    NotionCoreAtomicFormattingMachine.render actual =
      (NotionCoreMachine.visible actual.core).mapM (fun bid => do
        pure (bid,← NotionCoreAtomicFormattingMachine.blockRich actual bid)) := by
  unfold NotionCoreAtomicFormattingMachine.render NotionCoreFormattingMachine.render
  change (_ : Option (List (Nat × List NotionCoreFormattingMachine.RichAtom))).map
    (List.map fun (bid,atoms) => (bid,atoms.map (NotionCoreAtomicFormattingMachine.markAtom actual))) = _
  rw [mapM_result_map]
  congr 1
  funext bid
  cases head : NotionCoreFormattingMachine.blockRich (NotionCoreAtomicFormattingMachine.plainState actual) bid <;>
    simp [NotionCoreAtomicFormattingMachine.blockRich,head]

private theorem mapM_lookup {α : Type} (ids : List Nat) (f : Nat → Option α)
    (rows : List (Nat × α)) (assembled : ids.mapM (fun id => do pure (id,← f id)) = some rows)
    (bid : Nat) (present : bid ∈ ids) : rows.lookup bid = f bid := by
  induction ids generalizing rows with
  | nil => simp at present
  | cons first rest ih =>
    cases head : f first with
    | none =>
      have hp : (do pure (first,← f first)) = (none : Option (Nat × α)) := by rw [head]; rfl
      rw [List.mapM_cons,hp] at assembled
      cases assembled
    | some item =>
      cases tail : rest.mapM (fun id => do pure (id,← f id)) with
      | none =>
        have hp : (do pure (first,← f first)) = some (first,item) := by rw [head]; rfl
        rw [List.mapM_cons,hp,tail] at assembled
        cases assembled
      | some later =>
        have hp : (do pure (first,← f first)) = some (first,item) := by rw [head]; rfl
        have same : (first,item)::later = rows := by
          rw [List.mapM_cons,hp,tail] at assembled
          exact Option.some.inj assembled
        subst rows
        by_cases equal : first = bid
        · subst bid; simp [head]
        · have laterMember : bid ∈ rest := (List.mem_cons.mp present).resolve_left (Ne.symm equal)
          simpa only [List.lookup_cons,show (bid == first) = false from beq_eq_false_iff_ne.mpr (Ne.symm equal)]
            using ih later tail laterMember

private theorem neutral_lookup (view : NotionCoreAtomicFormattingMachine.View) (bid : Nat) :
    (NotionCoreRichProtocolCarrier.neutral view).lookup bid =
      (view.lookup bid).map (List.map neutralAtom) := by
  induction view with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨id,atoms⟩
    by_cases equal : id = bid
    · subst bid; simp [NotionCoreRichProtocolCarrier.neutral,neutralAtom]
    · simpa only [NotionCoreRichProtocolCarrier.neutral,List.map_cons,List.lookup_cons,
        show (bid == id) = false from beq_eq_false_iff_ne.mpr (Ne.symm equal)] using ih

/-- Accepted typed reconstruction derives display alignment, so a successful
block read names a live displayed block. No visible-block guard is supplied. -/
theorem selection_block_visible (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (bid : Nat) (atoms : List NotionCoreAtomicFormattingMachine.RichAtom)
    (blockRead : NotionCoreAtomicFormattingMachine.blockRich actual bid = some atoms) :
    bid ∈ NotionCoreMachine.visible actual.core := by
  have projection := NotionCoreRichPlainReach.reconstruct_core network reachable session
  rw [reconstructed,Option.map_some] at projection
  have aligned := NotionCoreMachineDisplay.reconstructed_aligned _ session actual.core projection.symm
  unfold NotionCoreAtomicFormattingMachine.blockRich NotionCoreFormattingMachine.blockRich at blockRead
  cases found : actual.core.forest.find? (fun b => b.id == bid) with
  | none => simp [NotionCoreAtomicFormattingMachine.plainState,found] at blockRead
  | some block =>
    have named : bid ∈ NotionCoreDisplayOrder.names actual.core.forest :=
      List.mem_map.mpr ⟨block,List.mem_of_find?_eq_some found,by simpa using List.find?_some found⟩
    exact aligned.2.2.mem_iff.mpr named

/-- The actual positional block slice and independent rich document slice
have identical full fields. Both use clipping, including oversize bounds. -/
theorem selectRich_block {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (bid start stop : Nat)
    (atoms : List NotionCoreAtomicFormattingMachine.RichAtom)
    (blockRead : NotionCoreAtomicFormattingMachine.blockRich actual bid = some atoms)
    (present : bid ∈ NotionCoreMachine.visible actual.core) :
    selectRich abstract bid start stop =
      some (((atoms.drop start).take (stop-start)).map neutralAtom) := by
  obtain ⟨view,hview,abstractView⟩ := render_total_related related
  have blocks := source_render_blocks actual
  have assembled : (NotionCoreMachine.visible actual.core).mapM (fun id => do
      pure (id,← NotionCoreAtomicFormattingMachine.blockRich actual id)) = some view := by
    rw [← blocks,hview]
  have lookup := mapM_lookup _ _ _ assembled bid present
  rw [blockRead] at lookup
  unfold selectRich
  rw [abstractView]
  simp only [Bind.bind,Option.bind]
  rw [neutral_lookup,lookup]
  simp

private def observation (character : Character) : Address × Bool :=
  (NotionCorePhysicalReplay.address character.textInstance character.item.id,character.bold)

private def rawObservation (atom : NotionCoreAtomicFormattingMachine.RichAtom) : Address × Bool :=
  (atom.address,atom.bold)

private theorem decode_observation (actual : NotionCoreAtomicFormattingMachine.State)
    (atom : NotionCoreAtomicFormattingMachine.RichAtom) (character : Character)
    (decoded : NotionCoreRichProtocolNetwork.decodeCharacter actual atom = some character) :
    observation character = rawObservation atom := by
  unfold NotionCoreRichProtocolNetwork.decodeCharacter at decoded
  obtain ⟨found,located,after⟩ := Option.bind_eq_some_iff.mp decoded
  cases Option.some.inj after
  have identity : NotionCorePhysicalReplay.address atom.address.1 found.item.id = atom.address := by
    simpa using List.find?_some located
  exact Prod.ext identity rfl

private theorem decoded_observations (actual : NotionCoreAtomicFormattingMachine.State)
    (atoms : List NotionCoreAtomicFormattingMachine.RichAtom) (characters : List Character)
    (decoded : atoms.mapM (NotionCoreRichProtocolNetwork.decodeCharacter actual) = some characters) :
    characters.map observation = atoms.map rawObservation := by
  induction atoms generalizing characters with
  | nil => have empty : ([] : List Character) = characters := Option.some.inj decoded; subst characters; rfl
  | cons atom rest ih =>
    cases head : NotionCoreRichProtocolNetwork.decodeCharacter actual atom with
    | none => simp [List.mapM_cons,head] at decoded
    | some character =>
      cases tail : rest.mapM (NotionCoreRichProtocolNetwork.decodeCharacter actual) with
      | none => simp [List.mapM_cons,head,tail] at decoded
      | some later =>
        have same : character::later = characters := by simpa [List.mapM_cons,head,tail] using decoded
        subst characters
        simp only [List.map_cons,decode_observation actual atom character head,ih later tail]

/-- Source decoding preserves exactly the selected identities and current
Boolean flags read from the independent document. -/
theorem selection_observations (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (related : Related actual abstract) (block : NotionCorePayload.BlockKey) (start stop : Nat)
    (characters : List Character)
    (selected : NotionCoreRichProtocolNetwork.selection actual block start stop = some characters) :
    ∃ rich, selectRich abstract (NotionCoreMachine.blockName block) start stop = some rich ∧
      characters.map observation = rich.map (fun char => (char.address,char.bold)) := by
  unfold NotionCoreRichProtocolNetwork.selection at selected
  obtain ⟨atoms,blockRead,decoded⟩ := Option.bind_eq_some_iff.mp selected
  have present := selection_block_visible network reachable session actual reconstructed _ atoms blockRead
  refine ⟨_,selectRich_block related _ start stop atoms blockRead present,?_⟩
  simpa only [List.map_map,Function.comp_def,neutralAtom] using decoded_observations actual _ characters decoded

/-- Successful actual toggle preparation selects a nonempty independently
read slice, computes exactly one Boolean from all its current flags, and
covers exactly those stable identities throughout the visible document.
The endpoint list, coordinates and Boolean are conclusions of the caller. -/
theorem formatPayload_exact (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (related : Related actual abstract) (block : NotionCorePayload.BlockKey) (start stop : Nat)
    (parts : List NotionCoreRichPayload.Part) (value : Bool) (priority : NotionRunAllocation.Id)
    (prepared : NotionCoreRichProtocolNetwork.formatPayload actual block start stop = some (.format parts value)) :
    ∃ rich, selectRich abstract (NotionCoreMachine.blockName block) start stop = some rich ∧
      rich ≠ [] ∧ value = !(rich.all (·.bold)) ∧
      selectedAddresses abstract (NotionCoreMachine.blockName block) start stop = some (rich.map (·.address)) ∧
      selectedVerdict abstract (NotionCoreMachine.blockName block) start stop = some value ∧
      ∀ shown ∈ abstract.document, shown.alive = true → ∀ slot ∈ shown.slots, slot.visible = true →
        NotionCoreAtomicFormatting.covers (NotionCoreAtomicFormattingMachine.instanceForest actual)
          (NotionCoreAtomicFormatting.Batch.ofFormat priority parts value) slot.address.1
          (coordinate actual slot.address) = (rich.map (·.address)).contains slot.address := by
  obtain ⟨characters,selected,nonempty,_,partsEq,valueEq⟩ :=
    NotionCoreRichProtocolFormatFacts.formatPayload_data prepared
  obtain ⟨rich,richSelected,observations⟩ := selection_observations network reachable session actual abstract
    reconstructed related block start stop characters selected
  have identities : (characters.map fun character =>
      NotionCorePhysicalReplay.address character.textInstance character.item.id) = rich.map (·.address) := by
    simpa only [List.map_map,Function.comp_def,observation] using congrArg (List.map Prod.fst) observations
  have flags : characters.map Character.bold = rich.map (·.bold) := by
    simpa only [List.map_map,Function.comp_def,observation] using congrArg (List.map Prod.snd) observations
  have ballot : value = !(rich.all (·.bold)) := by
    rw [valueEq]
    have eq : characters.all Character.bold = rich.all (·.bold) := by
      simpa only [List.all_map,Function.comp_def] using congrArg (fun values : List Bool => values.all id) flags
    rw [eq]
  have richNonempty : rich ≠ [] := by
    intro empty
    have lengths := congrArg List.length observations
    simp only [List.length_map,empty,List.length_nil] at lengths
    have charactersEmpty : characters = [] := by simpa using lengths
    simp [charactersEmpty] at nonempty
  refine ⟨rich,richSelected,richNonempty,ballot,?_,?_,?_⟩
  · simp only [selectedAddresses,richSelected,Option.map_some]
  · simp only [selectedVerdict,richSelected,Option.map_some,← ballot]
  · have batch : NotionCoreAtomicFormatting.Batch.ofFormat priority parts value =
        NotionCoreAtomicFormatting.planned (NotionCoreAtomicFormattingMachine.instanceForest actual)
          (rich.map (·.address)) ((actual.core.instances.map Prod.fst).eraseDups) priority value := by
      rw [partsEq]
      unfold NotionCoreRichProtocolFormatFacts.plannedSegments
      rw [identities]
      rfl
    rw [batch]
    exact planned_exact related _ priority value


/-- At issuance, the repaired whole batch writes the one captured Boolean
exactly on the independently selected visible identities. Every other visible
read retains its old Boolean. Future insertion is handled separately by the
character-and-gap refinement, rather than freezing this identity set. -/
theorem formatPayload_current_effect (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (related : Related actual abstract) (block : NotionCorePayload.BlockKey) (start stop : Nat)
    (parts : List NotionCoreRichPayload.Part) (value : Bool) (priority : NotionRunAllocation.Id)
    (prepared : NotionCoreRichProtocolNetwork.formatPayload actual block start stop = some (.format parts value))
    (fresh : ∀ old ∈ actual.batches, NotionRunAllocation.Before old.priority priority) :
    ∃ rich, selectRich abstract (NotionCoreMachine.blockName block) start stop = some rich ∧ rich ≠ [] ∧
      value = !(rich.all (·.bold)) ∧
      ∀ shown ∈ abstract.document, shown.alive = true → ∀ slot ∈ shown.slots, slot.visible = true →
        NotionCoreAtomicFormattingMachine.boldAt
          {actual with batches := actual.batches ++ [NotionCoreAtomicFormatting.Batch.ofFormat priority parts value]}
          slot.address = if (rich.map (·.address)).contains slot.address then value
            else NotionCoreAtomicFormattingMachine.boldAt actual slot.address := by
  obtain ⟨rich,selected,nonempty,ballot,_,_,coverage⟩ := formatPayload_exact network reachable session actual
    abstract reconstructed related block start stop parts value priority prepared
  refine ⟨rich,selected,nonempty,ballot,?_⟩
  intro shown member alive slot retained live
  obtain ⟨_,unique,p,hp,identity,position⟩ := displayCoordinates related shown member alive slot retained live
  have walkMember := (List.mem_filter.mp hp).1
  have livePosition := (List.mem_filter.mp hp).2
  obtain ⟨content,kind⟩ : ∃ content, p.item.kind = .text content false := by
    cases hk : p.item.kind with
    | split => simp [NotionCoreFormattingPlanner.live,hk] at livePosition
    | text content deleted =>
      cases deleted with
      | true => simp [NotionCoreFormattingPlanner.live,hk] at livePosition
      | false => exact ⟨content,rfl⟩
  let next : NotionCoreAtomicFormattingMachine.State := {actual with batches := actual.batches ++
    [NotionCoreAtomicFormatting.Batch.ofFormat priority parts value]}
  have after := NotionCoreAtomicFormattingMachine.boldAt_positioned next slot.address.1 unique p walkMember content kind
  have before := NotionCoreAtomicFormattingMachine.boldAt_positioned actual slot.address.1 unique p walkMember content kind
  rw [identity] at after before
  change NotionCoreAtomicFormattingMachine.boldAt next slot.address = _
  rw [after]
  change NotionCoreAtomicFormatting.resolveAt (NotionCoreAtomicFormattingMachine.instanceForest actual)
    (actual.batches ++ [NotionCoreAtomicFormatting.Batch.ofFormat priority parts value]) slot.address.1 p.entry = _
  rw [NotionCoreAtomicFormatting.resolve_latest_at _ actual.batches
    (NotionCoreAtomicFormatting.Batch.ofFormat priority parts value) fresh]
  have exactCoverage := coverage shown member alive slot retained live
  rw [position] at exactCoverage
  rw [exactCoverage,before]
  rfl


/-- Actual allocator receipt bounds put every reconstructed batch before the
next issued header. This freshness is derived, not a client obligation. -/
theorem reconstructed_batches_before_reserve (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (payload : NotionCoreRichPayload.Payload) :
    ∀ old ∈ actual.batches, NotionRunAllocation.Before old.priority
      (NotionRunAllocation.reserve (network.allocation.peers session) session payload.width).first := by
  have batches := NotionCoreAtomicFormattingMachine.replay_batches {} actual
    (NotionCoreRichPayload.sort (NotionCoreRichProtocolNetwork.receivedTransactions network session)) reconstructed
  simp only [List.nil_append] at batches
  intro old member
  rw [batches] at member
  obtain ⟨transaction,present,decoded⟩ := List.mem_filterMap.mp member
  rw [NotionCoreAtomicFormatting.ofTransaction_priority transaction old decoded]
  have received := (NotionCoreRichPayload.sort_perm _).mem_iff.mp present
  obtain ⟨entry,selected,same⟩ := List.mem_map.mp received
  subst transaction
  have entryReceived : entry.transaction.reservation ∈ (network.allocation.peers session).received := by
    simpa only [List.contains_iff_mem] using (List.mem_filter.mp selected).2
  have positive := NotionCoreRichProtocolNetwork.width_positive entry.transaction.payload
  apply Or.inl
  exact NotionRunAllocation.received_before_reservation
    (NotionRunAllocation.reachable_bounded (NotionCoreRichProtocolNetwork.allocation_reachable reachable) session)
    entryReceived ⟨0,positive,by simp [NotionRunAllocation.Run.at,NotionCoreRichPayload.Transaction.reservation]⟩
    session payload.width

/-- Concrete issuer effect at its actual allocated priority, with no supplied
coordinate, coverage, selected-identity, Boolean or freshness premise. -/
theorem formatPayload_issued_effect (network : NotionCoreRichProtocolNetwork.State)
    (reachable : NotionCoreRichProtocolNetwork.Reach network) (session : NotionRunAllocation.Session)
    (actual : NotionCoreAtomicFormattingMachine.State) (abstract : State)
    (reconstructed : NotionCoreRichProtocolNetwork.reconstruct network session = some actual)
    (related : Related actual abstract) (block : NotionCorePayload.BlockKey) (start stop : Nat)
    (parts : List NotionCoreRichPayload.Part) (value : Bool)
    (prepared : NotionCoreRichProtocolNetwork.formatPayload actual block start stop = some (.format parts value)) :
    ∃ rich, selectRich abstract (NotionCoreMachine.blockName block) start stop = some rich ∧ rich ≠ [] ∧
      value = !(rich.all (·.bold)) ∧
      ∀ shown ∈ abstract.document, shown.alive = true → ∀ slot ∈ shown.slots, slot.visible = true →
        NotionCoreAtomicFormattingMachine.boldAt
          {actual with batches := actual.batches ++ [NotionCoreAtomicFormatting.Batch.ofFormat
            (NotionRunAllocation.reserve (network.allocation.peers session) session
              (NotionCoreRichPayload.Payload.format parts value).width).first parts value]}
          slot.address = if (rich.map (·.address)).contains slot.address then value
            else NotionCoreAtomicFormattingMachine.boldAt actual slot.address :=
  formatPayload_current_effect network reachable session actual abstract reconstructed related block start stop parts value
    _ prepared (reconstructed_batches_before_reserve network reachable session actual reconstructed (.format parts value))


#print axioms displayCoordinates
#print axioms selection_observations
#print axioms formatPayload_exact
#print axioms formatPayload_current_effect
#print axioms formatPayload_issued_effect

end Sal.MRDTs.Instances.NotionCoreRichSequential.Selection
