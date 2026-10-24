import Sal.MRDTs.Instances.NotionCoreRichSequentialRelation
import Sal.MRDTs.Instances.NotionCoreRichProtocolCarrier

namespace Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
open NotionCoreSpec
open NotionCoreFormattingSource (Positioned)
open NotionCoreOriginTree (Forest preorder)

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
        have heq : first :: tail = ys := by simpa [List.mapM_cons,hx,ht] using h
        subst ys
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x,by simp,hx⟩
        · obtain ⟨z,hz,hf⟩ := ih tail ht hy
          exact ⟨z,by simp [hz],hf⟩

private theorem readAt_physical {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (inst : Nat) (atom : NotionCoreSource.Atom)
    (registered : Registered actual inst) (physical : atom ∈ NotionCoreMachine.physical actual.core inst)
    (value : Nat) (live : atom.kind = .text value false) :
    readAt abstract atom.address = some (NotionCoreAtomicFormattingMachine.boldAt actual atom.address) := by
  obtain ⟨text,ht⟩ := (related.registered inst).mpr registered
  simp only [NotionCoreMachine.physical,NotionCorePhysicalReplay.physical,List.mem_cons,List.mem_map] at physical
  rcases physical with hstart | ⟨item,hm,hitem⟩
  · subst atom
    simp [NotionCorePhysicalReplay.start,NotionCorePartition.boundary] at live
  · subst atom
    have hforest : item ∈ preorder (NotionCoreAtomicFormattingMachine.instanceForest actual inst) := by
      rw [NotionCoreAtomicFormattingMachine.instanceForest_traversal]
      exact hm
    have hwalk : item ∈ (NotionCoreFormattingSource.walk 0
        (NotionCoreAtomicFormattingMachine.instanceForest actual inst)).map Positioned.item := by
      rw [NotionCoreFormattingSource.walk_items]
      exact hforest
    obtain ⟨position,hp,hpi⟩ := List.mem_map.mp hwalk
    have hlive : item.kind = .text value false := by
      cases hk : item.kind <;> simp_all [NotionCorePhysicalReplay.atom]
    have hh := readAt_positioned related inst text ht position hp value (by rw [hpi]; exact hlive)
    simpa only [hpi] using hh

/-- Live displayed slots come from physically stored live atoms. Materialized
slice extraction derives this fact; no displayed/source coordinate relation is
assumed separately. -/
theorem visible_read {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (block : Block) (hb : block ∈ abstract.document)
    (halive : block.alive = true) (slot : Slot) (hs : slot ∈ block.slots) (hlive : slot.visible = true) :
    readAt abstract slot.address = some (NotionCoreAtomicFormattingMachine.boldAt actual slot.address) := by
  obtain ⟨source,hmat,hdoc⟩ := related.document
  rw [hdoc] at hb
  obtain ⟨sourceBlock,hblock,rfl⟩ := List.mem_map.mp hb
  obtain ⟨bid,_,hentry⟩ := mapM_member actual.core.display
    (NotionCoreMachineDocument.materializeEntry actual.core) source hmat hblock
  cases hfound : actual.core.forest.find? (fun old => old.id == bid) with
  | none =>
    rw [NotionCoreMachineDocument.materializeEntry_tombstone actual.core bid hfound] at hentry
    cases hentry
    simp [NotionCoreSource.Block.project,NotionCoreSource.Block.alive] at halive
  | some actualBlock =>
    have hblockmat : NotionCoreMachineDocument.materializeBlock actual.core actualBlock = some sourceBlock := by
      simpa only [NotionCoreMachineDocument.materializeEntry,hfound] using hentry
    have hslices := (NotionCoreMachineDocument.materialized_slices actual.core actualBlock sourceBlock hblockmat).1
    change slot ∈ sourceBlock.slices.flatMap NotionCoreSource.Slice.slots at hs
    obtain ⟨slice,hinslice,hslot⟩ := List.mem_flatMap.mp hs
    simp only [NotionCoreSource.Slice.slots,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hslot
    rcases hslot with hanchor | hatom | hclose
    · subst slot
      simp [NotionCoreSource.Slice.anchor] at hlive
    · obtain ⟨atom,hatomMember,rfl⟩ := List.mem_map.mp hatom
      have registered := (NotionCoreMachineClient.materialized_storage actual.core _ _ hslices slice hinslice).1
      have hphys := (NotionCoreMachineClient.materialized_physical actual.core _ _ hslices slice hinslice).2 atom hatomMember
      cases hk : atom.kind with
      | split => simp [NotionCoreSource.Atom.slot,hk] at hlive
      | text value deleted =>
        cases deleted with
        | true => simp [NotionCoreSource.Atom.slot,hk] at hlive
        | false =>
          have hh := readAt_physical related slice.start.1 atom registered hphys value hk
          simpa only [NotionCoreSource.Atom.slot,hk] using hh
    · subst slot
      simp [NotionCoreSource.Slice.close] at hlive

private theorem mapM_of_eq_some {α β : Type} (xs : List α) (f : α → Option β) (g : α → β)
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx := h x (by simp)
    have hr : ∀ x ∈ rest, f x = some (g x) := fun x hx => h x (by simp [hx])
    simp [List.mapM_cons,hx,ih hr]

theorem render_of_reads (abstract : State) (mark : Address → Bool)
    (hread : ∀ block ∈ abstract.document, block.alive = true →
      ∀ slot ∈ block.slots, slot.visible = true → readAt abstract slot.address = some (mark slot.address)) :
    render abstract = some (NotionCoreFormattingSpec.richView ⟨abstract.document,mark⟩) := by
  unfold render NotionCoreFormattingSpec.richView
  apply mapM_of_eq_some
  intro block hb
  obtain ⟨hb,halive⟩ := List.mem_filter.mp hb
  have hchars : (block.slots.filter Slot.visible).mapM (fun slot => do
      pure (⟨slot.address,slot.value,← readAt abstract slot.address⟩ : RichChar)) =
      some (NotionCoreFormattingSpec.richText mark block.slots) := by
    apply mapM_of_eq_some
    intro slot hs
    obtain ⟨hs,hvisible⟩ := List.mem_filter.mp hs
    simp [hread block hb halive slot hs hvisible]
  rw [hchars]
  rfl

private def overlayAtom (mark : Address → Bool) (atom : NotionCoreAtomicFormattingMachine.RichAtom) : RichChar :=
  ⟨atom.address,atom.value,mark atom.address⟩

private theorem overlay_atoms (state : NotionCoreFormattingMachine.State) (mark : Address → Bool)
    (atoms : List NotionCoreSource.Atom) :
    (atoms.flatMap (NotionCoreFormattingMachine.annotateAtom state)).map (overlayAtom mark) =
      NotionCoreFormattingSpec.richText mark (atoms.map NotionCoreSource.Atom.slot) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
    cases atom with
    | mk address kind =>
      cases kind with
      | split => simpa [NotionCoreFormattingMachine.annotateAtom,NotionCoreSource.Atom.slot,
          NotionCoreFormattingSpec.richText,overlayAtom] using ih
      | text value deleted =>
        cases deleted <;> simpa [NotionCoreFormattingMachine.annotateAtom,NotionCoreSource.Atom.slot,
          NotionCoreFormattingSpec.richText,overlayAtom] using ih

private theorem richText_append (mark : Address → Bool) (left right : List Slot) :
    NotionCoreFormattingSpec.richText mark (left ++ right) =
      NotionCoreFormattingSpec.richText mark left ++ NotionCoreFormattingSpec.richText mark right := by
  simp [NotionCoreFormattingSpec.richText]

private theorem projected_richText (mark : Address → Bool) (source : NotionCoreSource.Block) :
    NotionCoreFormattingSpec.richText mark source.project.slots =
      NotionCoreFormattingSpec.richText mark ((source.slices.flatMap NotionCoreSource.Slice.atoms).map NotionCoreSource.Atom.slot) := by
  change NotionCoreFormattingSpec.richText mark (source.slices.flatMap NotionCoreSource.Slice.slots) = _
  induction source.slices with
  | nil => rfl
  | cons slice rest ih =>
    simp only [List.flatMap_cons,List.map_append,richText_append]
    rw [ih]
    congr 1
    simp [NotionCoreSource.Slice.slots,NotionCoreSource.Slice.anchor,NotionCoreSource.Slice.close,
      NotionCoreFormattingSpec.richText,NotionCoreSpec.closeOf_visible]

private theorem block_overlay_materialized (state : NotionCoreMachine.State) (mark : Address → Bool)
    (bid : Nat) (block : NotionCoreSliceForest.Block) (source : NotionCoreSource.Block)
    (found : state.forest.find? (fun old => old.id == bid) = some block)
    (hmat : NotionCoreMachineDocument.materializeBlock state block = some source) :
    (NotionCoreFormattingMachine.blockRich ⟨state,[]⟩ bid).map (List.map (overlayAtom mark)) =
      some (NotionCoreFormattingSpec.richText mark source.project.slots) := by
  have hatoms := NotionCoreMachineDocument.materialized_tree_atoms state block source hmat
  simp [NotionCoreFormattingMachine.blockRich,found,hatoms,overlay_atoms]
  exact (projected_richText mark source).symm

private def overlayView (mark : Address → Bool) (document : NotionCoreAtomicFormattingMachine.View) :
    List (Nat × List RichChar) :=
  document.map fun (bid,atoms) => (bid,atoms.map (overlayAtom mark))

private theorem entry_overlay (state : NotionCoreMachine.State) (mark : Address → Bool)
    (bid : Nat) (source : NotionCoreSource.Block)
    (hmat : NotionCoreMachineDocument.materializeEntry state bid = some source) :
    source.id = bid ∧
    (source.alive = true ↔ (state.forest.any (fun block => block.id == bid)) = true) ∧
    (source.alive = true →
      (NotionCoreFormattingMachine.blockRich ⟨state,[]⟩ bid).map (List.map (overlayAtom mark)) =
        some (NotionCoreFormattingSpec.richText mark source.project.slots)) := by
  cases hfound : state.forest.find? (fun block => block.id == bid) with
  | none =>
    rw [NotionCoreMachineDocument.materializeEntry_tombstone state bid hfound] at hmat
    cases hmat
    refine ⟨rfl,?_,fun h => by simp [NotionCoreSource.Block.alive] at h⟩
    simp only [NotionCoreSource.Block.alive,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,false_iff]
    intro h
    obtain ⟨block,hb,hid⟩ := List.any_eq_true.mp h
    exact List.find?_eq_none.mp hfound block hb hid
  | some block =>
    have hbmat : NotionCoreMachineDocument.materializeBlock state block = some source := by
      simpa only [NotionCoreMachineDocument.materializeEntry,hfound] using hmat
    have hname := NotionCoreMachineDocument.materialized_named_id state bid source hmat
    have hlive := NotionCoreMachineDocument.materialized_alive state block source hbmat
    have hpresent : (state.forest.any fun block => block.id == bid) = true :=
      List.any_eq_true.mpr ⟨block,List.mem_of_find?_eq_some hfound,by simpa using List.find?_some hfound⟩
    exact ⟨hname,by simp [hlive,hpresent],fun _ => block_overlay_materialized state mark bid block source hfound hbmat⟩

/-- Full fields, including stable identities, agree with display-ordered
materialization before any rich relation or annotation invariant is used. -/
theorem materialized_overlay (state : NotionCoreMachine.State) (mark : Address → Bool)
    (document : NotionCoreSourceDocument.Document)
    (hmat : NotionCoreMachineDocument.materializeDocument state = some document) :
    (NotionCoreFormattingMachine.render ⟨state,[]⟩).map (overlayView mark) =
      some (NotionCoreFormattingSpec.richView ⟨NotionCoreSourceDocument.project document,mark⟩) := by
  have sequence : ∀ (ids : List Nat) (doc : NotionCoreSourceDocument.Document),
      ids.mapM (NotionCoreMachineDocument.materializeEntry state) = some doc →
      ((ids.filter (fun bid => state.forest.any (fun block => block.id == bid))).mapM
        (fun bid => do pure (bid,← NotionCoreFormattingMachine.blockRich ⟨state,[]⟩ bid))).map (overlayView mark) =
        some (NotionCoreFormattingSpec.richView ⟨NotionCoreSourceDocument.project doc,mark⟩) := by
    intro ids
    induction ids with
    | nil => intro doc h; simp at h; subst doc; rfl
    | cons bid rest ih =>
      intro doc h
      cases hfirst : NotionCoreMachineDocument.materializeEntry state bid with
      | none => simp [List.mapM_cons,hfirst] at h
      | some source =>
        cases htail : rest.mapM (NotionCoreMachineDocument.materializeEntry state) with
        | none => simp [List.mapM_cons,hfirst,htail] at h
        | some suffix =>
          have heq : source :: suffix = doc := by simpa [List.mapM_cons,hfirst,htail] using h
          subst doc
          obtain ⟨hname,halive,hpaint⟩ := entry_overlay state mark bid source hfirst
          have later := ih suffix htail
          by_cases hpresent : (state.forest.any (fun block => block.id == bid)) = true
          · have hlive := halive.mpr hpresent
            obtain ⟨atoms,hraw,hchars⟩ := Option.map_eq_some_iff.mp (hpaint hlive)
            obtain ⟨tail,htailraw,htailview⟩ := Option.map_eq_some_iff.mp later
            simp only [List.filter_cons,hpresent,↓reduceIte,List.mapM_cons,hraw,htailraw]
            simp [overlayView,hchars,NotionCoreFormattingSpec.richView,
              NotionCoreSourceDocument.project,NotionCoreSource.Block.project,hlive,hname]
            exact htailview
          · have hdead : source.alive = false := by cases h : source.alive <;> simp_all
            simp only [List.filter_cons,hpresent,Bool.false_eq_true,↓reduceIte]
            simpa [NotionCoreFormattingSpec.richView,NotionCoreSourceDocument.project,
              NotionCoreSource.Block.project,hdead] using later
  exact sequence state.display document hmat

/-- Full repaired renderer agreement, rather than only equality after dropping
bold flags. Every visible read is derived from physical items in Related. -/
theorem render_related {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) :
    (NotionCoreAtomicFormattingMachine.render actual).map NotionCoreRichProtocolCarrier.neutral = render abstract := by
  obtain ⟨source,hmat,hdoc⟩ := related.document
  have hsource := materialized_overlay actual.core (NotionCoreAtomicFormattingMachine.boldAt actual) source hmat
  have habstract := render_of_reads abstract (NotionCoreAtomicFormattingMachine.boldAt actual)
    (visible_read related)
  rw [habstract,hdoc]
  have hview : (NotionCoreAtomicFormattingMachine.render actual).map NotionCoreRichProtocolCarrier.neutral =
      (NotionCoreFormattingMachine.render ⟨actual.core,[]⟩).map (overlayView (NotionCoreAtomicFormattingMachine.boldAt actual)) := by
    simp only [NotionCoreAtomicFormattingMachine.render,NotionCoreAtomicFormattingMachine.plainState,
      Option.map_map,NotionCoreRichProtocolCarrier.neutral,NotionCoreAtomicFormattingMachine.markDocument,
      List.map_map,Function.comp_def,NotionCoreAtomicFormattingMachine.markAtom,
      NotionCoreAtomicFormattingMachine.RichAtom.address,NotionCoreAtomicFormattingMachine.RichAtom.value,
      NotionCoreAtomicFormattingMachine.RichAtom.bold]
    rfl
  exact hview.trans hsource

/-- Related well-formed documents always have a successful complete rich read. -/
theorem render_total_related {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) :
    ∃ raw, NotionCoreAtomicFormattingMachine.render actual = some raw ∧
      render abstract = some (NotionCoreRichProtocolCarrier.neutral raw) := by
  have habstract := render_of_reads abstract (NotionCoreAtomicFormattingMachine.boldAt actual)
    (visible_read related)
  have heq := render_related related
  cases hraw : NotionCoreAtomicFormattingMachine.render actual with
  | none => rw [hraw,Option.map_none,habstract] at heq; contradiction
  | some raw => exact ⟨raw,rfl,by simpa only [hraw,Option.map_some] using heq.symm⟩

/-- Primitive source anchor availability needed for executing a supported
format. Honest protocol reach derives these facts from real birth providers. -/
def FormatReady (actual : NotionCoreAtomicFormattingMachine.State)
    (parts : List NotionCoreRichPayload.Part) : Prop :=
  ∀ part ∈ parts, Registered actual part.instanceId ∧
    ∃ lo hi, NotionCoreFormattingSource.anchorPosition
      (NotionCoreAtomicFormattingMachine.instanceForest actual part.instanceId) part.lower = some lo ∧
      NotionCoreFormattingSource.anchorPosition
      (NotionCoreAtomicFormattingMachine.instanceForest actual part.instanceId) part.upper = some hi

private def partRange (forests : Nat → Forest) (inst : Nat) (part : NotionCoreRichPayload.Part) : Option Range :=
  if part.instanceId = inst then do
    pure ⟨← NotionCoreFormattingSource.anchorPosition (forests inst) part.lower,
      ← NotionCoreFormattingSource.anchorPosition (forests inst) part.upper⟩
  else none

private theorem rangesFor_parts (actual : NotionCoreAtomicFormattingMachine.State)
    (priority : NotionRunAllocation.Id) (parts : List NotionCoreRichPayload.Part) (value : Bool) (inst : Nat) :
    AtomicBridge.rangesFor (NotionCoreAtomicFormattingMachine.instanceForest actual) inst
      (NotionCoreAtomicFormatting.Batch.ofFormat priority parts value).segments =
      parts.filterMap (partRange (NotionCoreAtomicFormattingMachine.instanceForest actual) inst) := by
  unfold AtomicBridge.rangesFor
  have hf : AtomicBridge.segmentRange (NotionCoreAtomicFormattingMachine.instanceForest actual) inst =
      fun segment => partRange (NotionCoreAtomicFormattingMachine.instanceForest actual) inst segment.part := by
    funext segment
    unfold AtomicBridge.segmentRange partRange NotionCoreAtomicFormatting.Segment.part
    split <;> simp_all
    cases NotionCoreFormattingSource.anchorPosition
      (NotionCoreAtomicFormattingMachine.instanceForest actual inst) segment.lower <;>
      cases NotionCoreFormattingSource.anchorPosition
        (NotionCoreAtomicFormattingMachine.instanceForest actual inst) segment.upper <;> rfl
  rw [hf,NotionCoreAtomicFormatting.ofFormat_filterMap]

private theorem resolve_format_parts {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (parts : List NotionCoreRichPayload.Part) (regions : List Region)
    (compiled : parts.mapM NotionCoreRichSequentialInputs.region = some regions)
    (ready : FormatReady actual parts) :
    ∃ resolved, resolveRegions abstract regions = some resolved ∧
      ∀ inst, resolved.filterMap (fun (i,r) => if i = inst then some r else none) =
        parts.filterMap (partRange (NotionCoreAtomicFormattingMachine.instanceForest actual) inst) := by
  induction parts generalizing regions with
  | nil =>
    have empty : ([] : List Region) = regions := Option.some.inj compiled
    subst regions
    exact ⟨[],rfl,fun _ => rfl⟩
  | cons part rest ih =>
    cases hp : NotionCoreRichSequentialInputs.region part with
    | none => simp [List.mapM_cons,hp] at compiled
    | some region =>
      cases hr : rest.mapM NotionCoreRichSequentialInputs.region with
      | none => simp [List.mapM_cons,hp,hr] at compiled
      | some tail =>
        have heq : region :: tail = regions := by simpa [List.mapM_cons,hp,hr] using compiled
        subst regions
        obtain ⟨registered,lo,hi,hlo,hhi⟩ := ready part (by simp)
        obtain ⟨text,ht⟩ := (related.registered part.instanceId).mpr registered
        have translated := NotionCoreRichCoordinates.translated_region
          (NotionCoreAtomicFormattingMachine.instanceForest actual part.instanceId) text.bold text.gapBold part region hp
        have htext : text = ⟨NotionCoreRichCoordinates.physicalSlots part.instanceId
            (NotionCoreAtomicFormattingMachine.instanceForest actual part.instanceId),text.bold,text.gapBold⟩ :=
          Text.ext (related.physical part.instanceId text ht) rfl rfl
        have hresolve : resolveRegion text region = some ⟨lo,hi⟩ := by
          rw [htext,translated.2,hlo,hhi]; rfl
        obtain ⟨resolved,hresolved,hfilters⟩ := ih tail hr (fun p hm => ready p (by simp [hm]))
        refine ⟨(part.instanceId,⟨lo,hi⟩)::resolved,?_,?_⟩
        · have head : (do
              let text ← abstract.texts region.instanceId
              let range ← resolveRegion text region
              pure (region.instanceId,range)) = some (part.instanceId,(⟨lo,hi⟩ : Range)) := by
            simp only [translated.1,ht,Bind.bind,Option.bind]
            rw [hresolve]
            rfl
          unfold resolveRegions at hresolved ⊢
          rw [List.mapM_cons,head,hresolved]
          rfl

        · intro inst
          simp only [List.filterMap_cons,hfilters]
          by_cases same : part.instanceId = inst
          · subst inst; simp [partRange,hlo,hhi]
          · simp [partRange,same]

/-- The actual whole-batch append simulates direct union painting of the one
issued Boolean, on both existing characters and retained insertion gaps. -/
theorem format_preserves {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (priority : NotionRunAllocation.Id)
    (parts : List NotionCoreRichPayload.Part) (regions : List Region) (value : Bool)
    (compiled : parts.mapM NotionCoreRichSequentialInputs.region = some regions)
    (ready : FormatReady actual parts)
    (fresh : ∀ old ∈ actual.batches, NotionRunAllocation.Before old.priority priority) :
    ∃ next, format abstract regions value = some next ∧
      Related {actual with batches := actual.batches ++
        [NotionCoreAtomicFormatting.Batch.ofFormat priority parts value]} next := by
  obtain ⟨resolved,hresolved,hfilters⟩ := resolve_format_parts related parts regions compiled ready
  let next : State := {abstract with texts := (fun inst => (abstract.texts inst).map (fun text =>
    paint text (resolved.filterMap (fun (i,r) => if i = inst then some r else none)) value))}
  refine ⟨next,by simp only [format,hresolved,Option.map_some]; rfl,?_⟩
  constructor
  · exact related.document
  · intro inst
    constructor
    · rintro ⟨text,ht⟩
      obtain ⟨old,hold,_⟩ := Option.map_eq_some_iff.mp ht
      exact (related.registered inst).mp ⟨old,hold⟩
    · intro hr
      obtain ⟨old,hold⟩ := (related.registered inst).mpr hr
      exact ⟨paint old (resolved.filterMap (fun (i,r) => if i = inst then some r else none)) value,
        by simp only [next,hold,Option.map_some]⟩
  · intro inst text ht
    obtain ⟨old,hold,heq⟩ := Option.map_eq_some_iff.mp ht
    subst text
    exact related.physical inst old hold
  · exact related.unique
  · intro inst text ht
    obtain ⟨old,hold,heq⟩ := Option.map_eq_some_iff.mp ht
    subst text
    rw [hfilters,← rangesFor_parts actual priority parts value inst]
    exact AtomicBridge.paint_refines_latest _ actual.batches
      (NotionCoreAtomicFormatting.Batch.ofFormat priority parts value) inst old
      (related.marks inst old hold) fresh

/-- Transaction-shaped format simulation for the canonical-history induction.
Both interpreters consume the same complete source transaction atomically. -/
theorem format_transaction {actual : NotionCoreAtomicFormattingMachine.State} {abstract : State}
    (related : Related actual abstract) (transaction : NotionCoreRichPayload.Transaction)
    (parts : List NotionCoreRichPayload.Part) (regions : List Region) (value : Bool)
    (payload : transaction.payload = .format parts value)
    (compiled : parts.mapM NotionCoreRichSequentialInputs.region = some regions)
    (ready : FormatReady actual parts)
    (fresh : ∀ old ∈ actual.batches, NotionRunAllocation.Before old.priority transaction.id) :
    ∃ actualNext abstractNext,
      NotionCoreAtomicFormattingMachine.applyTransaction actual transaction = some actualNext ∧
      NotionCoreRichSequentialInputs.applyTransaction abstract transaction = some abstractNext ∧
      Related actualNext abstractNext := by
  obtain ⟨next,hstep,hrelated⟩ := format_preserves related transaction.id parts regions value compiled ready fresh
  refine ⟨_,next,?_,?_,hrelated⟩
  · simp only [NotionCoreAtomicFormattingMachine.applyTransaction,payload]
  · simpa only [NotionCoreRichSequentialInputs.applyTransaction,
      NotionCoreRichSequentialInputs.command,payload,compiled,Option.map_some,Bind.bind,Option.bind,step] using hstep

#print axioms render_related
#print axioms render_total_related
#print axioms format_preserves

end Sal.MRDTs.Instances.NotionCoreRichSequential.Refinement
