import Sal.MRDTs.Instances.NotionCoreFormattingBridge
import Sal.MRDTs.Instances.NotionCorePhysicalReplay

/-! Candidate compiler: scan whole-instance visible preorder, retaining an
open selected run until the first unselected visible item, or END. Unlike
`contiguousSegments`, displayed selection order does not determine boundaries.
The proofs concern immediate current coverage; intervals still contain hidden
physical items and retain the source's dynamic insertion behaviour. -/
namespace Sal.MRDTs.Instances.NotionCoreFormattingPlanner
open NotionCoreFormattingSource
open NotionCoreOriginTree (Forest preorder)
open NotionCoreSpec (Address Document)

structure Segment where
  first : Positioned
  next : Option Positioned
  deriving DecidableEq, Repr

/-- The open run is closed only by an unselected visible item or END.
This is the `first` accumulator in candidate-planner.mjs. -/
def scan (selected : Positioned → Bool) : Option Positioned → List Positioned → List Segment
  | active, [] => active.toList.map fun first => ⟨first, none⟩
  | active, item :: rest =>
      if selected item then scan selected (active.orElse (fun _ => some item)) rest
      else (active.toList.map fun first => ⟨first, some item⟩) ++ scan selected none rest

def segmentContains (finish : Nat) (segment : Segment) (index : Nat) : Bool :=
  decide (segment.first.entry ≤ index ∧ index < (segment.next.map Positioned.entry).getD finish)

def scanContains (finish : Nat) (selected : Positioned → Bool)
    (active : Option Positioned) (items : List Positioned) (index : Nat) : Bool :=
  (scan selected active items).any (fun segment => segmentContains finish segment index)

theorem scanContains_cons (finish : Nat) (selected : Positioned → Bool)
    (active : Option Positioned) (item : Positioned) (rest : List Positioned) (index : Nat) :
    scanContains finish selected active (item :: rest) index =
      if selected item then
        scanContains finish selected (active.orElse (fun _ => some item)) rest index
      else active.any (fun first => decide (first.entry ≤ index ∧ index < item.entry)) ||
        scanContains finish selected none rest index := by
  cases choice : selected item <;> cases active <;> simp [scanContains, scan, segmentContains, choice]

/-- Before all remaining visible items, only the open run can cover. -/
theorem scan_before (finish : Nat) (selected : Positioned → Bool)
    (items : List Positioned) (active : Option Positioned) (index : Nat)
    (before : ∀ item ∈ items, index < item.entry) (bound : index < finish) :
    scanContains finish selected active items index =
      active.any (fun first => decide (first.entry ≤ index)) := by
  induction items generalizing active with
  | nil => cases active <;> simp [scanContains, scan, segmentContains, bound]
  | cons item rest ih =>
    have head := before item (by simp)
    have tail : ∀ p ∈ rest, index < p.entry := fun p h => before p (by simp [h])
    rw [scanContains_cons]
    cases choice : selected item <;> cases active <;>
      simp [ih _ tail, head, Nat.not_le.mpr head]

/-- All visible coordinates receive exactly their selected bit. -/
theorem scan_exact (finish : Nat) (selected : Positioned → Bool)
    (items : List Positioned) (ordered : items.Pairwise (fun a b => a.entry < b.entry))
    (bounded : ∀ p ∈ items, p.entry < finish)
    (active : Option Positioned)
    (activeBefore : ∀ first ∈ active, ∀ p ∈ items, first.entry ≤ p.entry)
    (query : Positioned) (member : query ∈ items) :
    scanContains finish selected active items query.entry = selected query := by
  induction items generalizing active query with
  | nil => simp at member
  | cons item rest ih =>
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    have tailBound : ∀ p ∈ rest, p.entry < finish := fun p h => bounded p (by simp [h])
    have tailActive : ∀ first ∈ active, ∀ p ∈ rest, first.entry ≤ p.entry :=
      fun first h p hp => activeBefore first h p (by simp [hp])
    have nextActive : ∀ first ∈ active.orElse (fun _ => some item),
        ∀ p ∈ rest, first.entry ≤ p.entry := by
      cases active with
      | none => simpa using fun p hp => Nat.le_of_lt (headBefore p hp)
      | some first => simpa using tailActive
    rw [scanContains_cons]
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst query
      have bound := bounded item (by simp)
      cases choice : selected item with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [scan_before finish selected rest none item.entry headBefore bound]
        cases active <;> simp
      | true =>
        simp only [↓reduceIte]
        rw [scan_before finish selected rest _ item.entry headBefore bound]
        cases active with
        | none => simp
        | some first => simp [activeBefore first (by simp) item (by simp)]
    · cases choice : selected item with
      | true => simpa [choice] using ih tailOrdered tailBound _ nextActive query later
      | false =>
        rw [if_neg (by simp), ih tailOrdered tailBound none (by simp) query later]
        have after : ¬ query.entry < item.entry := Nat.not_lt.mpr (Nat.le_of_lt (headBefore query later))
        cases active <;> simp [after]

/-- Every emitted boundary is drawn from the scanned visible sequence (or END),
so the source lookup theorem is applicable without assumed endpoint coverage. -/
theorem scan_boundaries (selected : Positioned → Bool) (items : List Positioned)
    (active : Option Positioned) (segment : Segment) (member : segment ∈ scan selected active items) :
    (segment.first ∈ active ∨ segment.first ∈ items) ∧
      (∀ next ∈ segment.next, next ∈ items) := by
  induction items generalizing active with
  | nil =>
    cases active with
    | none => simp [scan] at member
    | some first =>
      simp only [scan, Option.toList_some, List.map_singleton, List.mem_singleton] at member
      subst segment
      simp
  | cons item rest ih =>
    cases choice : selected item with
    | true =>
      have h := ih (active.orElse (fun _ => some item)) (by simpa [scan, choice] using member)
      constructor
      · cases active with
        | none =>
          apply Or.inr
          have hh : item = segment.first ∨ segment.first ∈ rest := by simpa using h.1
          rcases hh with same | later
          · exact List.mem_cons.mpr (Or.inl same.symm)
          · exact List.mem_cons_of_mem item later
        | some first =>
          rcases h.1 with left | right
          · exact Or.inl (by simpa using left)
          · exact Or.inr (List.mem_cons_of_mem item right)
      · intro p hp; exact List.mem_cons_of_mem item (h.2 p hp)
    | false =>
      simp only [scan, choice, Bool.false_eq_true, ↓reduceIte, List.mem_append] at member
      rcases member with closed | tail
      · cases active <;> simp_all
      · have h := ih none tail
        simp only [Option.mem_def, reduceCtorEq, false_or] at h
        exact ⟨Or.inr (List.mem_cons_of_mem item h.1), fun p hp => List.mem_cons_of_mem item (h.2 p hp)⟩

def live (p : Positioned) : Bool := match p.item.kind with
  | .text _ false => true
  | _ => false

def visible (forest : Forest) : List Positioned := (walk 0 forest).filter live

/-- Projecting positioned visible items recovers the existing source renderer's
whole-instance visible list exactly, without renumbering physical entries. -/
theorem visible_items (forest : Forest) :
    (visible forest).map Positioned.item = visibleItems forest := by
  unfold visible visibleItems
  rw [← walk_items 0 forest, List.filter_map]
  rfl

def segments (forest : Forest) (selectedIds : NotionRunAllocation.Id → Bool) : List Segment :=
  scan (fun p => selectedIds p.item.id) none (visible forest)

def Segment.operation (segment : Segment) (id : NotionRunAllocation.Id) (value : Bool) : MarkOp :=
  ⟨id, ⟨.item segment.first.item.id, .before⟩,
    ⟨match segment.next with | some next => .item next.item.id | none => .finish, .before⟩, value⟩

/-- All IDs are retained, including tombstones and markers. Uniqueness is on
physical source IDs, rather than merely the currently displayed characters. -/
def UniqueIds (forest : Forest) : Prop := ((preorder forest).map (fun item => item.id)).Nodup
instance (forest : Forest) : Decidable (UniqueIds forest) :=
  inferInstanceAs (Decidable (((preorder forest).map NotionCoreOriginTree.Item.id).Nodup))

private theorem find_unique (items : List Positioned)
    (unique : (items.map (fun p => p.item.id)).Nodup)
    (p : Positioned) (member : p ∈ items) :
    items.find? (fun q => q.item.id == p.item.id) = some p := by
  induction items with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst p; simp
    · have different : first.item.id ≠ p.item.id := by
        intro equal
        apply fresh
        exact List.mem_map.mpr ⟨p, later, equal.symm⟩
      simp [different, ih tail later]

/-- Source anchor resolution is derived from the actual full physical walk;
the premise is ID uniqueness, not an assumed coordinate map. -/
theorem anchor_before_entry (forest : Forest) (unique : UniqueIds forest)
    (p : Positioned) (member : p ∈ walk 0 forest) :
    anchorPosition forest ⟨.item p.item.id, .before⟩ = some p.entry := by
  have ids : ((walk 0 forest).map (fun p => p.item.id)).Nodup := by
    change ((walk 0 forest).map (fun p => p.item.id)).Nodup
    have h : ((walk 0 forest).map Positioned.item |>.map (·.id)).Nodup := by
      rw [walk_items]
      exact unique
    simpa only [List.map_map] using h
  simp only [anchorPosition, find_unique _ ids p member, Option.map_some]

private theorem range_ordered (start count : Nat) :
    (List.range' start count).Pairwise (· < ·) := by
  induction count generalizing start with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ]
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih _⟩
    intro k member
    obtain ⟨i, _, hi⟩ := List.mem_range'.mp member
    omega

theorem visible_ordered (forest : Forest) :
    (visible forest).Pairwise (fun a b => a.entry < b.entry) := by
  apply List.Pairwise.filter
  apply List.pairwise_map.mp
  rw [walk_entries]
  exact range_ordered _ _

theorem walk_bounded (forest : Forest) (p : Positioned) (member : p ∈ walk 0 forest) :
    p.entry < (preorder forest).length := by
  have mapped : p.entry ∈ (walk 0 forest).map Positioned.entry := List.mem_map.mpr ⟨p, member, rfl⟩
  rw [walk_entries] at mapped
  obtain ⟨i, hi, equal⟩ := List.mem_range'.mp mapped
  omega

theorem visible_bounded (forest : Forest) (p : Positioned) (member : p ∈ visible forest) :
    p.entry < (preorder forest).length :=
  walk_bounded forest p (List.mem_filter.mp member).1

theorem segment_source_contains (forest : Forest) (unique : UniqueIds forest)
    (ids : NotionRunAllocation.Id → Bool) (segment : Segment) (member : segment ∈ segments forest ids)
    (id : NotionRunAllocation.Id) (value : Bool) (index : Nat) :
    covers forest (segment.operation id value) index =
      segmentContains (preorder forest).length segment index := by
  have boundaries := scan_boundaries (fun p => ids p.item.id) (visible forest) none segment member
  have firstVisible : segment.first ∈ visible forest := by simpa using boundaries.1
  have first : segment.first ∈ walk 0 forest := (List.mem_filter.mp firstVisible).1
  have startAt := anchor_before_entry forest unique segment.first first
  cases nextEq : segment.next with
  | none =>
    simp only [Segment.operation, nextEq]
    change covers forest ⟨id, ⟨.item segment.first.item.id, .before⟩, ⟨.finish, .before⟩, value⟩ index = _
    unfold covers
    rw [startAt]
    simp [anchorPosition, segmentContains, nextEq]
  | some next =>
    have nextMem : next ∈ walk 0 forest :=
      (List.mem_filter.mp (boundaries.2 next (by simp [nextEq]))).1
    have endAt := anchor_before_entry forest unique next nextMem
    simp [Segment.operation, covers, startAt, endAt, nextEq, segmentContains]

private theorem any_congr_mem {α : Type} (xs : List α) (f g : α → Bool)
    (same : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, same x (by simp), ih (fun y h => same y (by simp [h]))]

/-- Current exact coverage for the actual before-first .. before-next/END
planner, over arbitrary source origin forests with unique physical IDs. Markers
and tombstones remain in physical coordinates but are excluded from selection. -/
theorem segments_exact (forest : Forest) (unique : UniqueIds forest)
    (ids : NotionRunAllocation.Id → Bool) (p : Positioned) (member : p ∈ visible forest)
    (id : NotionRunAllocation.Id) (value : Bool) :
    (segments forest ids).any (fun segment => covers forest (segment.operation id value) p.entry) =
      ids p.item.id := by
  calc
    _ = (segments forest ids).any (fun segment => segmentContains (preorder forest).length segment p.entry) :=
      by
        apply any_congr_mem
        intro segment h
        exact segment_source_contains forest unique ids segment h id value p.entry
    _ = _ := scan_exact (preorder forest).length _ (visible forest)
      (visible_ordered forest) (visible_bounded forest) none (by simp) p member

/-- Bind source IDs to semantic addresses. This is the same caller-supplied
stable-ID decoding needed by the existing core/source relation. -/
def locatedSegments (forests : Nat → Forest) (addressOf : Nat → NotionRunAllocation.Id → Address)
    (targets : List Address) (instances : List Nat) : List (Nat × Segment) :=
  instances.flatMap fun instanceId =>
    (segments (forests instanceId) (fun id => targets.contains (addressOf instanceId id))).map
      fun segment => (instanceId, segment)

/-- Reserve consecutive operation IDs across the entire atomic plan. -/
def emit (session : NotionRunAllocation.Session) (counter : Nat) (value : Bool) :
    List (Nat × Segment) → List NotionCoreFormattingBridge.Located
  | [] => []
  | (instanceId, segment) :: rest =>
      (instanceId, segment.operation ⟨counter, session⟩ value) :: emit session (counter + 1) value rest

def plan (forests : Nat → Forest) (addressOf : Nat → NotionRunAllocation.Id → Address)
    (targets : List Address) (instances : List Nat) (session : NotionRunAllocation.Session)
    (counter : Nat) (value : Bool) : List NotionCoreFormattingBridge.Located :=
  emit session counter value (locatedSegments forests addressOf targets instances)

theorem emit_uniform (session : NotionRunAllocation.Session) (counter : Nat) (value : Bool)
    (parts : List (Nat × Segment)) (operation : NotionCoreFormattingBridge.Located)
    (member : operation ∈ emit session counter value parts) : operation.2.value = value := by
  induction parts generalizing counter with
  | nil => simp [emit] at member
  | cons part rest ih =>
    rcases part with ⟨instanceId, segment⟩
    simp only [emit, List.mem_cons] at member
    rcases member with same | later
    · subst operation; rfl
    · exact ih (counter + 1) later

private theorem emit_coverage (forests : Nat → Forest) (coordinate : Address → Nat)
    (address : Address) (session : NotionRunAllocation.Session) (counter : Nat) (value : Bool)
    (parts : List (Nat × Segment)) :
    (emit session counter value parts).any
        (fun op => NotionCoreFormattingBridge.coversAt forests coordinate op address) =
      parts.any (fun part => decide (address.1 = part.1) &&
        covers (forests part.1) (part.2.operation ⟨0, []⟩ value) (coordinate address)) := by
  induction parts generalizing counter with
  | nil => rfl
  | cons part rest ih =>
    rcases part with ⟨instanceId, segment⟩
    simp only [emit, List.any_cons]
    rw [ih]
    rfl

/-- No exact-coverage premise appears here: it is derived from ID uniqueness,
actual physical-walk membership and agreement of the core coordinate decoder.
All displayed instances must be supplied to the finite planner. -/
theorem plan_exact_at (forests : Nat → Forest)
    (addressOf : Nat → NotionRunAllocation.Id → Address) (coordinate : Address → Nat)
    (targets : List Address) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (value : Bool)
    (address : Address) (instancePresent : address.1 ∈ instances)
    (unique : UniqueIds (forests address.1))
    (p : Positioned) (member : p ∈ visible (forests address.1))
    (identity : addressOf address.1 p.item.id = address)
    (position : coordinate address = p.entry) :
    (plan forests addressOf targets instances session counter value).any
      (fun op => NotionCoreFormattingBridge.coversAt forests coordinate op address) = targets.contains address := by
  rw [plan, emit_coverage]
  unfold locatedSegments
  rw [List.any_flatMap]
  have perInstance : ∀ instanceId ∈ instances,
      ((segments (forests instanceId) (fun id => targets.contains (addressOf instanceId id))).map
        (fun segment => (instanceId, segment))).any
          (fun part => decide (address.1 = part.1) && covers (forests part.1)
            (part.2.operation ⟨0, []⟩ value) (coordinate address)) =
        (decide (address.1 = instanceId) && targets.contains address) := by
    intro instanceId _
    by_cases same : address.1 = instanceId
    · subst instanceId
      simp only [List.any_map, Function.comp_def, decide_true, Bool.true_and]
      rw [position, segments_exact _ unique _ p member, identity]
    · simp [same]
  rw [any_congr_mem _ _ _ perInstance]
  cases chosen : targets.contains address <;> simp [instancePresent]

/-- The relation asks only for displayed slots' source identity and physical
walk coordinate. It includes slots in other blocks, preventing N003 spillover. -/
def DisplayCoordinates (doc : Document) (forests : Nat → Forest)
    (addressOf : Nat → NotionRunAllocation.Id → Address) (coordinate : Address → Nat)
    (instances : List Nat) : Prop :=
  ∀ block ∈ doc, block.alive = true → ∀ slot ∈ block.slots, slot.visible = true →
    slot.address.1 ∈ instances ∧ UniqueIds (forests slot.address.1) ∧
      ∃ p ∈ visible (forests slot.address.1),
        addressOf slot.address.1 p.item.id = slot.address ∧ coordinate slot.address = p.entry

theorem plan_exact_coverage (doc : Document) (forests : Nat → Forest)
    (addressOf : Nat → NotionRunAllocation.Id → Address) (coordinate : Address → Nat)
    (targets : List Address) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (value : Bool)
    (related : DisplayCoordinates doc forests addressOf coordinate instances) :
    NotionCoreFormattingBridge.ExactCoverage doc forests coordinate
      (plan forests addressOf targets instances session counter value) targets := by
  intro block hb alive slot hs live
  obtain ⟨present, unique, p, hp, identity, position⟩ := related block hb alive slot hs live
  exact plan_exact_at forests addressOf coordinate targets instances session counter value slot.address
    present unique p hp identity position

/-- One atomic maximal-run plan refines the independent rich-view toggle. -/
theorem plan_refines_toggle (s : NotionCoreFormattingSpec.State) (forests : Nat → Forest)
    (addressOf : Nat → NotionRunAllocation.Id → Address) (coordinate : Address → Nat)
    (targets : List Address) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat)
    (related : DisplayCoordinates s.document forests addressOf coordinate instances) :
    NotionCoreFormattingSpec.richView
      (NotionCoreFormattingBridge.sourceUpdate s forests coordinate
        (plan forests addressOf targets instances session counter (NotionCoreFormattingSpec.toggleValue s targets))) =
      NotionCoreFormattingSpec.richView (NotionCoreFormattingSpec.toggle s targets) := by
  apply NotionCoreFormattingBridge.exact_coverage_refines_toggle
  · exact emit_uniform session counter _ _
  · exact plan_exact_coverage _ _ _ _ _ _ _ _ _ related

/-- Raw source-ID membership, as the candidate's per-instance `Set`. -/
def selectedAt (selection : List Character) (instanceId : Nat) (id : NotionRunAllocation.Id) : Bool :=
  selection.any fun c => decide (c.textInstance = instanceId) && (c.item.id == id)

private theorem physical_address_eq (i j : Nat) (x y : NotionRunAllocation.Id) :
    NotionCorePhysicalReplay.address i x = NotionCorePhysicalReplay.address j y ↔ i = j ∧ x = y := by
  constructor
  · intro same
    have first : i = j := congrArg Prod.fst same
    subst j
    exact ⟨rfl, NotionCorePhysicalReplay.address_injective i same⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Actual source keys and core semantic addresses have identical selection
membership. Session encoding injectivity is proved by PhysicalReplay. -/
theorem selectedAt_decoded (selection : List Character) (instanceId : Nat)
    (id : NotionRunAllocation.Id) :
    selectedAt selection instanceId id =
      (selection.map fun c => NotionCorePhysicalReplay.address c.textInstance c.item.id).contains
        (NotionCorePhysicalReplay.address instanceId id) := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedAt, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.contains_iff_mem, List.mem_map, physical_address_eq]

/-- Successful-input core of candidate `planToggle`. JavaScript additionally
checks duplicate selected addresses, selected visibility, and instance presence.
This total typed function omits exception machinery. Its scanner is the actual
maximal-run accumulator, not singleton intervals or a selected-ID renderer. -/
def planToggle (forests : Nat → Forest) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (selection : List Character) :=
  emit session counter (!(selection.all Character.bold))
    (instances.flatMap fun instanceId =>
      (segments (forests instanceId) (selectedAt selection instanceId)).map
        fun segment => (instanceId, segment))

theorem planToggle_eq_plan (forests : Nat → Forest) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (selection : List Character) :
    planToggle forests instances session counter selection =
      plan forests NotionCorePhysicalReplay.address
        (selection.map fun c => NotionCorePhysicalReplay.address c.textInstance c.item.id)
        instances session counter (!(selection.all Character.bold)) := by
  unfold planToggle plan locatedSegments
  congr 2
  funext instanceId
  congr 2
  funext id
  exact selectedAt_decoded selection instanceId id

/-- Display-order permutations preserve both maximal runs and the one global
verdict; this is a general theorem, not only an N002 fixture observation. -/
theorem planToggle_selection_perm (forests : Nat → Forest) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (left right : List Character)
    (permutation : left.Perm right) :
    planToggle forests instances session counter left = planToggle forests instances session counter right := by
  have chosen : ∀ instanceId, selectedAt left instanceId = selectedAt right instanceId := by
    intro instanceId
    funext id
    exact permutation.any_eq
  unfold planToggle
  rw [permutation.all_eq]
  simp_rw [chosen]

theorem planToggle_uniform (forests : Nat → Forest) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (selection : List Character)
    (operation : NotionCoreFormattingBridge.Located)
    (member : operation ∈ planToggle forests instances session counter selection) :
    operation.2.value = !(selection.all Character.bold) :=
  emit_uniform session counter _ _ operation member

theorem planToggle_exact_coverage (doc : Document) (forests : Nat → Forest)
    (coordinate : Address → Nat) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (selection : List Character)
    (related : DisplayCoordinates doc forests NotionCorePhysicalReplay.address coordinate instances) :
    NotionCoreFormattingBridge.ExactCoverage doc forests coordinate
      (planToggle forests instances session counter selection)
      (selection.map fun c => NotionCorePhysicalReplay.address c.textInstance c.item.id) := by
  rw [planToggle_eq_plan]
  exact plan_exact_coverage _ _ _ _ _ _ _ _ _ related

theorem planToggle_refines (s : NotionCoreFormattingSpec.State) (forests : Nat → Forest)
    (coordinate : Address → Nat) (instances : List Nat)
    (session : NotionRunAllocation.Session) (counter : Nat) (selection : List Character)
    (related : DisplayCoordinates s.document forests NotionCorePhysicalReplay.address coordinate instances)
    (issuer : selection.all Character.bold =
      (selection.map fun c => NotionCorePhysicalReplay.address c.textInstance c.item.id).all s.bold) :
    NotionCoreFormattingSpec.richView
      (NotionCoreFormattingBridge.sourceUpdate s forests coordinate
        (planToggle forests instances session counter selection)) =
      NotionCoreFormattingSpec.richView (NotionCoreFormattingSpec.toggle s
        (selection.map fun c => NotionCorePhysicalReplay.address c.textInstance c.item.id)) := by
  rw [planToggle_eq_plan, issuer]
  exact plan_refines_toggle s forests NotionCorePhysicalReplay.address coordinate _ instances session counter related

#print axioms anchor_before_entry
#print axioms segments_exact
#print axioms plan_exact_coverage
#print axioms plan_refines_toggle
#print axioms planToggle_exact_coverage
#print axioms planToggle_refines
#print axioms planToggle_selection_perm
end Sal.MRDTs.Instances.NotionCoreFormattingPlanner
