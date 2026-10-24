import Sal.MRDTs.Instances.NotionCoreRichPayload

/-! Repaired arbitration treats every formatting transaction as one boolean
assignment over a union of stable intervals. Segment IDs remain distinct,
while all segments share the transaction's arbitration priority and verdict.
The original per-segment evaluator and its obstruction remain unchanged.

Gap observations use lower < gap ≤ upper, the inheritance rule for the
planner's before-item/END boundaries. A raw START sentinel has different
prepend affinity and is not emitted by the supported formatting planner.
-/
namespace Sal.MRDTs.Instances.NotionCoreAtomicFormatting
open NotionRunAllocation (Id Before)
open NotionCoreOriginTree (Forest)
open NotionCoreFormattingSource (Anchor MarkOp anchorPosition)

structure Segment where
  instanceId : Nat
  id : Id
  lower : Anchor
  upper : Anchor
  deriving DecidableEq, Repr

structure Batch where
  priority : Id
  segments : List Segment
  value : Bool
  deriving DecidableEq, Repr

def Segment.operation (segment : Segment) (value : Bool) : MarkOp :=
  ⟨segment.id,segment.lower,segment.upper,value⟩

def Segment.ofLocated (located : Nat × MarkOp) : Segment :=
  ⟨located.1,located.2.id,located.2.start,located.2.finish⟩

/-- Forget only the per-segment reservation identity. Stable interval endpoints
and physical instance names are the original payload fields. -/
def Segment.part (segment : Segment) : NotionCoreRichPayload.Part :=
  ⟨segment.instanceId,segment.lower,segment.upper⟩

def Batch.ofFormat (priority : Id) (parts : List NotionCoreRichPayload.Part) (value : Bool) : Batch :=
  ⟨priority,(NotionCoreRichPayload.emit priority value parts).map Segment.ofLocated,value⟩

theorem ofFormat_parts (priority : Id) (parts : List NotionCoreRichPayload.Part) (value : Bool) :
    (Batch.ofFormat priority parts value).segments.map Segment.part = parts := by
  induction parts generalizing priority with
  | nil => rfl
  | cons part rest ih =>
    simpa only [Batch.ofFormat,NotionCoreRichPayload.emit,List.map_cons,Segment.ofLocated,
      NotionCoreRichPayload.Part.operation,Segment.part] using congrArg (part :: ·)
        (ih ⟨priority.counter + 1,priority.session⟩)

theorem ofFormat_filterMap {α : Type} (priority : Id) (parts : List NotionCoreRichPayload.Part)
    (value : Bool) (f : NotionCoreRichPayload.Part → Option α) :
    (Batch.ofFormat priority parts value).segments.filterMap (fun segment => f segment.part) =
      parts.filterMap f := by
  change (Batch.ofFormat priority parts value).segments.filterMap (f ∘ Segment.part) = _
  rw [← List.filterMap_map,ofFormat_parts]

def Batch.ofTransaction? (transaction : NotionCoreRichPayload.Transaction) : Option Batch :=
  match transaction.payload with
  | .edit _ => none
  | .format parts value => some (Batch.ofFormat transaction.id parts value)

theorem ofTransaction_priority (transaction : NotionCoreRichPayload.Transaction) (batch : Batch)
    (decoded : Batch.ofTransaction? transaction = some batch) : batch.priority = transaction.id := by
  cases transaction with
  | mk priority payload =>
    cases payload with
    | edit payload => simp [Batch.ofTransaction?] at decoded
    | format parts value =>
      simp only [Batch.ofTransaction?,Option.some.injEq] at decoded
      subst batch
      rfl

theorem ofFormat_segment_ids (priority : Id) (parts : List NotionCoreRichPayload.Part) (value : Bool) :
    (Batch.ofFormat priority parts value).segments.map Segment.id =
      (List.range parts.length).map (NotionCorePayload.offsetId priority) := by
  simpa only [Batch.ofFormat,List.map_map,Segment.ofLocated,Function.comp_def] using
    NotionCoreRichPayload.emit_ids priority value parts

theorem ofFormat_ids_unique (priority : Id) (parts : List NotionCoreRichPayload.Part) (value : Bool) :
    ((Batch.ofFormat priority parts value).segments.map Segment.id).Nodup := by
  simpa only [NotionCoreRichPayload.Transaction.annotations,Batch.ofFormat,List.map_map,
    Segment.ofLocated,Function.comp_def] using
    NotionCoreRichPayload.annotations_unique (⟨priority,.format parts value⟩ : NotionCoreRichPayload.Transaction)

def segmentCovers (forests : Nat → Forest) (segment : Segment) (inst index : Nat) : Bool :=
  (segment.instanceId == inst) &&
    NotionCoreFormattingSource.covers (forests inst) (segment.operation false) index

def covers (forests : Nat → Forest) (batch : Batch) (inst index : Nat) : Bool :=
  batch.segments.any (fun segment => segmentCovers forests segment inst index)

def segmentGapCovers (forests : Nat → Forest) (segment : Segment) (inst gap : Nat) : Bool :=
  (segment.instanceId == inst) &&
    match anchorPosition (forests inst) segment.lower, anchorPosition (forests inst) segment.upper with
    | some lo,some hi => decide (lo < gap ∧ gap ≤ hi)
    | _,_ => false

def gapCovers (forests : Nat → Forest) (batch : Batch) (inst gap : Nat) : Bool :=
  batch.segments.any (fun segment => segmentGapCovers forests segment inst gap)

def Ascending (left right : Batch) : Prop :=
  Before left.priority right.priority ∨ left.priority = right.priority
instance (left right : Batch) : Decidable (Ascending left right) :=
  inferInstanceAs (Decidable (Before left.priority right.priority ∨ left.priority = right.priority))

instance : Std.Total Ascending where
  total a b := by
    rcases NotionCoreSourceInvariant.before_trichotomy a.priority b.priority with before | same | reverse
    · exact Or.inl (Or.inl before)
    · exact Or.inl (Or.inr same)
    · exact Or.inr (Or.inl reverse)
instance : IsTrans Batch Ascending where
  trans a b c ab bc := by
    rcases ab with ab | ab <;> rcases bc with bc | bc
    · exact Or.inl (NotionCoreSourceInvariant.before_trans ab bc)
    · exact Or.inl (bc ▸ ab)
    · exact Or.inl (ab ▸ bc)
    · exact Or.inr (ab.trans bc)

def sort (batches : List Batch) : List Batch := batches.insertionSort Ascending

theorem sort_perm (batches : List Batch) : (sort batches).Perm batches := List.perm_insertionSort _ _
theorem sort_pairwise (batches : List Batch) : (sort batches).Pairwise Ascending :=
  List.pairwise_insertionSort _ _

def applyOrdered (covered : Batch → Bool) (batches : List Batch) (initial : Bool) : Bool :=
  batches.foldl (fun value batch => if covered batch then batch.value else value) initial

def resolveWith (covered : Batch → Bool) (batches : List Batch) : Bool :=
  applyOrdered covered (sort batches) false

theorem resolveWith_ordered (covered : Batch → Bool) (batches : List Batch)
    (ordered : batches.Pairwise Ascending) :
    resolveWith covered batches = applyOrdered covered batches false := by
  unfold resolveWith sort
  rw [ordered.insertionSort_eq]

def resolveAt (forests : Nat → Forest) (batches : List Batch) (inst index : Nat) : Bool :=
  resolveWith (fun batch => covers forests batch inst index) batches

def resolveGapAt (forests : Nat → Forest) (batches : List Batch) (inst gap : Nat) : Bool :=
  resolveWith (fun batch => gapCovers forests batch inst gap) batches

theorem applyOrdered_append (covered : Batch → Bool) (left right : List Batch) (initial : Bool) :
    applyOrdered covered (left ++ right) initial =
      applyOrdered covered right (applyOrdered covered left initial) := by
  simp [applyOrdered,List.foldl_append]

theorem untouched (covered : Batch → Bool) (batches : List Batch) (initial : Bool)
    (outside : ∀ batch ∈ batches, covered batch = false) :
    applyOrdered covered batches initial = initial := by
  induction batches generalizing initial with
  | nil => rfl
  | cons batch rest ih =>
      have first := outside batch (by simp)
      have tail : ∀ old ∈ rest, covered old = false := fun old member => outside old (by simp [member])
      simpa [applyOrdered,first] using ih initial tail

theorem last_covering (covered : Batch → Bool) (earlier later : List Batch) (batch : Batch)
    (initial : Bool) (inside : covered batch = true)
    (outside : ∀ old ∈ later, covered old = false) :
    applyOrdered covered (earlier ++ batch :: later) initial = batch.value := by
  rw [applyOrdered_append]
  simp only [applyOrdered,List.foldl_cons,inside,↓reduceIte]
  exact untouched covered later batch.value outside

private theorem insert_append_latest (batch : Batch) (old : List Batch) (latest : Batch)
    (before : Before batch.priority latest.priority) :
    List.orderedInsert Ascending batch (old ++ [latest]) =
      List.orderedInsert Ascending batch old ++ [latest] := by
  induction old with
  | nil => simp [List.orderedInsert,Ascending, before]
  | cons first rest ih =>
      by_cases head : Ascending batch first <;> simp [List.orderedInsert,head,ih]

/-- Fresh transaction priorities keep a complete batch after all earlier
batches, irrespective of its segment IDs or number of intervals. -/
theorem sort_append_latest (batches : List Batch) (latest : Batch)
    (fresh : ∀ old ∈ batches, Before old.priority latest.priority) :
    sort (batches ++ [latest]) = sort batches ++ [latest] := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      have first := fresh batch (by simp)
      have tail : ∀ old ∈ rest, Before old.priority latest.priority := fun old member => fresh old (by simp [member])
      simp only [List.cons_append,sort,List.insertionSort_cons]
      change List.orderedInsert Ascending batch (sort (rest ++ [latest])) = _
      rw [ih tail,insert_append_latest batch (sort rest) latest first]
      rfl

/-- Atomic assignment law. The new transaction chooses one value for every
covered character or gap; no segment can lose independently of its batch. -/
theorem resolve_latest (covered : Batch → Bool) (batches : List Batch) (latest : Batch)
    (fresh : ∀ old ∈ batches, Before old.priority latest.priority) :
    resolveWith covered (batches ++ [latest]) =
      if covered latest then latest.value else resolveWith covered batches := by
  simp [resolveWith,sort_append_latest batches latest fresh,applyOrdered]

theorem resolve_latest_at (forests : Nat → Forest) (batches : List Batch) (latest : Batch)
    (fresh : ∀ old ∈ batches, Before old.priority latest.priority) (inst index : Nat) :
    resolveAt forests (batches ++ [latest]) inst index =
      if covers forests latest inst index then latest.value else resolveAt forests batches inst index :=
  resolve_latest _ batches latest fresh

theorem resolve_latest_gap (forests : Nat → Forest) (batches : List Batch) (latest : Batch)
    (fresh : ∀ old ∈ batches, Before old.priority latest.priority) (inst gap : Nat) :
    resolveGapAt forests (batches ++ [latest]) inst gap =
      if gapCovers forests latest inst gap then latest.value else resolveGapAt forests batches inst gap :=
  resolve_latest _ batches latest fresh

#print axioms resolve_latest_at
#print axioms resolve_latest_gap
#print axioms ofFormat_ids_unique
end Sal.MRDTs.Instances.NotionCoreAtomicFormatting
