import Sal.MRDTs.Instances.NotionCoreMachinePrefix
import Sal.MRDTs.Instances.NotionCoreRanges

/-! Declarative full-prefix table contents: decoded births in transaction order,
with all prefix deletion targets applied. This is not a second document replay
or a sequential specification. It exposes the storage invariant required to
connect the actual machine to the existing archive graph proofs. -/
namespace Sal.MRDTs.Instances.NotionCoreTableView
open NotionRunAllocation (Id)
open NotionCorePayload (BlockKey Payload Transaction Operation)
open NotionCoreOriginTree (Item Origin)
open NotionCoreParentMap (Row Table)
open NotionCoreParentErase (erase eraseRow eraseItem)
open NotionCoreMachinePrefix (transactionRows)

def transactionTargets (tx : Transaction) (inst : BlockKey) : List Id :=
  match tx.payload with
  | .erase _ groups => groups.flatMap fun group => if group.1 = inst then group.2 else []
  | _ => []

def targets (txs : List Transaction) (inst : BlockKey) : List Id :=
  txs.flatMap (transactionTargets · inst)

def birthsRows (txs : List Transaction) (inst : BlockKey) : Table :=
  txs.flatMap (transactionRows · inst (fun _ _ => false))

def rows (txs : List Transaction) (inst : BlockKey) : Table :=
  erase (targets txs inst) (birthsRows txs inst)

@[simp] theorem erase_empty (table : Table) : erase [] table = table := by
  have same : eraseRow [] = id := by
    funext row
    cases row with
    | mk item origin => cases item with
      | mk id kind => cases kind <;> simp [eraseRow, eraseItem]
  simp [erase, same]

theorem erase_append (ids : List Id) (a b : Table) :
    erase ids (a ++ b) = erase ids a ++ erase ids b := by simp [erase]

theorem erase_targets_append (a b : List Id) (table : Table) :
    erase (a ++ b) table = erase b (erase a table) := by
  simp only [erase, List.map_map]
  apply List.map_congr_left
  intro row _
  cases row with
  | mk item origin => cases item with
    | mk id kind => cases kind <;>
      simp [eraseRow, eraseItem, List.mem_append, Bool.or_assoc]

theorem erase_commute (a b : List Id) (table : Table) :
    erase a (erase b table) = erase b (erase a table) := by
  rw [← erase_targets_append, ← erase_targets_append]
  exact NotionCoreRanges.erase_permutation _ _ (List.perm_append_comm (l₁ := b) (l₂ := a)) table

theorem runRows_erase (ids : List Id) (origin : Origin) (items : List Item) :
    NotionCoreParentMap.runRows origin (items.map (eraseItem ids)) =
      erase ids (NotionCoreParentMap.runRows origin items) := by
  induction items generalizing origin with
  | nil => rfl
  | cons item rest ih => simp [NotionCoreParentMap.runRows, erase, eraseRow, ih]

theorem textItems_erase (ids : List Id) (first : Id) (atoms : List Nat) (deleted : Id → Bool) :
    (NotionCorePayload.textItems first atoms deleted).map (eraseItem ids) =
      NotionCorePayload.textItems first atoms (fun id => deleted id || decide (id ∈ ids)) := by
  simp [NotionCorePayload.textItems, List.map_map, Function.comp_def, eraseItem]

private theorem filter_none {α β : Type} (xs : List α) :
    xs.filterMap (fun _ => (none : Option β)) = [] := by
  induction xs <;> simp_all

theorem transactionRows_erase (ids : List Id) (tx : Transaction) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) :
    erase ids (transactionRows tx inst deleted) =
      transactionRows tx inst (fun key id => deleted key id || decide (id ∈ ids)) := by
  cases tx with
  | mk first payload =>
    cases payload with
    | bootstrap atoms =>
      by_cases same : BlockKey.initial = inst
      · simp [transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
          Operation.births, List.filterMap_map, Function.comp_def, same]
        rw [← runRows_erase, textItems_erase]
      · simp [transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
          Operation.births, List.filterMap_map, Function.comp_def, same, filter_none, erase]
    | insert block key origin atoms =>
      by_cases same : key = inst
      · simp [transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
          Operation.births, List.filterMap_map, Function.comp_def, same]
        rw [← runRows_erase, textItems_erase]
      · simp [transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
          Operation.births, List.filterMap_map, Function.comp_def, same, filter_none, erase]
    | split block key origin =>
      by_cases same : key = inst <;>
        simp [transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
          Operation.births, same, erase, eraseRow, eraseItem]
    | create afterBlock => simp [transactionRows, NotionCorePayload.births,
        NotionCorePayload.operations, Operation.births, erase]
    | erase block groups => simp [transactionRows, erase]
    | merge source target => simp [transactionRows, NotionCorePayload.births,
        NotionCorePayload.operations, Operation.births, erase]

theorem transactionRows_pending (ids : List Id) (tx : Transaction) (inst : BlockKey) :
    transactionRows tx inst (fun _ id => decide (id ∈ ids)) =
      erase ids (transactionRows tx inst (fun _ _ => false)) := by
  simpa using (transactionRows_erase ids tx inst (fun _ _ => false)).symm

@[simp] theorem targets_append (a b : List Transaction) (inst : BlockKey) :
    targets (a ++ b) inst = targets a inst ++ targets b inst := by simp [targets]

@[simp] theorem birthsRows_append (a b : List Transaction) (inst : BlockKey) :
    birthsRows (a ++ b) inst = birthsRows a inst ++ birthsRows b inst := by simp [birthsRows]

theorem rows_append (a b : List Transaction) (inst : BlockKey) :
    rows (a ++ b) inst =
      erase (targets b inst) (rows a inst) ++
      erase (targets a inst) (rows b inst) := by
  simp only [rows, targets_append, birthsRows_append, erase_append]
  congr 1
  · exact erase_targets_append _ _ _
  · rw [erase_targets_append]
    exact erase_commute _ _ _

/-- All previous and later deletions can be read at each birth; the resulting
row list keeps chronological birth order and every original parent link. -/
theorem rows_flatMap (txs : List Transaction) (inst : BlockKey) :
    rows txs inst = txs.flatMap (fun tx => transactionRows tx inst
      (fun _ id => decide (id ∈ targets txs inst))) := by
  unfold rows birthsRows erase
  rw [List.map_flatMap]
  apply congrArg (fun f => txs.flatMap f)
  funext tx
  exact (transactionRows_pending (targets txs inst) tx inst).symm

private def a : Id := ⟨1,[65]⟩
private def marker : Id := ⟨2,[66]⟩
private def fixture : List Transaction :=
  [⟨⟨1,[69]⟩,.erase .initial [(.initial,[a,marker])]⟩,
   NotionCorePayload.bootstrap [97], ⟨marker,.split .initial .initial (.item a)⟩]

/-- PASS+FAIL: pending deletion tombstones a later text birth, while a marker
retains its split kind even when a raw delete names its ID. -/
theorem pending_birth_control :
    rows fixture .initial = [⟨⟨a,.text 97 true⟩,.start⟩,⟨⟨marker,.split⟩,.item a⟩] ∧
    rows fixture .initial ≠ [⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨marker,.split⟩,.item a⟩] ∧
    rows fixture (.issued marker) = [] := by decide +kernel

#print axioms rows_append
#print axioms transactionRows_pending
#print axioms rows_flatMap
#print axioms pending_birth_control
end Sal.MRDTs.Instances.NotionCoreTableView
