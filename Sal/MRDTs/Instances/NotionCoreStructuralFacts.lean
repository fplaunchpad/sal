import Sal.MRDTs.Instances.NotionCoreTableView
import Sal.MRDTs.Instances.FinsetStore

/-! Immutable structural facts for the typed core. This carrier contains no
transaction archive or query cache. Render correspondence is a separate
obligation: union laws alone do not establish document correctness. A merge
contributes no fact: its effect depends on replay order, so this carrier
covers the merge-free fragment. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralFacts
open NotionCorePayload (BlockKey Transaction)
open NotionCoreParentMap (Row)
open NotionRunAllocation (Id)

inductive Fact where
  | birth (inst : BlockKey) (row : Row)
  | erased (inst : BlockKey) (id : Id)
  | created (block : BlockKey) (afterBlock : Option BlockKey)
  | cut (inst : BlockKey) (marker : Id) (target : BlockKey)
  deriving DecidableEq, Repr

abbrev State := Finset Fact

def extra (tx : Transaction) : List Fact := match tx.payload with
  | .bootstrap _ => [.created .initial none]
  | .create afterBlock => [.created (.issued tx.id) afterBlock]
  | .insert _ _ _ _ => []
  | .erase _ groups => groups.flatMap fun group => group.2.map (Fact.erased group.1)
  | .split block inst _ =>
      [.created (.issued tx.id) (some block), .cut inst tx.id (.issued tx.id)]
  | .merge _ _ _ => []

def decodeList (tx : Transaction) : List Fact :=
  (NotionCorePayload.births tx (fun _ _ => false)).map
    (fun pair => Fact.birth pair.1 pair.2) ++ extra tx

def decode (tx : Transaction) : State := (decodeList tx).toFinset

def integrate (state : State) (tx : Transaction) : State := state ∪ decode tx

def merge (_base left right : State) : State := left ∪ right

def ofTransactions (txs : List Transaction) : State :=
  (txs.flatMap decodeList).toFinset

@[simp] theorem ofTransactions_nil : ofTransactions [] = ∅ := rfl

@[simp] theorem ofTransactions_cons (tx : Transaction) (txs : List Transaction) :
    ofTransactions (tx :: txs) = decode tx ∪ ofTransactions txs := by
  simp [ofTransactions, decode]

@[simp] theorem ofTransactions_append (a b : List Transaction) :
    ofTransactions (a ++ b) = ofTransactions a ∪ ofTransactions b := by
  simp [ofTransactions]

theorem integrate_comm (state : State) (a b : Transaction) :
    integrate (integrate state a) b = integrate (integrate state b) a := by
  simp [integrate, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

theorem integrate_idempotent (state : State) (tx : Transaction) :
    integrate (integrate state tx) tx = integrate state tx := by
  simp [integrate, Finset.union_assoc]

theorem ofTransactions_perm {a b : List Transaction} (same : a.Perm b) :
    ofTransactions a = ofTransactions b := by
  apply Finset.ext
  intro fact
  simp only [ofTransactions, List.mem_toFinset]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨tx, member, decoded⟩
    exact ⟨tx, same.mem_iff.mp member, decoded⟩
  · rintro ⟨tx, member, decoded⟩
    exact ⟨tx, same.mem_iff.mpr member, decoded⟩

/-- Late delivery inserts its structural facts without revisiting old
transactions, including when its source key precedes already received keys. -/
theorem late_integrate (before after : List Transaction) (tx : Transaction) :
    integrate (ofTransactions (before ++ after)) tx =
      ofTransactions (before ++ tx :: after) := by
  simp [integrate, Finset.union_left_comm, Finset.union_comm]

/-- The received archive is proof input only; the maintained carrier is the
union of structural facts. Ordinary and recursive bases use the same union. -/
theorem merge_correspondence (base left right : List Transaction) :
    merge (ofTransactions base) (ofTransactions left) (ofTransactions right) =
      ofTransactions (left ++ right) := by simp [merge]

@[simp] theorem birth_not_extra (tx : Transaction) (inst : BlockKey) (row : Row) :
    Fact.birth inst row ∉ extra tx := by
  cases tx with
  | mk id payload => cases payload <;> simp [extra]

@[simp] theorem birth_decodeList (tx : Transaction) (inst : BlockKey) (row : Row) :
    Fact.birth inst row ∈ decodeList tx ↔
      (inst,row) ∈ NotionCorePayload.births tx (fun _ _ => false) := by
  simp [decodeList]

/-- Direct origin-record membership exactly matches the existing reconstruction
invariant, without replaying a transaction or assuming query equality. -/
theorem birth_correspondence (txs : List Transaction) (inst : BlockKey) (row : Row) :
    Fact.birth inst row ∈ ofTransactions txs ↔
      row ∈ NotionCoreTableView.birthsRows txs inst := by
  simp only [ofTransactions, List.mem_toFinset, List.mem_flatMap,
    birth_decodeList, NotionCoreTableView.birthsRows,
    NotionCoreMachinePrefix.transaction_row_member]

@[simp] theorem erased_decodeList (tx : Transaction) (inst : BlockKey) (id : Id) :
    Fact.erased inst id ∈ decodeList tx ↔
      id ∈ NotionCoreTableView.transactionTargets tx inst := by
  cases tx with
  | mk key payload =>
    cases payload <;> simp [decodeList, extra, NotionCoreTableView.transactionTargets]

/-- Deletion identities are an independent monotone component; their receipt
order is absent from the representation. -/
theorem erased_correspondence (txs : List Transaction) (inst : BlockKey) (id : Id) :
    Fact.erased inst id ∈ ofTransactions txs ↔
      id ∈ NotionCoreTableView.targets txs inst := by
  simp only [ofTransactions, List.mem_toFinset, List.mem_flatMap,
    erased_decodeList, NotionCoreTableView.targets]

private def seed : Transaction := NotionCorePayload.bootstrap [97]
private def late : Transaction := ⟨⟨2,[66]⟩,.insert .initial .initial .start [88]⟩
private def early : Transaction := ⟨⟨2,[67]⟩,.insert .initial .initial .start [89]⟩

/-- Hand-derived birth and cut facts distinguish text, deletion and split.
This fixture tests decoding, not honest-protocol reachability. -/
theorem decode_control :
    Fact.birth .initial ⟨⟨⟨1,[65]⟩,.text 97 false⟩,.start⟩ ∈ decode seed ∧
    Fact.erased .initial ⟨1,[65]⟩ ∉ decode seed ∧
    Fact.cut .initial ⟨2,[66]⟩ (.issued ⟨2,[66]⟩) ∈
      decode ⟨⟨2,[66]⟩,.split .initial .initial .start⟩ := by decide +kernel

theorem late_control :
    integrate (ofTransactions [seed,early]) late = ofTransactions [seed,late,early] ∧
    integrate (ofTransactions [seed,early]) late ≠ ofTransactions [seed,early] := by
  constructor
  · exact late_integrate [seed] [early] late
  · decide +kernel

#print axioms late_integrate
#print axioms merge_correspondence
#print axioms decode_control
#print axioms late_control
end Sal.MRDTs.Instances.NotionCoreStructuralFacts
