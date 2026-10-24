import Sal.MRDTs.Instances.NotionCoreAtomicFormatting

/-! Actual editing-core integration for shared-priority formatting batches.
The plain tree/slice renderer is reused; only boolean marks are replaced.
Every query resolves all batch intervals against current physical trees.
-/
namespace Sal.MRDTs.Instances.NotionCoreAtomicFormattingMachine
open NotionCoreAtomicFormatting (Batch)
open NotionCoreRichPayload (Transaction)
open NotionCoreSpec (Address)
open NotionCoreFormattingSource (Formatted)

structure State where
  core : NotionCoreMachine.State := {}
  batches : List Batch := []
  deriving DecidableEq, Repr

abbrev RichAtom := NotionCoreFormattingMachine.RichAtom
abbrev View := List (Nat × List RichAtom)

namespace RichAtom
abbrev address (atom : RichAtom) : Address := NotionCoreFormattingMachine.RichAtom.address atom
abbrev value (atom : RichAtom) : Nat := NotionCoreFormattingMachine.RichAtom.value atom
abbrev bold (atom : RichAtom) : Bool := NotionCoreFormattingMachine.RichAtom.bold atom
end RichAtom

def plainState (state : State) : NotionCoreFormattingMachine.State := ⟨state.core,[]⟩

def instanceForest (state : State) (inst : Nat) : NotionCoreOriginTree.Forest :=
  NotionCoreFormattingMachine.instanceForest (plainState state) inst

theorem instanceForest_traversal (state : State) (inst : Nat) :
    NotionCoreOriginTree.preorder (instanceForest state inst) =
      NotionCoreMachine.traversal
        (NotionCoreMachine.getInstance state.core inst).rows.length
        (NotionCoreMachine.getInstance state.core inst).rows .start :=
  NotionCoreFormattingMachine.instanceForest_traversal (plainState state) inst

def formatPosition (state : State) (inst : Nat) (position : NotionCoreFormattingSource.Positioned) : Option Formatted :=
    match position.item.kind with
    | .text _ false => some ⟨position.item,NotionCoreAtomicFormatting.resolveAt
        (instanceForest state) state.batches inst position.entry⟩
    | _ => none

def resolvePositions (state : State) (inst : Nat) (positions : List NotionCoreFormattingSource.Positioned) : List Formatted :=
  positions.filterMap (formatPosition state inst)

def resolvedInstance (state : State) (inst : Nat) : List Formatted :=
  resolvePositions state inst (NotionCoreFormattingSource.walk 0 (instanceForest state inst))

def boldAt (state : State) (address : Address) : Bool :=
  ((resolvedInstance state address.1).find? fun formatted =>
    NotionCorePhysicalReplay.address address.1 formatted.item.id == address).map Formatted.bold |>.getD false

theorem find_resolvePositions (state : State) (inst : Nat)
    (positions : List NotionCoreFormattingSource.Positioned)
    (unique : (positions.map (fun p => p.item.id)).Nodup)
    (position : NotionCoreFormattingSource.Positioned) (member : position ∈ positions)
    (value : Nat) (live : position.item.kind = .text value false) :
    ((resolvePositions state inst positions).find? fun formatted =>
      NotionCorePhysicalReplay.address inst formatted.item.id ==
        NotionCorePhysicalReplay.address inst position.item.id).map Formatted.bold =
      some (NotionCoreAtomicFormatting.resolveAt (instanceForest state) state.batches inst position.entry) := by
  induction positions with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | later
      · subst position
        simp [resolvePositions,formatPosition,live]
      · have distinct : first.item.id ≠ position.item.id := by
          intro same
          exact fresh (List.mem_map.mpr ⟨position,later,same.symm⟩)
        have apart : NotionCorePhysicalReplay.address inst first.item.id ≠
            NotionCorePhysicalReplay.address inst position.item.id :=
          fun same => distinct (NotionCorePhysicalReplay.address_injective inst same)
        have tail := ih tailUnique later
        cases firstKind : first.item.kind with
        | split => simpa [resolvePositions,formatPosition,firstKind] using tail
        | text content deleted =>
          cases deleted <;> simpa [resolvePositions,formatPosition,firstKind,apart] using tail

/-- Concrete retained-identity lookup agrees with the physical-coordinate
batch read. The source walk itself supplies positions; no desired read or
coordinate equation is assumed. -/
theorem boldAt_positioned (state : State) (inst : Nat)
    (unique : NotionCoreFormattingPlanner.UniqueIds (instanceForest state inst))
    (position : NotionCoreFormattingSource.Positioned)
    (member : position ∈ NotionCoreFormattingSource.walk 0 (instanceForest state inst))
    (value : Nat) (live : position.item.kind = .text value false) :
    boldAt state (NotionCorePhysicalReplay.address inst position.item.id) =
      NotionCoreAtomicFormatting.resolveAt (instanceForest state) state.batches inst position.entry := by
  have ids : ((NotionCoreFormattingSource.walk 0 (instanceForest state inst)).map
      (fun p => p.item.id)).Nodup := by
    have mapped : ((NotionCoreFormattingSource.walk 0 (instanceForest state inst)).map
        NotionCoreFormattingSource.Positioned.item |>.map (·.id)).Nodup := by
      rw [NotionCoreFormattingSource.walk_items]
      exact unique
    simpa only [List.map_map] using mapped
  have found := find_resolvePositions state inst _ ids position member value live
  change (Option.map Formatted.bold ((resolvePositions state inst
      (NotionCoreFormattingSource.walk 0 (instanceForest state inst))).find? fun formatted =>
    NotionCorePhysicalReplay.address inst formatted.item.id ==
      NotionCorePhysicalReplay.address inst position.item.id)).getD false = _
  rw [found]
  rfl

def gapBoldAt (state : State) (inst gap : Nat) : Bool :=
  NotionCoreAtomicFormatting.resolveGapAt (instanceForest state) state.batches inst gap

def markAtom (state : State) (atom : RichAtom) : RichAtom :=
  {atom with bold := boldAt state atom.address}

def markDocument (state : State) (document : View) : View :=
  document.map fun (bid,atoms) => (bid,atoms.map (markAtom state))

def blockRich (state : State) (bid : Nat) : Option (List RichAtom) :=
  (NotionCoreFormattingMachine.blockRich (plainState state) bid).map (List.map (markAtom state))

def render (state : State) : Option View :=
  (NotionCoreFormattingMachine.render (plainState state)).map (markDocument state)

abbrev forget := NotionCoreFormattingMachine.forget

theorem forget_markDocument (state : State) (document : View) :
    forget (markDocument state document) = forget document := by
  simp only [forget,NotionCoreFormattingMachine.forget,markDocument,List.map_map,
    Function.comp_def,markAtom]

theorem blockRich_forget (state : State) (bid : Nat) :
    (blockRich state bid).map (List.map RichAtom.value) = NotionCoreMachine.blockText state.core bid := by
  have plain := NotionCoreFormattingMachine.blockRich_forget (plainState state) bid
  simpa only [blockRich,Option.map_map,List.map_map,Function.comp_def,markAtom] using plain

/-- Shared-priority repair preserves the actual plain editing result, including
query failures, without any reachability or completed-state invariant premise. -/
theorem render_forget (state : State) :
    (render state).map forget = NotionCoreMachine.render state.core := by
  simpa only [render,Option.map_map,Function.comp_def,forget_markDocument] using
    NotionCoreFormattingMachine.render_forget (plainState state)

def applyTransaction (state : State) (transaction : Transaction) : Option State :=
  match transaction.payload with
  | .edit payload => (NotionCoreMachine.applyTransaction state.core ⟨transaction.id,payload⟩).map
      fun core => {state with core := core}
  | .format parts value => some {state with batches :=
      state.batches ++ [Batch.ofFormat transaction.id parts value]}

def replay : State → List Transaction → Option State
  | state,[] => some state
  | state,transaction :: rest => do replay (← applyTransaction state transaction) rest

def eraseFormats : List Transaction → List NotionCorePayload.Transaction
  | [] => []
  | transaction :: rest => match transaction.payload with
    | .edit payload => ⟨transaction.id,payload⟩ :: eraseFormats rest
    | .format _ _ => eraseFormats rest

def transactionBatches (transactions : List Transaction) : List Batch :=
  transactions.filterMap Batch.ofTransaction?

theorem applyTransaction_batches (state result : State) (transaction : Transaction)
    (accepted : applyTransaction state transaction = some result) :
    result.batches = state.batches ++ (Batch.ofTransaction? transaction).toList := by
  cases transaction with
  | mk id payload =>
    cases payload with
    | format parts value =>
      simp only [applyTransaction,Option.some.injEq] at accepted
      subst result
      rfl
    | edit payload =>
      cases executed : NotionCoreMachine.applyTransaction state.core ⟨id,payload⟩ with
      | none => simp [applyTransaction,executed] at accepted
      | some core =>
        simp only [applyTransaction,executed,Option.map_some,Option.some.injEq] at accepted
        subst result
        simp [Batch.ofTransaction?]

/-- Batches in a reconstructed state come from whole retained transactions,
not an independently supplied annotation store or a completed integrity fact. -/
theorem replay_batches (state result : State) (transactions : List Transaction)
    (accepted : replay state transactions = some result) :
    result.batches = state.batches ++ transactionBatches transactions := by
  induction transactions generalizing state with
  | nil => simp only [replay,Option.some.injEq] at accepted; subst result; simp [transactionBatches]
  | cons transaction rest ih =>
    obtain ⟨middle,first,later⟩ := Option.bind_eq_some_iff.mp accepted
    rw [ih middle later,applyTransaction_batches state middle transaction first]
    cases decoded : Batch.ofTransaction? transaction <;>
      simp [transactionBatches,decoded,List.append_assoc]

theorem format_atomic (state : State) (id : NotionRunAllocation.Id)
    (parts : List NotionCoreRichPayload.Part) (value : Bool) :
    applyTransaction state ⟨id,.format parts value⟩ =
      some ⟨state.core,state.batches ++ [Batch.ofFormat id parts value]⟩ := rfl

theorem replay_core_projection (state : State) (transactions : List Transaction) :
    (replay state transactions).map State.core =
      NotionCoreMachine.replay state.core (eraseFormats transactions) := by
  induction transactions generalizing state with
  | nil => rfl
  | cons transaction rest ih =>
      cases transaction with
      | mk id payload =>
        cases payload with
        | format parts value =>
          simpa [replay,applyTransaction,eraseFormats] using
            (ih {state with batches := state.batches ++ [Batch.ofFormat id parts value]})
        | edit payload =>
          cases executed : NotionCoreMachine.applyTransaction state.core ⟨id,payload⟩ with
          | none => simp [replay,applyTransaction,eraseFormats,NotionCoreMachine.replay,executed]
          | some core => simpa [replay,applyTransaction,eraseFormats,NotionCoreMachine.replay,executed]
              using (ih {state with core := core})

theorem replay_render_forget (state : State) (transactions : List Transaction) :
    ((replay state transactions >>= render).map forget) =
      (NotionCoreMachine.replay state.core (eraseFormats transactions) >>= NotionCoreMachine.render) := by
  have projected := replay_core_projection state transactions
  cases executed : replay state transactions with
  | none =>
      have plain : NotionCoreMachine.replay state.core (eraseFormats transactions) = none := by
        simpa [executed] using projected.symm
      simp [plain]
  | some result =>
      have plain : NotionCoreMachine.replay state.core (eraseFormats transactions) = some result.core := by
        simpa [executed] using projected.symm
      simpa [executed,plain] using render_forget result

#print axioms render_forget
#print axioms replay_render_forget
#print axioms boldAt_positioned
end Sal.MRDTs.Instances.NotionCoreAtomicFormattingMachine
