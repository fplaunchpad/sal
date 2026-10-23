import Sal.MRDTs.Instances.NotionCoreMachine
import Sal.MRDTs.Instances.NotionCoreFormattingSource

/-! Staged executable integration of boolean annotations with the actual core
editing interpreter. Edit requests delegate to NotionCoreMachine unchanged;
format requests atomically retain a whole batch of instance/operation pairs.
Rich rendering reads the actual displayed slice atoms and resolves source
anchors against current physical instance trees on every query.

The projection theorems cover arbitrary states and failures. This wrapper does
not extend the production payload enum, validate format issuance, transport
atomic batches through an archive, or establish rich-text RA linearizability.
-/
namespace Sal.MRDTs.Instances.NotionCoreFormattingMachine
open NotionCoreFormattingSource (MarkOp Formatted)
open NotionCorePayload (Transaction)
open NotionCoreSpec (Address)
open NotionCoreOriginTree (Forest Origin preorder)
open NotionCoreParentMap (Table)
open NotionCoreSource (Atom)

structure State where
  core : NotionCoreMachine.State := {}
  annotations : List (Nat × MarkOp) := []
  deriving DecidableEq, Repr

inductive Request where
  | edit (transaction : Transaction)
  | format (operations : List (Nat × MarkOp))
  deriving DecidableEq, Repr

def applyRequest (state : State) : Request → Option State
  | .edit transaction => (NotionCoreMachine.applyTransaction state.core transaction).map
      fun core => {state with core := core}
  | .format operations => some {state with annotations := state.annotations ++ operations}

def replay : State → List Request → Option State
  | state, [] => some state
  | state, request :: rest => do replay (← applyRequest state request) rest

def eraseFormats : List Request → List Transaction
  | [] => []
  | .edit transaction :: rest => transaction :: eraseFormats rest
  | .format _ :: rest => eraseFormats rest

/-- A format request commits the complete operation batch in one step. -/
theorem format_atomic (state : State) (operations : List (Nat × MarkOp)) :
    applyRequest state (.format operations) =
      some ⟨state.core, state.annotations ++ operations⟩ := rfl

/-- Every replay has exactly the old core replay as its projection, including
failed edits and arbitrary malformed starting states. -/
theorem replay_core_projection (state : State) (requests : List Request) :
    (replay state requests).map State.core =
      NotionCoreMachine.replay state.core (eraseFormats requests) := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest ih =>
      cases request with
      | format operations =>
          simpa [replay, applyRequest, eraseFormats] using
            (ih {state with annotations := state.annotations ++ operations})
      | edit transaction =>
          cases executed : NotionCoreMachine.applyTransaction state.core transaction with
          | none => simp [replay, applyRequest, eraseFormats, NotionCoreMachine.replay, executed]
          | some core =>
              simpa [replay, applyRequest, eraseFormats, NotionCoreMachine.replay, executed]
                using (ih {state with core := core})

/-- Use the actual machine's structural child sorting, so this executable
frontend reduces in the kernel on the same concrete editing histories. -/
def extract : Nat → Table → Origin → Forest
  | 0, _, _ => .nil
  | fuel + 1, rows, origin =>
      NotionCoreParentMap.buildForest rows (fun id => extract fuel rows (.item id))
        (NotionCoreMachine.children rows origin)

theorem extract_correct (fuel : Nat) (rows : Table) (origin : Origin) :
    extract fuel rows origin = NotionCoreParentMap.extract fuel rows origin := by
  induction fuel generalizing origin with
  | zero => rfl
  | succ fuel ih => simp only [extract, NotionCoreParentMap.extract,
      NotionCoreMachine.children_correct, ih]

def instanceForest (state : State) (inst : Nat) : Forest :=
  let rows := (NotionCoreMachine.getInstance state.core inst).rows
  extract rows.length rows .start

/-- Formatting and editing use precisely the same current physical preorder.
Tombstones and split markers remain in it and retain anchor positions. -/
theorem instanceForest_traversal (state : State) (inst : Nat) :
    preorder (instanceForest state inst) =
      NotionCoreMachine.traversal
        (NotionCoreMachine.getInstance state.core inst).rows.length
        (NotionCoreMachine.getInstance state.core inst).rows .start := by
  rw [instanceForest, extract_correct, NotionCoreParentMap.extract_preorder,
    NotionCoreMachine.traversal_correct]

def instanceOperations (state : State) (inst : Nat) : List MarkOp :=
  state.annotations.filterMap fun (name, operation) => if name = inst then some operation else none

def resolvedInstance (state : State) (inst : Nat) : List Formatted :=
  NotionCoreFormattingSource.resolveRichText (instanceForest state inst) (instanceOperations state inst)

/-- Match source item identities to actual slice atoms through the production
physical-address encoding. Re-resolve anchors from current rows on each call;
there is no snapshot of item membership captured at format time. -/
def boldAt (state : State) (address : Address) : Bool :=
  ((resolvedInstance state address.1).find? fun formatted =>
    NotionCorePhysicalReplay.address address.1 formatted.item.id == address).map Formatted.bold |>.getD false

structure RichAtom where
  address : Address
  value : Nat
  bold : Bool
  deriving DecidableEq, Repr

def annotateAtom (state : State) (atom : Atom) : List RichAtom :=
  match atom.kind with
  | .text value false => [⟨atom.address, value, boldAt state atom.address⟩]
  | _ => []

def blockRich (state : State) (bid : Nat) : Option (List RichAtom) := do
  let block ← state.core.forest.find? (fun b => b.id == bid)
  let atoms ← NotionCoreMachine.treeAtoms state.core block.title
  pure (atoms.flatMap (annotateAtom state))

def render (state : State) : Option (List (Nat × List RichAtom)) :=
  (NotionCoreMachine.visible state.core).mapM fun bid => do pure (bid, ← blockRich state bid)

def forget (document : List (Nat × List RichAtom)) : List (Nat × List Nat) :=
  document.map fun (bid, atoms) => (bid, atoms.map RichAtom.value)

theorem annotateAtom_forget (state : State) (atom : Atom) :
    (annotateAtom state atom).map RichAtom.value = NotionCoreMachine.atomText atom := by
  cases kind : atom.kind with
  | split => simp [annotateAtom, NotionCoreMachine.atomText, kind]
  | text value deleted => cases deleted <;> simp [annotateAtom, NotionCoreMachine.atomText, kind]

theorem annotateAtoms_forget (state : State) (atoms : List Atom) :
    (atoms.flatMap (annotateAtom state)).map RichAtom.value =
      atoms.flatMap NotionCoreMachine.atomText := by
  simp only [List.map_flatMap, annotateAtom_forget]

/-- No successful or failing block query is changed by adding formatting. -/
theorem blockRich_forget (state : State) (bid : Nat) :
    (blockRich state bid).map (List.map RichAtom.value) =
      NotionCoreMachine.blockText state.core bid := by
  unfold blockRich NotionCoreMachine.blockText
  cases found : state.core.forest.find? (fun b => b.id == bid) with
  | none => simp
  | some block =>
      cases atoms : NotionCoreMachine.treeAtoms state.core block.title with
      | none => simp [atoms]
      | some items => simp [atoms, annotateAtoms_forget]

private theorem renderList_forget (state : State) (blocks : List Nat) :
    ((blocks.mapM fun bid => do pure (bid, ← blockRich state bid)).map forget) =
      (blocks.mapM fun bid => do pure (bid, ← NotionCoreMachine.blockText state.core bid)) := by
  induction blocks with
  | nil => rfl
  | cons bid rest ih =>
      have projected := blockRich_forget state bid
      cases rich : blockRich state bid with
      | none =>
          have plain : NotionCoreMachine.blockText state.core bid = none := by
            simpa [rich] using projected.symm
          simp [List.mapM_cons, rich, plain]
      | some atoms =>
          have plain : NotionCoreMachine.blockText state.core bid = some (atoms.map RichAtom.value) := by
            simpa [rich] using projected.symm
          simp only [List.mapM_cons, rich, plain]
          cases tail : rest.mapM (fun bid => do pure (bid, ← blockRich state bid)) with
          | none =>
              have tailPlain : (rest.mapM fun bid => do pure (bid, ← NotionCoreMachine.blockText state.core bid)) = none := by
                rw [tail] at ih
                exact ih.symm
              rw [tailPlain]
              rfl
          | some document =>
              have tailPlain : (rest.mapM fun bid => do pure (bid, ← NotionCoreMachine.blockText state.core bid)) = some (forget document) := by
                rw [tail] at ih
                exact ih.symm
              rw [tailPlain]
              rfl

/-- Forgetting rich flags and retained identities returns the actual machine
render exactly, for every state. Failures stay failures without reachability
or well-formedness assumptions. -/
theorem render_forget (state : State) :
    (render state).map forget = NotionCoreMachine.render state.core :=
  renderList_forget state (NotionCoreMachine.visible state.core)

/-- Whole replay conservatively extends the actual plain editing query. -/
theorem replay_render_forget (state : State) (requests : List Request) :
    ((replay state requests >>= render).map forget) =
      (NotionCoreMachine.replay state.core (eraseFormats requests) >>= NotionCoreMachine.render) := by
  have projected := replay_core_projection state requests
  cases executed : replay state requests with
  | none =>
      have plain : NotionCoreMachine.replay state.core (eraseFormats requests) = none := by
        simpa [executed] using projected.symm
      simp [plain]
  | some result =>
      have plain : NotionCoreMachine.replay state.core (eraseFormats requests) = some result.core := by
        simpa [executed] using projected.symm
      simpa [executed, plain] using render_forget result

#print axioms instanceForest_traversal
#print axioms replay_core_projection
#print axioms render_forget
#print axioms replay_render_forget
end Sal.MRDTs.Instances.NotionCoreFormattingMachine
