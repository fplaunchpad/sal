import Sal.MRDTs.Instances.TreeMove
import Sal.MRDTs.GC.StateComposition

/-!
# TreeMove log and materialized-state collection

The generic distributed collector removes commit-DAG history.  This module
handles the two TreeMove representation layers that remain inside a retained
version: a stable prefix of move events and the hidden trash subtree.
-/

namespace Sal.MRDTs.Instances.TreeMove.GC

open Sal.MRDTs Foundation Classical
open Sal.MRDTs.Instances.TreeMove

noncomputable def replayFrom (base : Tree) (events : List Event) : Tree :=
  events.foldl (fun t e => doMove t e.2.2) base

theorem replayFrom_append (base : Tree) (left right : List Event) :
    replayFrom base (left ++ right) = replayFrom (replayFrom base left) right := by
  simp [replayFrom, List.foldl_append]

theorem replayList_eq_replayFrom (events : List Event) :
    replayList events = replayFrom emptyTree events := rfl

/-- Frontier evidence chooses an exact stable prefix of canonical replay.
The prefix itself is proof data and need not remain in the compact runtime. -/
structure StableCut (full : Finset Event) where
  stable : List Event
  pending : List Event
  split : orderedEvents full = stable ++ pending

structure Compact where
  base : Tree
  pending : List Event

noncomputable def collectPrefix {full : Finset Event}
  (cut : StableCut full) : Compact :=
  ⟨replayFrom emptyTree cut.stable, cut.pending⟩

noncomputable def materialize (compact : Compact) : Tree :=
  replayFrom compact.base compact.pending

noncomputable def query (compact : Compact) : Tree :=
  Sal.MRDTs.Instances.TreeMove.visibleTree (materialize compact)

def Exact (compact : Compact) (full : Finset Event) : Prop :=
  materialize compact = render full

def Represents (compact : Compact) (full : Finset Event) : Prop :=
  query compact = D.query full ()

theorem collectPrefix_exact {full : Finset Event}
    (cut : StableCut full) : Exact (collectPrefix cut) full := by
  unfold Exact collectPrefix materialize render
  rw [cut.split, replayList_eq_replayFrom, replayFrom_append]

theorem collectPrefix_represents {full : Finset Event}
    (cut : StableCut full) : Represents (collectPrefix cut) full := by
  unfold Represents query D
  rw [collectPrefix_exact cut]

theorem collectPrefix_query {full : Finset Event}
    (cut : StableCut full) : query (collectPrefix cut) = D.query full () :=
  collectPrefix_represents cut

theorem orderedEvents_insert_last (full : Finset Event) (fresh : Event)
    (hnew : fresh ∉ full)
    (hlast : ∀ old ∈ full, eventLE old fresh) :
    orderedEvents (insert fresh full) = orderedEvents full ++ [fresh] := by
  have hn : (orderedEvents full ++ [fresh]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.sort_nodup _ _, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact fun h => hnew (h ▸ (Finset.mem_sort eventLE |>.mp hx))
  have hp : (orderedEvents full ++ [fresh]).Pairwise eventLE := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, (by simp), ?_⟩
    intro old hold x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact hlast old (Finset.mem_sort eventLE |>.mp hold)
  have hfin : (orderedEvents full ++ [fresh]).toFinset = insert fresh full := by
    ext x
    simp [orderedEvents]
  rw [← hfin]
  exact (List.toFinset_sort (r := eventLE) hn).2 hp

noncomputable def appendFresh (compact : Compact) (fresh : Event) : Compact :=
  ⟨compact.base, compact.pending ++ [fresh]⟩

theorem appendFresh_materialize (compact : Compact) (fresh : Event) :
    materialize (appendFresh compact fresh) =
      doMove (materialize compact) fresh.2.2 := by
  simp [materialize, appendFresh, replayFrom, List.foldl_append]

theorem appendFresh_exact {compact : Compact} {full : Finset Event}
    (hexact : Exact compact full) (fresh : Event)
    (hnew : fresh ∉ full)
    (hlast : ∀ old ∈ full, eventLE old fresh) :
    Exact (appendFresh compact fresh) (insert fresh full) := by
  unfold Exact at hexact ⊢
  rw [appendFresh_materialize, hexact]
  unfold render
  rw [orderedEvents_insert_last full fresh hnew hlast]
  simp [replayList, List.foldl_append]

/-- The incremental undo/redo implementation may choose any split around the
new event.  If undo, insertion, and redo reconstruct the canonical ordered
log, its materialized tree equals canonical replay. -/
structure UndoRedoWitness (old : Finset Event) (fresh : Event) where
  before : List Event
  after : List Event
  oldSplit : orderedEvents old = before ++ after
  newSplit : orderedEvents (insert fresh old) = before ++ fresh :: after

theorem orderedEvents_insert (old : Finset Event) (fresh : Event)
    (hnew : fresh ∉ old) :
    orderedEvents (insert fresh old) =
      (orderedEvents old).orderedInsert eventLE fresh := by
  apply List.Perm.eq_of_pairwise' (r := eventLE)
  · exact Finset.pairwise_sort _ _
  · exact (Finset.pairwise_sort old eventLE).orderedInsert fresh _
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.sort_nodup _ _
    · apply (List.perm_orderedInsert (r := eventLE) fresh
        (orderedEvents old)).nodup_iff.mpr
      apply List.nodup_cons.mpr
      constructor
      · simpa [orderedEvents] using hnew
      · exact Finset.sort_nodup _ _
    · ext x
      simp [orderedEvents, List.mem_orderedInsert]

noncomputable def undoRedoWitness (old : Finset Event) (fresh : Event)
    (hnew : fresh ∉ old) : UndoRedoWitness old fresh where
  before := (orderedEvents old).takeWhile (fun b => decide ¬ eventLE fresh b)
  after := (orderedEvents old).dropWhile (fun b => decide ¬ eventLE fresh b)
  oldSplit := (List.takeWhile_append_dropWhile).symm
  newSplit := by
    rw [orderedEvents_insert old fresh hnew,
      List.orderedInsert_eq_take_drop]

noncomputable def undoRedoResult {old : Finset Event} {fresh : Event}
    (w : UndoRedoWitness old fresh) : Tree :=
  replayFrom (replayFrom emptyTree w.before) (fresh :: w.after)

theorem undoRedo_refines_canonical {old : Finset Event} {fresh : Event}
    (w : UndoRedoWitness old fresh) :
    undoRedoResult w = render (insert fresh old) := by
  unfold undoRedoResult render
  rw [w.newSplit, replayList_eq_replayFrom, replayFrom_append]

theorem undoRedo_algorithm_refines (old : Finset Event) (fresh : Event)
    (hnew : fresh ∉ old) :
    undoRedoResult (undoRedoWitness old fresh hnew) =
      render (insert fresh old) :=
  undoRedo_refines_canonical _

/-- Once the entire event log is stable, the compact state contains only its
materialized base tree. -/
noncomputable def fullyStableCut (full : Finset Event) : StableCut full where
  stable := orderedEvents full
  pending := []
  split := by simp

theorem fullyStable_has_empty_suffix (full : Finset Event) :
    (collectPrefix (fullyStableCut full)).pending = [] := rfl

/-- Removing the hidden trash closure is a concrete materialized-state GC. -/
noncomputable def collectTrash (compact : Compact) : Compact :=
  ⟨Sal.MRDTs.Instances.TreeMove.visibleTree compact.base, compact.pending⟩

theorem collectTrash_query_of_empty_suffix (compact : Compact)
    (h : compact.pending = []) :
    query (collectTrash compact) = query compact := by
  rcases compact with ⟨base, pending⟩
  dsimp at h ⊢
  subst pending
  unfold query collectTrash materialize replayFrom
  simpa using Sal.MRDTs.Instances.TreeMove.visibleTree_idempotent base

theorem fullyStable_collectTrash_query (full : Finset Event) :
    query (collectTrash (collectPrefix (fullyStableCut full))) =
      D.query full () := by
  rw [collectTrash_query_of_empty_suffix _ (fullyStable_has_empty_suffix full)]
  exact collectPrefix_query (fullyStableCut full)

/-! The distributed frontier is the authority for declaring `prefix` stable.
The datatype proof consumes only the resulting exact split; commit-history
collection and state collection then compose through `combinedProtocol`. -/

def FrontierAuthorizes (parents : Version → List Version)
    (author : Sal.MRDTs.GC.Author) (roster : Set Replica) (self : Replica)
    {full : Finset Event} (cut : StableCut full)
    (replicaState : Sal.MRDTs.GC.Local) : Prop :=
  Sal.MRDTs.GC.EvidenceComplete parents author roster self replicaState ∧
  ∀ e ∈ cut.stable, ∀ future ∈ cut.pending, eventLE e future

theorem authorized_cut_query (parents : Version → List Version)
    (author : Sal.MRDTs.GC.Author) (roster : Set Replica) (self : Replica)
    {full : Finset Event} (cut : StableCut full)
    {replicaState : Sal.MRDTs.GC.Local}
    (_ : FrontierAuthorizes parents author roster self cut replicaState) :
    query (collectPrefix cut) = D.query full () :=
  collectPrefix_query cut

/-! ## Operational package and composition with distributed commit GC -/

structure Physical where
  semantic : Configuration D
  compact : Version → Option Compact
  sound : ∀ {v full events compactState},
    semantic.ver v = some (full, events) →
    compact v = some compactState → Represents compactState full
  headCovered : ∀ {r v}, semantic.head r = some v → ∃ c, compact v = some c

def replace (P : Physical) (v : Version) (c : Compact) :
    Version → Option Compact :=
  fun w => if w = v then some c else P.compact w

inductive PhysicalStep (V : VirtualMergeBaseResolver D) :
    Physical → Option (Label D) → Physical → Prop where
  | collectLog {P P' : Physical} {v : Version} {full : Finset Event}
      (cut : StableCut full)
      (atVersion : ∃ events, P.semantic.ver v = some (full, events))
      (semantic : P'.semantic = P.semantic)
      (compact : P'.compact = replace P v (collectPrefix cut)) :
      PhysicalStep V P none P'
  | collectTrash {P P' : Physical} {v : Version} {old : Compact}
      (oldAt : P.compact v = some old)
      (stable : old.pending = [])
      (semantic : P'.semantic = P.semantic)
      (compact : P'.compact = replace P v (GC.collectTrash old)) :
      PhysicalStep V P none P'
  | ordinary {P P' : Physical} {label : Label D}
      (step : Step D P.semantic label P'.semantic) :
      PhysicalStep V P (some label) P'
  | virtual {P P' : Physical} {label : Label D}
      (step : StepV D V P.semantic label P'.semantic) :
      PhysicalStep V P (some label) P'

def protocol (V : VirtualMergeBaseResolver D) : StateGCProtocol D V where
  Physical := Physical
  semantic := Physical.semantic
  Valid := fun _ => True
  PhysicalStep := PhysicalStep V
  valid_preserved := by simp
  silent_stutters := by
    intro P P' _ step
    cases step with
    | collectLog _ _ h _ => exact h
    | collectTrash _ _ h _ => exact h
  visible_refines := by
    intro P P' label _ step
    cases step with
    | ordinary h => exact .base h
    | virtual h => exact h

theorem silent_semantic_eq {V : VirtualMergeBaseResolver D} {P P' : Physical}
    (h : PhysicalStep V P none P') : P'.semantic = P.semantic :=
  (protocol V).silent_stutters True.intro h

theorem refines {V : VirtualMergeBaseResolver D} {P P' : Physical} {labels}
    (run : StateGCProtocol.Steps (protocol V) P labels P') :
    StateGCProtocol.SemanticSteps V P.semantic
      (StateGCProtocol.eraseLabels labels) P'.semantic :=
  StateGCProtocol.refines (protocol V) True.intro run

/-- The existing framework theorem now combines asynchronous commit-DAG GC,
TreeMove log collection, trash collection, and visible execution. -/
noncomputable def combinedProtocol (V : VirtualMergeBaseResolver D)
    (author : Sal.MRDTs.GC.Author) (roster : Set Replica) : StateGCProtocol D V :=
  Sal.MRDTs.GC.combinedProtocol (protocol V) author roster

#print axioms undoRedo_refines_canonical
#print axioms collectPrefix_represents
#print axioms fullyStable_collectTrash_query
#print axioms refines

end Sal.MRDTs.Instances.TreeMove.GC
