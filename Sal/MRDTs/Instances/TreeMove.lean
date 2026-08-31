import Sal.MRDTs.Instances.FinsetStore

/-!
# Replicated tree move

This module gives a canonical-replay model of the tree move algorithm from
Kleppmann et al., "A Highly-Available Move Operation for Replicated Trees"
(IEEE TPDS 2022).  The replicated carrier is the finite set of timestamped
move events.  `render` sorts that set by timestamp and replays the ordinary
cycle-rejecting tree move operation.

The paper implements out-of-order delivery with undo/redo.  Keeping canonical
replay as the specification makes the MRDT merge set union and leaves
undo/redo as a separate implementation-refinement problem.
-/

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.TreeMove

open Sal.MRDTs.Foundation
open Classical

abbrev Node := Nat
abbrev Metadata := Nat

def root : Node := 0
def trash : Node := 1

/-- A request moves `child` under `parent` and replaces its edge metadata. -/
structure Move where
  parent : Node
  metadata : Metadata
  child : Node
deriving DecidableEq, Repr

abbrev Event := Op Move

/-- A tree has at most one parent by construction. -/
abbrev Tree := Node → Option (Node × Metadata)

def edge (t : Tree) (child parent : Node) : Prop :=
  ∃ metadata, t child = some (parent, metadata)

def TreeSafe (t : Tree) : Prop :=
  ∀ node, ¬ Relation.TransGen (edge t) node node

def emptyTree : Tree := fun _ => none

def setParent (t : Tree) (child parent : Node) (metadata : Metadata) : Tree :=
  Function.update t child (some (parent, metadata))

/-- Sequential tree semantics.  Reject exactly those moves whose resulting
parent graph would contain a cycle. -/
noncomputable def doMove (t : Tree) (m : Move) : Tree :=
  let candidate := setParent t m.child m.parent m.metadata
  if TreeSafe candidate then candidate else t

theorem emptyTree_safe : TreeSafe emptyTree := by
  intro x h
  obtain ⟨y, _, hy⟩ := Relation.TransGen.tail'_iff.mp h
  simp [edge, emptyTree] at hy

theorem doMove_safe {t : Tree} (ht : TreeSafe t) (m : Move) :
    TreeSafe (doMove t m) := by
  classical
  simp only [doMove]
  split <;> assumption

theorem doMove_accepts {t : Tree} {m : Move}
    (h : TreeSafe (setParent t m.child m.parent m.metadata)) :
    doMove t m = setParent t m.child m.parent m.metadata := by
  simp [doMove, h]

theorem doMove_rejects {t : Tree} {m : Move}
    (h : ¬ TreeSafe (setParent t m.child m.parent m.metadata)) :
    doMove t m = t := by
  simp [doMove, h]

theorem selfMove_unsafe (t : Tree) (node : Node) (metadata : Metadata) :
    ¬ TreeSafe (setParent t node node metadata) := by
  intro h
  apply h node
  apply Relation.TransGen.single
  refine ⟨metadata, ?_⟩
  simp [setParent]

theorem selfMove_rejected (t : Tree) (node : Node) (metadata : Metadata) :
    doMove t ⟨node, metadata, node⟩ = t :=
  doMove_rejects (selfMove_unsafe t node metadata)

noncomputable def replayList (events : List Event) : Tree :=
  events.foldl (fun t e => doMove t e.2.2) emptyTree

theorem replayList_safe (events : List Event) : TreeSafe (replayList events) := by
  induction events using List.reverseRecOn with
  | nil => exact emptyTree_safe
  | append_singleton events e ih =>
      simpa [replayList, List.foldl_append] using doMove_safe ih e.2.2

/-- A total encoding uses the Lamport timestamp and replica first. Payload
fields only make malformed duplicate clock keys deterministic; the generation
contract rules those ties out of certified executions. -/
def eventKey (e : Event) : List Nat :=
  [e.1, e.2.1, e.2.2.parent, e.2.2.metadata, e.2.2.child]

theorem eventKey_injective : Function.Injective eventKey := by
  rintro ⟨ta, ra, ma⟩ ⟨tb, rb, mb⟩ h
  simp only [eventKey, List.cons.injEq, and_true] at h
  rcases h with ⟨rfl, rfl, hparent, hmetadata, hchild⟩
  cases ma
  cases mb
  simp_all

def eventLE (a b : Event) : Prop := eventKey a ≤ eventKey b

instance : DecidableRel eventLE := fun a b => inferInstanceAs (Decidable (eventKey a ≤ eventKey b))
instance : IsTrans Event eventLE := ⟨fun _ _ _ => le_trans⟩
instance : Std.Antisymm eventLE :=
  ⟨fun _ _ hab hba => eventKey_injective (le_antisymm hab hba)⟩
instance : Std.Total eventLE :=
  ⟨fun a b => le_total (eventKey a) (eventKey b)⟩

def orderedEvents (events : Finset Event) : List Event := events.sort eventLE

theorem orderedEvents_toFinset (events : List Event) (hn : events.Nodup)
    (hs : events.Pairwise eventLE) : orderedEvents events.toFinset = events := by
  exact (List.toFinset_sort (r := eventLE) hn).2 hs

theorem eventLE_of_timestamp_lt {a b : Event} (h : a.1 < b.1) : eventLE a b := by
  apply le_of_lt
  exact List.Lex.rel h

def Chronological (events : List Event) : Prop :=
  ∀ pre e post, events = pre ++ e :: post →
    ∀ old ∈ pre, old.1 < e.1

theorem chronological_pairwise {events : List Event} (h : Chronological events) :
    events.Pairwise eventLE := by
  induction events with
  | nil => exact .nil
  | cons first rest ih =>
      rw [List.pairwise_cons]
      constructor
      · intro e he
        obtain ⟨pre, post, hrest⟩ := List.mem_iff_append.mp he
        apply eventLE_of_timestamp_lt
        apply h (first :: pre) e post
        · simp [hrest]
        · simp
      · apply ih
        intro pre e post heq old hold
        exact h (first :: pre) e post (by simp [heq]) old (by simp [hold])

theorem chronological_nodup {events : List Event} (h : Chronological events) :
    events.Nodup := by
  induction events with
  | nil => exact .nil
  | cons first rest ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨pre, post, hrest⟩ := List.mem_iff_append.mp hmem
        have hlt := h (first :: pre) first post (by simp [hrest]) first (by simp)
        exact (Nat.lt_irrefl _ hlt)
      · apply ih
        intro pre e post heq old hold
        exact h (first :: pre) e post (by simp [heq]) old (by simp [hold])

noncomputable def render (events : Finset Event) : Tree :=
  replayList (orderedEvents events)

theorem render_safe (events : Finset Event) : TreeSafe (render events) :=
  replayList_safe _

def underTrash (t : Tree) (node : Node) : Prop :=
  node = trash ∨ Relation.TransGen (edge t) node trash

/-- The distinguished trash node and its descendants are outside the client
observation, as in the TPDS algorithm. -/
noncomputable def visibleTree (t : Tree) : Tree := fun node =>
  if underTrash t node then none else t node

theorem edge_visibleTree {t : Tree} {a b : Node} :
    edge (visibleTree t) a b → edge t a b := by
  rintro ⟨m, h⟩
  unfold visibleTree at h
  split at h
  · contradiction
  · exact ⟨m, h⟩

theorem visibleTree_safe {t : Tree} (h : TreeSafe t) :
    TreeSafe (visibleTree t) := by
  intro node cycle
  apply h node
  exact cycle.lift id (fun _ _ e => edge_visibleTree e)

theorem underTrash_visibleTree {t : Tree} {node : Node} :
    underTrash (visibleTree t) node → underTrash t node := by
  rintro (rfl | path)
  · exact Or.inl rfl
  · exact Or.inr (path.lift id (fun _ _ e => edge_visibleTree e))

theorem visibleTree_idempotent (t : Tree) :
    visibleTree (visibleTree t) = visibleTree t := by
  funext node
  by_cases h : underTrash t node
  · change (if underTrash (visibleTree t) node then none else visibleTree t node) =
      visibleTree t node
    unfold visibleTree
    simp [h]
  · have h' : ¬ underTrash (visibleTree t) node :=
      fun bad => h (underTrash_visibleTree bad)
    change (if underTrash (visibleTree t) node then none else visibleTree t node) =
      visibleTree t node
    rw [if_neg h']

/-- The raw replicated state is a grow-only event set. -/
noncomputable def D : MRDTSig where
  State := Finset Event
  dec_state := inferInstance
  init := ∅
  AppOp := Move
  dec_op := inferInstance
  Query := Unit
  Value := Tree
  update s e := insert e s
  query s _ := visibleTree (render s)
  merge _ a b := a ∪ b

theorem all_comm (a b : Event) : D.toUpdateSig.commutes a b := by
  intro s
  apply Finset.ext
  intro x
  simp [D, or_left_comm]

theorem replayLaws : ReplayLaws D.toUpdateSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b _ _
    constructor
    · intro h
      exact absurd (all_comm a b) h
    · rintro (h | h) <;> exact RcRes.noConfusion h
  · intro a b c _ _
    rintro ⟨h, _⟩
    exact RcRes.noConfusion h
  · intro s a b c π _ _ _ h _
    exact RcRes.noConfusion h

theorem mergeLaws : MergeLaws D := by
  refine ⟨replayLaws, ?_, ?_⟩
  · intro l a b; apply Finset.ext; intro x; simp [D, or_comm]
  · intro s; apply Finset.ext; intro x; simp [D]

theorem commutingPeelLaw : CommutingPeelLaw D := by
  constructor
  · intro a e π₀ π₂ _ _; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]

theorem deltaLaws : DeltaLaws D := by
  constructor
  · intro m x₀ x₁ x₂ c; apply Finset.ext; intro x
    simp [D, or_assoc, or_left_comm, or_comm]
  · intro l m x c y; apply Finset.ext; intro z
    simp [D, or_assoc, or_left_comm, or_comm]

theorem join : Join D :=
  JoinProof.ofArbitraryStateLaws mergeLaws deltaLaws
    (causalDeltaLaw_of_all_comm mergeLaws commutingPeelLaw all_comm)

def knownNode (s : Finset Event) (n : Node) : Prop :=
  n = root ∨ n = trash ∨ ∃ e ∈ s, e.2.2.child = n

def visibleNode (s : Finset Event) (n : Node) : Prop :=
  knownNode s n ∧ ¬ underTrash (render s) n

theorem root_visible_empty : visibleNode (∅ : Finset Event) root := by
  constructor
  · exact Or.inl rfl
  · rintro (h | path)
    · simp [root, trash] at h
    · have hempty : render (∅ : Finset Event) = emptyTree := by
        simp [render, orderedEvents, replayList]
      rw [hempty] at path
      obtain ⟨y, _, hy⟩ := Relation.TransGen.tail'_iff.mp path
      simp [edge, emptyTree] at hy

/-- Issuer obligations that are meaningful before replay: timestamps are
globally fresh, the destination exists, and reserved nodes cannot be moved. -/
def applicable (e : Event) (s : Finset Event) : Prop :=
  (∀ old ∈ s, (old.1, old.2.1) ≠ (e.1, e.2.1)) ∧
  visibleNode s e.2.2.parent ∧
  (¬ knownNode s e.2.2.child ∨ visibleNode s e.2.2.child) ∧
  e.2.2.child ≠ root ∧ e.2.2.child ≠ trash

def generation : Issuance D where
  CanIssue := applicable

def replayAdequacy : ReplayAdequacyCertificate D generation :=
  ReplayAdequacyCertificate.ofJoin generation join

/-- The independent chronological machine applies each move once to its
current tree.  It does not sort or replay its prior operations. -/
noncomputable def spec : SequentialMachine Event where
  State := Tree
  init := emptyTree
  step t e := doMove t e.2.2

theorem spec_run_tree (ops : List Event) :
    spec.run ops = replayList ops := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      rw [SequentialMachine.run_append_single]
      simpa [spec, replayList, List.foldl_append] using
        congrArg (fun t => doMove t e.2.2) ih

theorem applySeq_eq_toFinset (ops : List Event) :
    applySeq D.toUpdateSig D.init ops = ops.toFinset := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      rw [applySeq_append_single]
      simpa [D] using congrArg (fun s : Finset Event => insert e s) ih

def stateRel (s : D.State) (q : Tree) : Prop :=
  render s = q

/-- Abstract legality requires exactly the deterministic event-key order and
no duplicate events. This covers concurrent equal Lamport counters by the
replica and payload tie-breakers already present in `eventKey`. -/
def SequentialLegal (ops : List Event) : Prop :=
  ops.Nodup ∧ ops.Pairwise eventLE

noncomputable def sequentialSpec : SequentialSpec D where
  toSequentialMachine := spec
  Legal := SequentialLegal
  query := fun q _ => visibleTree q

theorem sequentialSound (ops : List Event) (h : SequentialLegal ops) :
    stateRel (applySeq D.toUpdateSig D.init ops) (spec.run ops) := by
  rw [stateRel, applySeq_eq_toFinset, spec_run_tree]
  rw [render, orderedEvents_toFinset ops h.1 h.2]

noncomputable def sequential : SequentialRefinement D spec where
  Honest := SequentialLegal
  Rel := stateRel
  init := by simp [stateRel, D, spec, render, orderedEvents, replayList]
  sound := sequentialSound

theorem lo_false (C : Configuration D) (a b : Event) :
    ¬ Sal.MRDTs.Foundation.lo C.replayContext a b := by
  rintro (⟨_, hnoncomm⟩ | ⟨_, _, hrc, _⟩)
  · exact hnoncomm (all_comm a b)
  · exact RcRes.noConfusion hrc

theorem respects_lo (C : Configuration D) (ops : List Event) :
    respects ops (Sal.MRDTs.Foundation.lo C.replayContext) := by
  induction ops with
  | nil => exact List.Pairwise.nil
  | cons e rest ih =>
      exact List.pairwise_cons.mpr ⟨fun b _ => lo_false C b e, ih⟩

noncomputable def sequentialCorrectness : SequentialCorrectnessCertificate D generation
    (InteractionSpec.raw D)
    sequentialSpec stateRel where
  sound C _ replay := by
    intro v s E hver
    obtain ⟨ops, hperm, _, hfold⟩ := replay v s E hver
    have hstate : ops.toFinset = s := by
      rw [← hfold, applySeq_eq_toFinset]
    let π := orderedEvents s
    have hpermπ : listPermOf π E := by
      refine ⟨Finset.sort_nodup _ _, ?_⟩
      intro e
      simp only [π, orderedEvents, Finset.mem_sort]
      rw [← hstate]
      simpa using hperm.2 e
    have hlegal : SequentialLegal π :=
      ⟨Finset.sort_nodup _ _, Finset.pairwise_sort _ _⟩
    have href : stateRel s (sequentialSpec.run π) := by
      change stateRel s (spec.run π)
      have hs := sequentialSound π hlegal
      have hπstate : applySeq D.toUpdateSig D.init π = s := by
        rw [applySeq_eq_toFinset]
        exact Finset.sort_toFinset s eventLE
      rw [← hπstate]
      exact hs
    refine ⟨π, hpermπ,
      respects_interactionLoOn_raw_of_lo (respects_lo C π),
      hlegal, href, ?_⟩
    intro query
    cases query
    exact congrArg visibleTree href

def safety : SafetyCertificate D (canonicalVirtualMergeBase D) generation where
  Safe := fun s => TreeSafe (render s)
  Observable := fun s => TreeSafe (D.query s ())
  preservationV := by
    intro C _ v s E _
    exact render_safe s
  consequence := by
    intro s h
    exact visibleTree_safe h

noncomputable def verified : VerifiedMRDT D where
  issuance := generation
  interaction := InteractionSpec.raw D
  replayAdequacy := replayAdequacy
  Spec := sequentialSpec
  Rel := stateRel
  sequentialCorrectness := sequentialCorrectness

/-! Small proof-oriented tests for the public issuer guard. -/

def firstMove : Event := (2, 0, ⟨0, 7, 2⟩)

example : applicable firstMove (∅ : Finset Event) := by
  refine ⟨by simp, root_visible_empty, ?_, by decide, by decide⟩
  left
  simp [knownNode, firstMove, root, trash]

example : ¬ applicable (2, 0, ⟨0, 9, 3⟩) ({firstMove} : Finset Event) := by
  simp [applicable, firstMove]

example : ¬ applicable (3, 1, ⟨0, 9, root⟩) ({firstMove} : Finset Event) := by
  simp [applicable]

#print axioms render_safe
#print axioms join
#print axioms verified

end Sal.MRDTs.Instances.TreeMove
