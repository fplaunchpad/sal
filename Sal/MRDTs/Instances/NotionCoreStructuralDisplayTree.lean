import Sal.MRDTs.Instances.NotionCoreStructuralDisplay
import Sal.MRDTs.Instances.NotionCoreParentCoupling

/-! Descending-child display traversal alternative. Directed controls and the
one-step parent-table bridge below are checked. The full honest-archive
traversal/fold induction is not yet proved; displayFacts remains the proved
facts-only query. -/
namespace Sal.MRDTs.Instances.NotionCoreStructuralDisplayTree
open NotionCoreStructuralDisplay (Link creatorKey creation displayLinks)
open NotionCorePayload (BlockKey)
open NotionCoreOriginTree (Item Origin Forest)
open NotionCoreParentMap (Table ParentEdges Unique runRows)
open NotionCoreParentCoupling (OrderedForest)

def linkOrigin (link : Link) : Origin := match link.2 with
  | none => .start
  | some block => .item (creatorKey (block,none))
def row (link : Link) : NotionCoreParentMap.Row :=
  ⟨⟨creatorKey link,.text (NotionCoreMachine.blockName link.1) false⟩,linkOrigin link⟩
def name (item : Item) : Nat := match item.kind with
  | .text n _ => n
  | .split => 0

def displayFromLinks (links : List Link) : List Nat :=
  let rows := links.map row
  (NotionCoreMachine.traversal rows.length rows .start).map name
noncomputable def displayTree (facts : Finset NotionCoreStructuralFacts.Fact) : List Nat :=
  displayFromLinks (NotionCoreStructuralDisplay.orderedLinks facts)

/-- Successful origin-tree insertion and direct parent-table traversal have
one identical identity splice. The hypotheses are structural edge coupling,
unique keys, sibling order, freshness and dominance; no traversal or desired
result equation is assumed. Origin presence derives insertion success. -/
theorem fresh_graph_splice (rows : Table) (forest : Forest) (origin : Origin) (fresh : Item)
    (coupled : ParentEdges rows forest) (unique : Unique rows) (ordered : OrderedForest forest)
    (apart : fresh.id ∉ rows.map (fun r => r.item.id))
    (ready : NotionCoreOriginTree.Ready origin (NotionCoreOriginTree.runTree fresh []) forest)
    (present : NotionCorePhysicalReplay.Present origin forest) :
    ∃ next, NotionCoreOriginTree.insert origin (NotionCoreOriginTree.runTree fresh []) forest = some next ∧
      (NotionCoreOriginTree.linearInsert origin [fresh]
        (NotionCoreParentMap.traverse rows.length rows .start)).map (List.map name) =
      some ((NotionCoreParentMap.traverse (rows ++ runRows origin [fresh]).length
        (rows ++ runRows origin [fresh]) .start).map name) := by
  have projected := NotionCoreOriginTree.insert_preorder origin (NotionCoreOriginTree.runTree fresh []) forest ready
  have existsResult : ∃ items, NotionCoreOriginTree.linearInsert origin [fresh]
      (NotionCoreOriginTree.preorder forest) = some items := by
    cases origin with
    | start => exact ⟨_,rfl⟩
    | item id => exact ⟨_,NotionCoreOriginTree.spliceAfter_indices id [fresh] _ present⟩
  obtain ⟨items,linear⟩ := existsResult
  simp only [NotionCoreOriginTree.runTree_preorder] at projected
  rw [linear] at projected
  obtain ⟨next,inserted,preorder⟩ := Option.map_eq_some_iff.mp projected
  have newUnique : ([fresh].map Item.id).Nodup := by simp
  have disjoint : List.Disjoint (rows.map (fun r => r.item.id)) ([fresh].map Item.id) := by
    simpa using apart
  have traversed := (NotionCoreParentCoupling.appended_run_traversal rows forest next origin fresh []
    coupled unique ordered newUnique disjoint ready inserted).2
  refine ⟨next,inserted,?_⟩
  rw [NotionCoreParentCoupling.edges_traversal rows forest coupled unique ordered,linear,traversed,preorder]
  rfl

/-- The precise remaining generic algorithm-alignment lemma. This is a
research target expressed as a proposition, not an asserted theorem. Strict
creator-key order supplies freshness/dominance; predecessor closure supplies
successful insertion. Its proof must assemble the coupled ordered forest and
transport source-ID splices to block-name splices. -/
def TraversalFoldLaw : Prop :=
  ∀ links : List Link,
    links.Pairwise (fun a b => NotionRunAllocation.Before (creatorKey a) (creatorKey b)) →
    (∀ pre link suffix, links = pre ++ link :: suffix →
      ∀ block, link.2 = some block → ∃ old ∈ pre, old.1 = block) →
    displayFromLinks links = displayLinks [] links

namespace SPOT
private def seed : Link := (.initial,none)
private def left : Link := (.issued ⟨3,[66]⟩,some .initial)
private def right : Link := (.issued ⟨3,[67]⟩,some .initial)
private def child : Link := (.issued ⟨4,[66]⟩,some left.1)
private def before : Link := (.issued ⟨1,[64]⟩,none)
theorem descendants_control :
    displayFromLinks [seed,left,right,child] =
      [0,NotionCoreMachine.blockName right.1,NotionCoreMachine.blockName left.1,NotionCoreMachine.blockName child.1] ∧
    displayFromLinks [seed,left,right,child] ≠
      [0,NotionCoreMachine.blockName right.1,NotionCoreMachine.blockName child.1,NotionCoreMachine.blockName left.1] := by decide +kernel

theorem prebootstrap_control :
    displayFromLinks [before,seed] = [0,NotionCoreMachine.blockName before.1] ∧
    displayFromLinks [before,seed] ≠ [NotionCoreMachine.blockName before.1,0] := by decide +kernel

/-- A bounded graph/fold comparison for generated closed creator graphs. It
is computation evidence, not the unproved generic traversal/fold theorem. -/
def generated (choices : List Nat) : List Link :=
  choices.foldl (fun links choice =>
    let key : BlockKey := .issued ⟨links.length + 1,[66]⟩
    let after := if choice % (links.length + 1) = links.length then none
      else (links[choice % links.length]?).map Prod.fst
    links ++ [(key,after)]) [seed]
def words : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun rest => [0,1,2,3].map (· :: rest)
def boundedOracle : Bool := (words 4).all fun choices =>
  let links := generated choices
  displayFromLinks links == displayLinks [] links
#eval boundedOracle
end SPOT

#print axioms fresh_graph_splice
#print axioms SPOT.descendants_control
#print axioms SPOT.prebootstrap_control
end Sal.MRDTs.Instances.NotionCoreStructuralDisplayTree
