import Mathlib.Data.List.Basic

/-! Local structural lemmas for the core source correspondence enquiry.
The timestamp/provenance argument must separately justify that a fresh run is
placed before every existing child. These lemmas do not model issuance, sort
children, or prove correspondence of the complete JavaScript document.
-/
namespace Sal.MRDTs.Instances.NotionCoreRGA

inductive Tree where
  | node (id : Nat) (children : List Tree)

def preorder : Tree → List Nat
  | .node id children => id :: children.flatMap preorder

def runTree (first : Nat) : List Nat → Tree
  | [] => .node first []
  | next :: rest => .node first [runTree next rest]

theorem runTree_preorder (first : Nat) (rest : List Nat) :
    preorder (runTree first rest) = first :: rest := by
  induction rest generalizing first with
  | nil => simp [runTree, preorder]
  | cons next rest ih => simp [runTree, preorder, ih]

/-- Once sibling dominance puts a newly issued run first, preorder splices
its whole contiguous run immediately after the origin. -/
theorem first_child_run_splice (origin first : Nat) (rest : List Nat)
    (oldChildren : List Tree) :
    preorder (.node origin (runTree first rest :: oldChildren)) =
      origin :: ((first :: rest) ++ oldChildren.flatMap preorder) := by
  simp [preorder, runTree_preorder]

/-- The same local replacement remains a splice inside any already established
preorder before/after context. This does not derive the context from a tree. -/
theorem context_run_splice (before after : List Nat) (origin first : Nat)
    (rest : List Nat) (oldChildren : List Tree) :
    before ++ preorder (.node origin (runTree first rest :: oldChildren)) ++ after =
      before ++ (origin :: ((first :: rest) ++ oldChildren.flatMap preorder)) ++ after := by
  rw [first_child_run_splice]

/-- PASS+FAIL: a two-character run precedes an old child's whole subtree;
it cannot be explained by appending the run after that subtree. -/
theorem splice_control :
    preorder (.node 0 [runTree 3 [4], .node 1 [.node 2 []]]) = [0, 3, 4, 1, 2] ∧
    preorder (.node 0 [runTree 3 [4], .node 1 [.node 2 []]]) ≠ [0, 1, 2, 3, 4] := by
  simp [preorder, runTree]

#print axioms first_child_run_splice
end Sal.MRDTs.Instances.NotionCoreRGA
