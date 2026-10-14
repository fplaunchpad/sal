import Sal.MRDTs.Instances.FugueMaxImplementation
import Sal.MRDTs.Paper1.HistorySpec

/-! Candidate trusted boundary, not a replacement public contract.
The natural client is a positional list of identities (the current Sal query
observes identities). Generated messages retain stable origins and deletion
identities; numeric positions are interpreted at the issuing view. The gap
machine below is an intermediate nondeterministic specification, with no
coordinates, structural-parent relation or implementation update function. -/
namespace Sal.MRDTs.Paper1.FugueMaxClientCandidate
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open Classical

inductive ClientAction where
  | insert (index id : Nat)
  | delete (index : Nat)
  deriving DecidableEq

def clientStep (view : List Nat) : ClientAction → List Nat
  | .insert index id => view.take index ++ id :: view.drop index
  | .delete index => view.take index ++ view.drop (index + 1)

def clientLegal (view : List Nat) : ClientAction → Prop
  | .insert index id => index ≤ view.length ∧ id ≠ 0 ∧ id ∉ view
  | .delete index => index < view.length

/-- Exact positional preparation, with original API index bounds. The current
Sal carrier exposes insertion identities, so `id` is the event's fresh stamp;
arbitrary application values require a separate payload refinement. -/
def Generates (Γ : Sal.EmbedRGA.OrderedPrefixCode) (s : IssuerState)
    (rep stamp : Nat) (request : ClientAction) (message : MRec) : Prop :=
  match request with
  | .insert index id => index ≤ s.live.length ∧ id = stamp ∧
      message = prepareInsert Γ s rep stamp index
  | .delete index => index < s.live.length ∧
      message = prepareDelete s rep stamp index

inductive MessageIntent where
  | insert (id left : Nat) (right : Option Nat)
  | delete (id : Nat)
  deriving DecidableEq

/-- Structural parent, side and chain are not abstract client parameters. -/
def messageIntent (g : MRec) : MessageIntent := match g.op with
  | .ins _ _ => .insert g.ts g.lo g.ro
  | .del id => .delete id

structure Buffer where
  order : List Nat
  deleted : Finset Nat
  deriving DecidableEq

def initial : Buffer := ⟨[0],∅⟩
def visiblePart (deleted : Finset Nat) (order : List Nat) : List Nat :=
  order.filter (fun id => decide (id ≠ 0 ∧ id ∉ deleted))
def visible (s : Buffer) : List Nat := visiblePart s.deleted s.order

def insertState (s : Buffer) (pre suf : List Nat) (id : Nat) : Buffer :=
  ⟨pre ++ id :: suf,s.deleted⟩
def deleteState (s : Buffer) (id : Nat) : Buffer :=
  ⟨s.order,if id = 0 then s.deleted else insert id s.deleted⟩

def Gap (s : Buffer) (left : Nat) (right : Option Nat) (pre suf : List Nat) : Prop :=
  s.order = pre ++ suf ∧ left ∈ pre ∧ match right with
    | none => True
    | some id => id ∈ suf

def insertTransition (s : Buffer) (id left : Nat) (right : Option Nat) (next : Buffer) : Prop :=
  id ≠ 0 ∧ id ∉ s.order ∧ ∃ pre suf, Gap s left right pre suf ∧
    next = insertState s pre suf id

def machine : HistoryMachine MessageIntent Unit (List Nat) where
  State := Buffer
  initial := initial
  transition s label next := match label with
    | .update (.insert id left right) => insertTransition s id left right next
    | .update (.delete id) => (id = 0 ∨ id ∈ s.order) ∧ next = deleteState s id
    | .query _ answer => next = s ∧ answer = visible s

def spec := machine.toSpec

/- One source-local request selects a structural gap whose visible prefix
has exactly its requested length. Concurrent integration may choose another
permanent split within the same origin bounds; it does not replay this index. -/
/-- Source-local structural adjacency includes tombstones. Global concurrent
integration uses the weaker origin-bounded gap relation above. -/
def AdjacentGap (s : Buffer) (left : Nat) (right : Option Nat)
    (pre suf : List Nat) : Prop := Gap s left right pre suf ∧
  (∃ before, pre = before ++ [left]) ∧ match right with
    | none => suf = []
    | some id => ∃ after, suf = id :: after

def LocalGapIntent (s : Buffer) (index left : Nat) (right : Option Nat)
    (pre suf : List Nat) : Prop := Gap s left right pre suf ∧
      (visiblePart s.deleted pre).length = index

theorem insert_refines_positional {s : Buffer} {index id left : Nat} {right : Option Nat}
    {pre suf : List Nat} (intent : LocalGapIntent s index left right pre suf)
    (nonzero : id ≠ 0) (undeleted : id ∉ s.deleted) :
    visible (insertState s pre suf id) = clientStep (visible s) (.insert index id) := by
  obtain ⟨⟨split,_,_⟩,indexEq⟩ := intent
  have vs : visible s = visiblePart s.deleted pre ++ visiblePart s.deleted suf := by
    simp [visible,split,visiblePart]
  have vn : visible (insertState s pre suf id) =
      visiblePart s.deleted pre ++ id :: visiblePart s.deleted suf := by
    simp [visible,insertState,visiblePart,nonzero,undeleted]
  rw [vn,vs,clientStep,← indexEq]
  simp

theorem adjacent_insert_refines_positional {s : Buffer} {index id left : Nat}
    {right : Option Nat} {pre suf : List Nat}
    (adjacent : AdjacentGap s left right pre suf)
    (position : (visiblePart s.deleted pre).length = index)
    (nonzero : id ≠ 0) (undeleted : id ∉ s.deleted) :
    visible (insertState s pre suf id) = clientStep (visible s) (.insert index id) :=
  insert_refines_positional ⟨adjacent.1,position⟩ nonzero undeleted

/-- Deletion changes only visibility; structural identities survive. -/
theorem delete_preserves_order (s : Buffer) (id : Nat) :
    (deleteState s id).order = s.order := rfl

theorem visible_delete {s : Buffer} {id : Nat} (nonzero : id ≠ 0) :
    visible (deleteState s id) = (visible s).filter (fun x => x != id) := by
  simp only [visible,visiblePart,deleteState,nonzero,if_false,List.filter_filter]
  apply List.filter_congr
  intro x hx
  simp only [Finset.mem_insert,not_or]
  by_cases h0 : x = 0 <;> by_cases hi : x = id <;> simp [h0,hi]

theorem delete_refines_positional {s : Buffer} {pre suf : List Nat} {id : Nat}
    (split : visible s = pre ++ id :: suf) (unique : (visible s).Nodup)
    (nonzero : id ≠ 0) :
    visible (deleteState s id) = clientStep (visible s) (.delete pre.length) := by
  rw [visible_delete nonzero,split]
  have freshPre : id ∉ pre := by
    rw [split] at unique
    exact fun h => (List.nodup_append.mp unique).2.2 id h id (by simp) rfl
  have freshSuf : id ∉ suf := by
    rw [split] at unique
    exact (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).1
  have filterPre : pre.filter (fun x => x != id) = pre := by
    apply List.filter_eq_self.mpr
    intro x hx
    simpa only [bne_iff_ne] using (fun h : x = id => freshPre (h ▸ hx))
  have filterSuf : suf.filter (fun x => x != id) = suf := by
    apply List.filter_eq_self.mpr
    intro x hx
    simpa only [bne_iff_ne] using (fun h : x = id => freshSuf (h ▸ hx))
  simp [List.filter_append,filterPre,filterSuf,clientStep]

/-- Fixed numeric replay cannot account for concurrent identity deletes. -/
theorem literal_position_replay_obstruction :
    clientStep (clientStep [1,2] (.delete 0)) (.delete 0) = [] ∧
    visible (deleteState (deleteState ⟨[0,1,2],∅⟩ 1) 1) = [2] ∧
    clientStep (clientStep [1,2] (.delete 0)) (.delete 0) ≠
      visible (deleteState (deleteState ⟨[0,1,2],∅⟩ 1) 1) := by decide

/-- Hand-derived deleted-parent scenario: permanent identity 1 remains a
right bound, although the visible document is empty. -/
theorem tombstone_gap_control :
    let old : Buffer := ⟨[0,1],{1}⟩
    let next : Buffer := ⟨[0,3,1],{1}⟩
    machine.transition old (.update (.insert 3 0 (some 1))) next ∧
    visible next = [3] ∧ visible next ≠ [] ∧ 1 ∉ visible next := by
  dsimp only
  refine ⟨⟨by decide,by decide,[0],[1],by simp [Gap],rfl⟩,by decide,by decide,by decide⟩

#print axioms insert_refines_positional
#print axioms delete_refines_positional
end Sal.MRDTs.Paper1.FugueMaxClientCandidate
