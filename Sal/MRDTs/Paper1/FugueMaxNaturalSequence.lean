import Sal.MRDTs.Paper1.FugueMaxClientCandidate

/-! Deterministic identity-list candidate for the natural sequence contract.
The abstract state remembers only permanent identity order and deletion marks.
Positions are interpreted once, at issuance; replay uses stable identities.
No global RA refinement is asserted in this module. -/
namespace Sal.MRDTs.Paper1.FugueMaxNaturalSequence
open FugueMaxClientCandidate
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax

abbrev Buffer := FugueMaxClientCandidate.Buffer

inductive Action where
  | insertAfter (id left : Nat)
  | deleteID (id : Nat)
  deriving DecidableEq

def insertAfter (order : List Nat) (id left : Nat) : List Nat :=
  match order with
  | [] => []
  | head :: tail => if head = left then head :: id :: tail
      else head :: insertAfter tail id left

def step (s : Buffer) : Action → Buffer
  | .insertAfter id left => ⟨insertAfter s.order id left,s.deleted⟩
  | .deleteID id => deleteState s id

def legal (s : Buffer) : Action → Prop
  | .insertAfter id left => id ≠ 0 ∧ id ∉ s.order ∧ left ∈ s.order
  | .deleteID id => id ∈ s.order

def natural : DeterministicSpec Action Unit (List Nat) where
  State := Buffer
  initial := FugueMaxClientCandidate.initial
  update := step
  query s _ := visible s

def machine : HistoryMachine Action Unit (List Nat) where
  State := Buffer
  initial := FugueMaxClientCandidate.initial
  transition s label next := match label with
    | .update action => legal s action ∧ next = step s action
    | .query _ answer => next = s ∧ answer = visible s

def spec := machine.toSpec

def ofMessage (g : MRec) : Action := match g.op with
  | .ins _ _ => .insertAfter g.ts g.lo
  | .del id => .deleteID id

/-- The exact unchanged issuer translates a source index to its visible left
identity. The structural parent and right origin are absent from this action. -/
theorem generated_insert_intent (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    (s : IssuerState) (rep stamp index : Nat) :
    ofMessage (prepareInsert Γ s rep stamp index) =
      .insertAfter stamp
        (if index = 0 then 0 else (Instances.SidedEmbedRGA.sIds s.live).getD (index - 1) 0) := by
  unfold prepareInsert Instances.SidedEmbedRGA.mGenInsAfter
  split <;> rfl

theorem generated_delete_intent (s : IssuerState) (rep stamp index : Nat) :
    ofMessage (prepareDelete s rep stamp index) =
      .deleteID ((Instances.SidedEmbedRGA.sIds s.live).getD index 0) := rfl

theorem generates_insert_action {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {s : IssuerState} {rep stamp index id : Nat} {message : MRec}
    (generated : Generates Γ s rep stamp (.insert index id) message) :
    ofMessage message = .insertAfter id
      (if index = 0 then 0 else (sIds s.live).getD (index - 1) 0) := by
  obtain ⟨_,same,exactMessage⟩ := generated
  rw [exactMessage,generated_insert_intent,same]

theorem generates_delete_action {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {s : IssuerState} {rep stamp index : Nat} {message : MRec}
    (generated : Generates Γ s rep stamp (.delete index) message) :
    ofMessage message = .deleteID ((sIds s.live).getD index 0) := by
  rw [generated.2,generated_delete_intent]

theorem insertAfter_split (pre suf : List Nat) (id left : Nat)
    (absent : left ∉ pre) :
    insertAfter (pre ++ left :: suf) id left = pre ++ left :: id :: suf := by
  induction pre with
  | nil => simp [insertAfter]
  | cons head tail ih =>
    have different : head ≠ left := fun h => absent (by simp [h])
    have rest : left ∉ tail := fun h => absent (by simp [h])
    simpa [insertAfter,different] using congrArg (List.cons head) (ih rest)

/-- The local permanent-list split is sufficient for positional insertion.
Deleted identities before the left origin do not contribute to the index. -/
theorem insert_refines_positional {s : Buffer} {pre suf : List Nat}
    {id left index : Nat}
    (split : s.order = pre ++ left :: suf) (first : left ∉ pre)
    (indexEq : (visiblePart s.deleted (pre ++ [left])).length = index)
    (nonzero : id ≠ 0) (undeleted : id ∉ s.deleted) :
    visible (step s (.insertAfter id left)) =
      clientStep (visible s) (.insert index id) := by
  have placement : step s (.insertAfter id left) =
      insertState s (pre ++ [left]) suf id := by
    simp [step,split,insertAfter_split pre suf id left first,insertState]
  rw [placement]
  apply FugueMaxClientCandidate.insert_refines_positional
    (left := left) (right := none) (pre := pre ++ [left]) (suf := suf)
  · exact ⟨⟨by simpa using split, by simp, trivial⟩,indexEq⟩
  · exact nonzero
  · exact undeleted

theorem delete_refines_positional {s : Buffer} {pre suf : List Nat} {id : Nat}
    (split : visible s = pre ++ id :: suf) (unique : (visible s).Nodup)
    (nonzero : id ≠ 0) :
    visible (step s (.deleteID id)) =
      clientStep (visible s) (.delete pre.length) :=
  FugueMaxClientCandidate.delete_refines_positional split unique nonzero

/-- A prepared positional request and a matching source-local abstract view
have the same visible effect. The source representation obligations are
explicit: this is a local refinement, not a global history theorem. -/
theorem generated_insert_refines {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {issuer : IssuerState} {rep stamp index id : Nat} {message : MRec}
    {s : Buffer} {pre suf : List Nat}
    (generated : Generates Γ issuer rep stamp (.insert index id) message)
    (view : visible s = sIds issuer.live)
    (split : s.order = pre ++
      (if index = 0 then 0 else (sIds issuer.live).getD (index - 1) 0) :: suf)
    (first : (if index = 0 then 0 else
      (sIds issuer.live).getD (index - 1) 0) ∉ pre)
    (position : (visiblePart s.deleted (pre ++
      [if index = 0 then 0 else (sIds issuer.live).getD (index - 1) 0])).length = index)
    (nonzero : id ≠ 0) (undeleted : id ∉ s.deleted) :
    visible (step s (ofMessage message)) =
      clientStep (sIds issuer.live) (.insert index id) := by
  rw [generates_insert_action generated]
  exact (insert_refines_positional split first position nonzero undeleted).trans
    (congrArg (fun v => clientStep v (.insert index id)) view)

/-- For a wellformed permanent buffer, the issuer's positional predecessor
determines the source split; callers need not provide that split. -/
theorem positional_anchor_refines {s : Buffer} {tail : List Nat} {index id : Nat}
    (root : s.order = 0 :: tail) (unique : s.order.Nodup)
    (bound : index ≤ (visible s).length)
    (nonzero : id ≠ 0) (undeleted : id ∉ s.deleted) :
    visible (step s (.insertAfter id
      (if index = 0 then 0 else (visible s).getD (index - 1) 0))) =
      clientStep (visible s) (.insert index id) := by
  cases index with
  | zero =>
    apply insert_refines_positional (pre := []) (suf := tail) root (by simp)
    · simp [visiblePart]
    · exact nonzero
    · exact undeleted

  | succ index =>
    have positionBound : index < (visible s).length := by omega
    let left := (visible s)[index]
    have anchorEq : (visible s).getD index 0 = left := List.getD_eq_getElem _ _ positionBound
    have visibleMember : left ∈ visible s := List.getElem_mem positionBound
    have properties : left ∈ s.order ∧ left ≠ 0 ∧ left ∉ s.deleted := by
      simpa [visible,visiblePart] using visibleMember
    obtain ⟨pre,suf,split⟩ := List.append_of_mem properties.1
    have first : left ∉ pre := by
      have nd := unique
      rw [split] at nd
      exact fun member => (List.nodup_append.mp nd).2.2 left member left (by simp) rfl
    have firstVisible : left ∉ visiblePart s.deleted pre := by
      intro member
      exact first (List.mem_of_mem_filter member)
    have viewSplit : visible s = visiblePart s.deleted pre ++ left :: visiblePart s.deleted suf := by
      simp [visible,visiblePart,split,properties.2.1,properties.2.2]
    have ndView : (visible s).Nodup := List.Nodup.filter _ unique
    have indexEq : (visible s).idxOf left = index := ndView.idxOf_getElem index positionBound
    rw [viewSplit,List.idxOf_append,if_neg firstVisible] at indexEq
    simp only [List.idxOf_cons_self,Nat.zero_add] at indexEq
    simp only [Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,anchorEq]
    apply insert_refines_positional split first
    · simpa [visiblePart,properties.2.1,properties.2.2] using congrArg Nat.succ indexEq
    · exact nonzero
    · exact undeleted

theorem generated_insert_refines_source {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {issuer : IssuerState} {rep stamp index id : Nat} {message : MRec}
    {s : Buffer} {tail : List Nat}
    (generated : Generates Γ issuer rep stamp (.insert index id) message)
    (view : visible s = sIds issuer.live)
    (root : s.order = 0 :: tail) (unique : s.order.Nodup)
    (nonzero : id ≠ 0) (undeleted : id ∉ s.deleted) :
    visible (step s (ofMessage message)) =
      clientStep (sIds issuer.live) (.insert index id) := by
  rw [generates_insert_action generated,← view]
  apply positional_anchor_refines root unique
  · have lengths : (sIds issuer.live).length = issuer.live.length := by simp [sIds]
    rw [view,lengths]
    exact generated.1
  · exact nonzero
  · exact undeleted

theorem positional_delete_refines {s : Buffer} {index : Nat}
    (unique : s.order.Nodup) (bound : index < (visible s).length) :
    visible (step s (.deleteID ((visible s).getD index 0))) =
      clientStep (visible s) (.delete index) := by
  have anchorEq := List.getD_eq_getElem (visible s) 0 bound
  have member : (visible s)[index] ∈ visible s := List.getElem_mem bound
  have nonzero : (visible s)[index] ≠ 0 := by
    have properties := (List.mem_filter.mp member).2
    exact (of_decide_eq_true properties).1
  have split : visible s = (visible s).take index ++
      (visible s)[index] :: (visible s).drop (index + 1) := by
    rw [List.getElem_cons_drop bound,List.take_append_drop]
  have proof := delete_refines_positional split (List.Nodup.filter _ unique) nonzero
  rw [anchorEq]
  simpa only [List.length_take,Nat.min_eq_left (Nat.le_of_lt bound)] using proof

theorem generated_delete_refines_source {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {issuer : IssuerState} {rep stamp index : Nat} {message : MRec}
    {s : Buffer}
    (generated : Generates Γ issuer rep stamp (.delete index) message)
    (view : visible s = sIds issuer.live) (unique : s.order.Nodup) :
    visible (step s (ofMessage message)) =
      clientStep (sIds issuer.live) (.delete index) := by
  rw [generates_delete_action generated,← view]
  apply positional_delete_refines unique
  have lengths : (sIds issuer.live).length = issuer.live.length := by simp [sIds]
  rw [view,lengths]
  exact generated.1

#print axioms insert_refines_positional
#print axioms delete_refines_positional
#print axioms generated_insert_refines_source
#print axioms generated_delete_refines_source
end Sal.MRDTs.Paper1.FugueMaxNaturalSequence
