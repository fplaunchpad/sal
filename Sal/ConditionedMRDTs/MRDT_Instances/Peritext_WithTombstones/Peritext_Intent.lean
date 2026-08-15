import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_WithTombstones.Peritext
import Sal.ConditionedMRDTs.Metatheory.UnifiedVerifiedMRDT

/-! # Tombstoned Peritext: guarded intent certificate -/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

set_option maxHeartbeats 1000000

structure PtSeqState where
  chars : Finset PtChar
  tombs : Finset (ℕ × ℕ)
  marks : Finset PtAnchor

private def ptInsertAfter (anchor value : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => if anchor = (0, 0) then [value] else []
  | x :: xs =>
      if anchor = (0, 0) then value :: x :: xs
      else if x = anchor then x :: value :: xs
      else x :: ptInsertAfter anchor value xs

/-- Deterministic visible character identifiers.  Character records are
ordered by their globally unique `(timestamp, replica)` id, inserted at their
declared anchor, then tombstones are filtered. -/
noncomputable def ptCharacterIds (q : PtSeqState) : List (ℕ × ℕ) :=
  let ordered := q.chars.toList.mergeSort (fun a b => a.1 ≤ b.1)
  let inserted := ordered.foldl (fun xs c => ptInsertAfter c.2.1 c.1 xs) []
  inserted.filter (fun id => id ∉ q.tombs)

/-- Mark events attached to the visible rich-text state.  The Boolean in each
record distinguishes add from remove; interpretation can select the latest
event for a matching range/type. -/
noncomputable def ptMarkEvents (q : PtSeqState) : List PtAnchor :=
  q.marks.toList.mergeSort (fun a b => a.2.2.1 ≤ b.2.2.1)

noncomputable def ptSequentialSpec : SequentialSpec (Op PtOp) where
  State := PtSeqState
  init := ⟨∅, ∅, ∅⟩
  step q e := match e.2.2 with
    | .insert ch af => ⟨insert ((e.1, e.2.1), af, ch) q.chars, q.tombs, q.marks⟩
    | .remove id => ⟨q.chars, insert id q.tombs, q.marks⟩
    | .addMark sI sS eI eS mt =>
        ⟨q.chars, q.tombs,
          insert (eI, eS, ((e.1, e.2.1), sI, sS, eI, eS, mt, true)) q.marks⟩
    | .removeMark sI sS eI eS mt =>
        ⟨q.chars, q.tombs,
          insert (eI, eS, ((e.1, e.2.1), sI, sS, eI, eS, mt, false)) q.marks⟩

def ptStateRel (s : PtState) (q : PtSeqState) : Prop :=
  (∀ c, s.1 c = decide (c ∈ q.chars)) ∧
  (∀ id, s.2.1 id = decide (id ∈ q.tombs)) ∧
  (∀ m, s.2.2 m = decide (m ∈ q.marks))

private def ptKnown (s : PtState) (id : ℕ × ℕ) : Prop :=
  ∃ af ch, s.1 (id, af, ch) = true

private def ptFreshOpId (s : PtState) (id : ℕ × ℕ) : Prop :=
  (∀ af ch, s.1 (id, af, ch) = false) ∧
  (∀ finish side start ss ee es mt add,
    s.2.2 (finish, side, (id, start, ss, ee, es, mt, add)) = false)

/-- Generation guard for character and mark operations. -/
def ptApplicable (e : Op PtOp) (s : PtState) : Prop :=
  let id := (e.1, e.2.1)
  match e.2.2 with
  | .insert _ af =>
      (af = (0, 0) ∨ ptKnown s af) ∧ ptFreshOpId s id ∧ s.2.1 id = false
  | .remove target => ptKnown s target ∧ s.2.1 target = false
  | .addMark start _ finish _ _ =>
      ptKnown s start ∧ ptKnown s finish ∧ ptFreshOpId s id
  | .removeMark start ss finish es mt =>
      ptKnown s start ∧ ptKnown s finish ∧ ptFreshOpId s id ∧
      (∃ old endSide,
        s.2.2 (finish, endSide, (old, start, ss, finish, es, mt, true)) = true)

inductive PtHistoryOK : List (Op PtOp) → Prop where
  | nil : PtHistoryOK []
  | snoc {ops e} : PtHistoryOK ops →
      ptApplicable e (applySeq Peritext.toCRDTSig Peritext.init ops) →
      PtHistoryOK (ops ++ [e])

theorem ptSequentialSound (ops : List (Op PtOp)) :
    ptStateRel (applySeq Peritext.toCRDTSig Peritext.init ops)
      (ptSequentialSpec.run ops) := by
  induction ops using List.reverseRecOn with
  | nil =>
      refine ⟨?_, ?_, ?_⟩ <;> intro x <;>
        simp [applySeq, SequentialSpec.run, Peritext, ptSequentialSpec]
  | append_singleton ops e ih =>
      rw [applySeq_append_single, SequentialSpec.run_append_single]
      rcases e with ⟨ts, replica, op⟩
      cases op with
      | insert ch af =>
          refine ⟨?_, ?_, ?_⟩
          · intro c
            change ((applySeq Peritext.toCRDTSig Peritext.init ops).1 c ||
              decide (c = ((ts, replica), af, ch))) = _
            rw [ih.1 c]
            simp [ptSequentialSpec, Bool.or_comm]
          · exact ih.2.1
          · exact ih.2.2
      | remove id =>
          refine ⟨ih.1, ?_, ih.2.2⟩
          intro x
          change ((applySeq Peritext.toCRDTSig Peritext.init ops).2.1 x ||
            decide (x = id)) = _
          rw [ih.2.1 x]
          simp [ptSequentialSpec, eq_comm, Bool.or_comm]
      | addMark sI sS eI eS mt =>
          refine ⟨ih.1, ih.2.1, ?_⟩
          intro m
          change ((applySeq Peritext.toCRDTSig Peritext.init ops).2.2 m ||
            decide (m = (eI, eS, ((ts, replica), sI, sS, eI, eS, mt, true)))) = _
          rw [ih.2.2 m]
          simp [ptSequentialSpec, Bool.or_comm]
      | removeMark sI sS eI eS mt =>
          refine ⟨ih.1, ih.2.1, ?_⟩
          intro m
          change ((applySeq Peritext.toCRDTSig Peritext.init ops).2.2 m ||
            decide (m = (eI, eS, ((ts, replica), sI, sS, eI, eS, mt, false)))) = _
          rw [ih.2.2 m]
          simp [ptSequentialSpec, Bool.or_comm]

def ptHistorySequentialRefinement :
    HistorySequentialRefinement Peritext ptSequentialSpec where
  Honest := PtHistoryOK
  Rel := ptStateRel
  init := by
    refine ⟨?_, ?_, ?_⟩ <;> intro x <;> simp [Peritext, ptSequentialSpec]
  sound := fun ops _ => ptSequentialSound ops

def ptGeneration : GenerationContract Peritext where
  Guard := ptApplicable
  History := fun C => MintHonest Peritext ptApplicable (Configuration.core C)
  history_of_mint := fun _ h => h

private theorem ptJoin : JoinLemma3 Peritext :=
  join_lemma3_of_cd_feasible Peritext_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta Peritext_coreVCs3 Peritext_deltaVCs3)
    (cdVC3_of_all_comm Peritext_coreVCs3 Peritext_all_comm)

noncomputable def ptVerified : VerifiedMRDT Peritext where
  Honest := fun _ => True
  initInv := trivial
  join := fun C _ => (joinKitAt_plain_iff Peritext C).2 (ptJoin C)
  Spec := ptSequentialSpec
  seq := ptHistorySequentialRefinement

noncomputable def ptUnified : UnifiedVerifiedMRDT Peritext where
  verified := ptVerified
  generation := ptGeneration
  history_entails_honest := fun _ _ => True.intro
  safety := SafetyCertificate.trivial ptGeneration

def ptPassInsert : Op PtOp := (1, 1, .insert 65 (0, 0))
example : ptApplicable ptPassInsert Peritext.init := by
  simp [ptApplicable, ptPassInsert, ptFreshOpId, Peritext]
example : ptCharacterIds ⟨{(((1, 1), (0, 0), 65) : PtChar)}, ∅, ∅⟩ = [(1, 1)] := by
  simp [ptCharacterIds, ptInsertAfter]
example : ¬ ptApplicable (1, 1, .remove (9, 9)) Peritext.init := by
  simp [ptApplicable, ptKnown, Peritext]
example : ¬ ptApplicable (1, 1, .insert 65 (9, 9)) Peritext.init := by
  simp [ptApplicable, ptKnown, Peritext]

#print axioms ptSequentialSound
#print axioms ptHistorySequentialRefinement
#print axioms ptUnified

end Sal.ConditionedMRDTs
