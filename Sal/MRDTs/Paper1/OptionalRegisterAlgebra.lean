import Sal.MRDTs.Instances.OptionalRegister
import Sal.MRDTs.Paper1.EnableWinsFlagAlgebra

namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation Instances.OptionalRegister

@[simp] theorem mergePayload_self (p : Payload) : mergePayload p p p = p := by
  cases p
  simp only [mergePayload,ite_true]
  congr 1
  omega

theorem mergePayload_comm (l a b : Payload) : mergePayload l a b = mergePayload l b a := by
  rcases a with ⟨ta,av⟩; rcases b with ⟨tb,bv⟩
  simp only [mergePayload]
  split_ifs <;> simp_all <;> omega

theorem sourceCell_comm (l a b : Cell) : mergeCell l a b = mergeCell l b a := by
  rcases l with ⟨⟨lc,lf⟩,lp⟩
  rcases a with ⟨⟨ac,af⟩,ap⟩
  rcases b with ⟨⟨bc,bf⟩,bp⟩
  cases af <;> cases bf
  all_goals simp only [mergeCell,Instances.NeemFlag.mergeFlag,Bool.and_true,Bool.and_false,
    Bool.true_and,Bool.false_and,Bool.not_false,Bool.not_true,ite_true,ite_false]
  all_goals (try split_ifs) <;> simp_all [mergePayload_comm] <;> omega

theorem source_comm (l a b : State) : merge l a b = merge l b a := by
  apply State.ext
  · simp [merge,Finset.union_comm]
  · intro r; exact sourceCell_comm _ _ _

/-- Averaging equal timestamps is not associative on arbitrary payloads.
The source branch needs timestamp/payload coherence; replacing it by max
would hide this obligation rather than certify the supplied algorithm. -/
theorem averaging_obstruction :
    mergePayload (0,0) (mergePayload (0,0) (7,0) (7,0)) (7,2) = (7,1) ∧
    mergePayload (0,0) (7,0) (mergePayload (0,0) (7,0) (7,2)) = (7,0) ∧
    mergePayload (0,0) (mergePayload (0,0) (7,0) (7,0)) (7,2) ≠
      mergePayload (0,0) (7,0) (mergePayload (0,0) (7,0) (7,2)) := by decide

/-- Same timestamp and same payload reduce the averaging branch to identity. -/
theorem coherent_tie (l a b : Payload) (same : a = b) : mergePayload l a b = a := by
  subst b
  rcases a with ⟨ta,av⟩
  simp only [mergePayload,ite_true]
  congr 1
  omega

/-- Reachable cells are ordered by Set count, with a reset dominating its
observed count. Payloads do not participate in this logical flag order. -/
abbrev CellKey := Lex (Int × Lex (Bool × Lex Payload))

def cellKey (c : Cell) : CellKey := toLex (c.1.1,toLex (!c.1.2,toLex c.2))
def keyCell (k : CellKey) : Cell :=
  (((ofLex k).1,!(ofLex (ofLex k).2).1),(ofLex (ofLex (ofLex k).2).2))

@[simp] theorem keyCell_cellKey (c : Cell) : keyCell (cellKey c) = c := by
  rcases c with ⟨⟨count,flag⟩,payload⟩
  cases flag <;> rfl
@[simp] theorem cellKey_keyCell (k : CellKey) : cellKey (keyCell k) = k := by
  rcases k with ⟨count,flag,payload⟩
  cases flag <;> rfl

def joinCell (a b : Cell) : Cell := keyCell (max (cellKey a) (cellKey b))

theorem joinCell_comm (a b : Cell) : joinCell a b = joinCell b a := by
  simp [joinCell,max_comm]
theorem joinCell_assoc (a b c : Cell) :
    joinCell (joinCell a b) c = joinCell a (joinCell b c) := by
  simp [joinCell,max_assoc]
@[simp] theorem joinCell_idem (a : Cell) : joinCell a a = a := by simp [joinCell]

/-- Explicit payload coherence needed to identify the source merge with the
comparison join. Strict count growth means the active Set timestamp grows;
equal active counts identify the same source Set and payload. -/
def CoherentCells (a b : Cell) : Prop :=
  (a.1.2 = true → b.1.2 = true →
    (a.1.1 < b.1.1 → a.2.1 < b.2.1) ∧
    (b.1.1 < a.1.1 → b.2.1 < a.2.1) ∧
    (a.1.1 = b.1.1 → a.2 = b.2)) ∧
  (a.1.2 = false → a.2 = (0,0)) ∧ (b.1.2 = false → b.2 = (0,0))

private theorem joinCell_of_lt (a b : Cell) (lt : a.1.1 < b.1.1) : joinCell a b = b := by
  have keylt : cellKey a < cellKey b := Prod.Lex.toLex_lt_toLex.mpr (Or.inl lt)
  simp [joinCell,max_eq_right (le_of_lt keylt)]

private theorem joinCell_reset_tie (a b : Cell) (same : a.1.1 = b.1.1)
    (af : a.1.2 = true) (bf : b.1.2 = false) : joinCell a b = b := by
  have keylt : cellKey a < cellKey b := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    right; refine ⟨same,?_⟩
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    simp [af,bf]
  simp [joinCell,max_eq_right (le_of_lt keylt)]

/-- Source averaging is retained. The comparison join is valid only under
these explicit count-prefix, timestamp-growth, and zero-inactive facts. -/
theorem sourceCell_as_join (l a b : Cell) (count : l.1.1 = min a.1.1 b.1.1)
    (coherent : CoherentCells a b) : mergeCell l a b = joinCell a b := by
  rcases coherent with ⟨payload,az,bz⟩
  rcases lt_trichotomy a.1.1 b.1.1 with lt | same | lt
  · rw [joinCell_of_lt a b lt]
    have lc : l.1.1 = a.1.1 := by omega
    rcases a with ⟨⟨ac,af⟩,⟨ta,av⟩⟩
    rcases b with ⟨⟨bc,bf⟩,⟨tb,bv⟩⟩
    cases af <;> cases bf
    all_goals simp only [Prod.fst,Prod.snd] at *
    all_goals simp only [mergeCell,Instances.NeemFlag.mergeFlag]
    all_goals simp_all [mergePayload] <;> (try omega)
    have ts := payload.1
    simp [lt,lc,ne_of_lt ts,not_lt_of_ge (le_of_lt ts)]
  · rcases a with ⟨⟨ac,af⟩,ap⟩
    rcases b with ⟨⟨bc,bf⟩,bp⟩
    simp only [Prod.fst,Prod.snd] at *
    subst bc
    have lc : l.1.1 = ac := by omega
    cases af <;> cases bf
    · have apz := az rfl; have bpz := bz rfl
      subst ap; subst bp
      simp [mergeCell,Instances.NeemFlag.mergeFlag,lc,joinCell]
    · rw [joinCell_comm,joinCell_reset_tie ((ac,true),bp) ((ac,false),ap) rfl rfl rfl]
      have apz := az rfl; subst ap
      simp [mergeCell,Instances.NeemFlag.mergeFlag,lc]
    · rw [joinCell_reset_tie ((ac,true),ap) ((ac,false),bp) rfl rfl rfl]
      have bpz := bz rfl; subst bp
      simp [mergeCell,Instances.NeemFlag.mergeFlag,lc]
    · have eq := (payload rfl rfl).2.2 rfl
      subst bp
      simp [mergeCell,Instances.NeemFlag.mergeFlag,lc,joinCell,mergePayload]
      rcases ap with ⟨ta,av⟩
      simp [keyCell,cellKey]
      omega
  · rw [sourceCell_comm,joinCell_comm]
    apply sourceCell_as_join l b a
    · simpa [min_comm] using count
    · exact ⟨fun hb ha => ⟨(payload ha hb).2.1,(payload ha hb).1,
        fun eq => ((payload ha hb).2.2 eq.symm).symm⟩,bz,az⟩
termination_by if a.1.1 < b.1.1 then 0 else 1
decreasing_by simp only [lt,if_pos]; split_ifs <;> omega

#print axioms source_comm
#print axioms joinCell_assoc
#print axioms averaging_obstruction
end Sal.MRDTs.Paper1.OptionalRegister
