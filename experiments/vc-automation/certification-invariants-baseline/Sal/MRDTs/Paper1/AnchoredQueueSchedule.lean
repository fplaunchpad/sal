import Sal.MRDTs.Paper1.AnchoredQueueHistory
import Sal.MRDTs.Paper1.AnchoredQueueReadSide

/-! Delete-first independent FIFO scheduling. Each identity's birth is placed
 immediately before its first deletion; duplicate deletions are replayed on an
 absent identity. The abstract queue is empty between these blocks. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.History
open Foundation Instances.EmbedRGA

structure BirthDelete where
  birth : Event
  deletion : Event
  insertion : eIsIns birth = true
  target : deletion.op = .del birth.time

theorem fifoFold_append (pre suf : List Event) :
    fifoFold (pre ++ suf) = suf.foldl fifoStep (fifoFold pre) := by
  simp [fifoFold, List.foldl_append]

/-- The prefix argument tracks abstract birth freshness, never live state. -/
def deadWord (pre : List Event) : List BirthDelete → List Event
  | [] => []
  | p :: ps =>
    if p.birth.time ∈ eInsIds pre then
      p.deletion :: deadWord (pre ++ [p.deletion]) ps
    else
      p.birth :: p.deletion :: deadWord (pre ++ [p.birth,p.deletion]) ps

theorem next_birth {pre : List Event} {birth : Event}
    (insertion : eIsIns birth = true)
    (fresh : birth.time ∉ eInsIds pre) : NextLegal pre birth := by
  rcases birth with ⟨ts,rep,op⟩
  cases op with
  | del target => simp [eIsIns] at insertion
  | ins value coordinate anchor =>
    refine ⟨?_,fun _ => fresh,?_⟩
    · exact fifo_fresh_of_birth_fresh fresh
    · intro target impossible
      cases impossible

theorem next_delete_empty {pre : List Event} {birth deletion : Event}
    (empty : fifoFold pre = []) (born : birth.time ∈ eInsIds pre)
    (target : deletion.op = .del birth.time) : NextLegal pre deletion := by
  refine ⟨?_,?_,?_⟩
  · simp [fifoApplicable,target,empty]
  · simp [eIsIns,Op.op] at target ⊢
    rw [target]
    simp
  · intro named eq
    have same : named = birth.time := by rw [target] at eq; simpa using eq.symm
    simpa [same] using born

theorem birth_delete_empty (pre : List Event) (p : BirthDelete)
    (empty : fifoFold pre = []) : fifoFold (pre ++ [p.birth,p.deletion]) = [] := by
  rw [fifoFold_append,empty]
  rcases p with ⟨⟨ts,rep,op⟩,deletion,insertion,target⟩
  cases op with
  | del named => simp [eIsIns] at insertion
  | ins value coordinate anchor =>
    simp only [Op.op,Op.time] at target
    simp [fifoStep,Op.op,Op.time,target]

theorem deadWord_checked_empty (pre : List Event) (ps : List BirthDelete)
    (empty : fifoFold pre = []) :
    CheckFrom pre (deadWord pre ps) ∧ fifoFold (pre ++ deadWord pre ps) = [] := by
  induction ps generalizing pre with
  | nil => simpa [deadWord,CheckFrom] using empty
  | cons p ps ih =>
    unfold deadWord
    split
    · rename_i born
      have next := next_delete_empty empty born p.target
      have empty' : fifoFold (pre ++ [p.deletion]) = [] := by
        rw [fifoFold_snoc,empty]
        simp [fifoStep,p.target]
      obtain ⟨checked,last⟩ := ih (pre ++ [p.deletion]) empty'
      exact ⟨⟨next,checked⟩,by simpa [List.append_assoc] using last⟩
    · rename_i fresh
      have next := next_birth p.insertion fresh
      have birthExists : p.birth.time ∈ eInsIds (pre ++ [p.birth]) := by
        rw [eInsIds_append]
        apply List.mem_append_right
        simp [eInsIds,p.insertion,Op.time]
      have legalDelete : NextLegal (pre ++ [p.birth]) p.deletion := by
        refine ⟨?_,?_,?_⟩
        · rcases p with ⟨⟨ts,rep,op⟩,deletion,insertion,target⟩
          cases op with
          | del named => simp [eIsIns] at insertion
          | ins value coordinate anchor =>
            rw [fifoFold_snoc,empty]
            simp only [Op.op,Op.time] at target
            simp [fifoApplicable,fifoStep,Op.op,Op.time,target]
        · have target := p.target
          simp only [Op.op] at target
          simp [eIsIns,target]
        · intro named eq
          have same : named = p.birth.time := by rw [p.target] at eq; simpa using eq.symm
          simpa [same] using birthExists
      obtain ⟨checked,last⟩ := ih (pre ++ [p.birth,p.deletion]) (birth_delete_empty pre p empty)
      refine ⟨⟨next,legalDelete,?_⟩,?_⟩
      · simpa [List.append_assoc] using checked
      · simpa [List.append_assoc] using last

theorem deadWord_legal (ps : List BirthDelete) : fifoLegal (deadWord [] ps) :=
  legal_of_check (deadWord_checked_empty [] ps rfl).1

/-- Appending the surviving births gives an ordinary legal FIFO suffix.
 Freshness is checked against all removed births, not merely the empty live
 queue left by the deletion blocks. -/
theorem survivingBirths_checked (pre births : List Event)
    (insertions : ∀ e ∈ births, eIsIns e = true)
    (distinct : births.Pairwise (fun a b => a.time ≠ b.time))
    (fresh : ∀ e ∈ births, e.time ∉ eInsIds pre) : CheckFrom pre births := by
  induction births generalizing pre with
  | nil => trivial
  | cons first rest ih =>
    obtain ⟨different,distinct⟩ := List.pairwise_cons.mp distinct
    refine ⟨next_birth (insertions first List.mem_cons_self) (fresh first List.mem_cons_self),?_⟩
    apply ih (pre ++ [first])
    · intro e mem
      exact insertions e (List.mem_cons_of_mem first mem)
    · exact distinct
    · intro e mem born
      rw [eInsIds_append] at born
      rcases List.mem_append.mp born with old | current
      · exact fresh e (List.mem_cons_of_mem first mem) old
      · have ids : eInsIds [first] = [first.time] := by
          simp [eInsIds,insertions first List.mem_cons_self,Op.time]
        rw [ids,List.mem_singleton] at current
        exact different e mem current.symm

/-- The scheduling algorithm gives a legal independent FIFO history before
 any representation or visibility theorem is invoked. -/
theorem schedule_legal (ps : List BirthDelete) (live : List Event)
    (insertions : ∀ e ∈ live, eIsIns e = true)
    (distinct : live.Pairwise (fun a b => a.time ≠ b.time))
    (fresh : ∀ e ∈ live, e.time ∉ eInsIds (deadWord [] ps)) :
    fifoLegal (deadWord [] ps ++ live) := by
  apply legal_of_check
  rw [checkFrom_append]
  exact ⟨(deadWord_checked_empty [] ps rfl).1,
    by simpa using survivingBirths_checked (deadWord [] ps) live insertions distinct fresh⟩

/-- A position rank for the emitted birth/deletion blocks. Only first births
 receive a rank here; repeated target births do not occur in the word. -/
def FreshRanks (rank : Event → Nat) (pre : List Event) : List BirthDelete → Prop
  | [] => True
  | p :: ps =>
    if p.birth.time ∈ eInsIds pre then
      FreshRanks rank (pre ++ [p.deletion]) ps
    else
      rank p.birth = 2 * p.deletion.time ∧
      FreshRanks rank (pre ++ [p.birth,p.deletion]) ps

theorem deadWord_append (pre : List Event) (xs ys : List BirthDelete) :
    deadWord pre (xs ++ ys) = deadWord pre xs ++ deadWord (pre ++ deadWord pre xs) ys := by
  induction xs generalizing pre with
  | nil => simp [deadWord]
  | cons p xs ih =>
    simp only [List.cons_append,deadWord]
    by_cases born : p.birth.time ∈ eInsIds pre
    · simp only [if_pos born,List.cons_append]
      rw [ih]
      simp [List.append_assoc]
    · simp only [if_neg born,List.cons_append]
      rw [ih]
      simp [List.append_assoc]

theorem deadWord_birth_coverage (pre : List Event) (ps : List BirthDelete) :
    ∀ p ∈ ps, p.birth.time ∈ eInsIds (pre ++ deadWord pre ps) := by
  induction ps generalizing pre with
  | nil => simp
  | cons first rest ih =>
    intro p mem
    unfold deadWord
    split
    · rename_i born
      rcases List.mem_cons.mp mem with rfl | mem
      · rw [eInsIds_append]
        exact List.mem_append_left _ born
      · simpa [List.append_assoc] using ih (pre ++ [first.deletion]) p mem
    · rename_i fresh
      rcases List.mem_cons.mp mem with rfl | mem
      · apply mem_eInsIds.mpr
        refine ⟨p.birth,?_,p.insertion,rfl⟩
        simp
      · simpa [List.append_assoc] using ih (pre ++ [first.birth,first.deletion]) p mem

theorem freshRanks_iff (rank : Event → Nat) (pre : List Event) (ps : List BirthDelete) :
    FreshRanks rank pre ps ↔
    ∀ before p after, ps = before ++ p :: after →
      p.birth.time ∉ eInsIds (pre ++ deadWord pre before) →
      rank p.birth = 2 * p.deletion.time := by
  induction ps generalizing pre with
  | nil => simp [FreshRanks]
  | cons first ps ih =>
    by_cases born : first.birth.time ∈ eInsIds pre
    · simp only [FreshRanks,if_pos born]
      rw [ih]
      constructor
      · intro all before p after split fresh
        cases before with
        | nil =>
          obtain ⟨rfl,_⟩ := List.cons.inj (by simpa using split)
          exact (fresh (by simpa [deadWord] using born)).elim
        | cons x before =>
          have eq : first = x ∧ ps = before ++ p :: after :=
            List.cons.inj (by simpa only [List.cons_append] using split)
          obtain ⟨rfl,tailEq⟩ := eq
          apply all before p after tailEq
          simpa [deadWord,born,List.append_assoc] using fresh
      · intro all before p after split fresh
        apply all (first :: before) p after (by simp [split])
        simpa [deadWord,born,List.append_assoc] using fresh
    · simp only [FreshRanks,if_neg born]
      rw [ih]
      constructor
      · rintro ⟨firstRank,all⟩ before p after split fresh
        cases before with
        | nil =>
          obtain ⟨rfl,_⟩ := List.cons.inj (by simpa using split)
          exact firstRank
        | cons x before =>
          have eq : first = x ∧ ps = before ++ p :: after :=
            List.cons.inj (by simpa only [List.cons_append] using split)
          obtain ⟨rfl,tailEq⟩ := eq
          apply all before p after tailEq
          simpa [deadWord,born,List.append_assoc] using fresh
      · intro all
        refine ⟨all [] first ps rfl (by simpa [deadWord] using born),?_⟩
        intro before p after split fresh
        apply all (first :: before) p after (by simp [split])
        simpa [deadWord,born,List.append_assoc] using fresh

/-- A first occurrence in the pair list is exactly the rank obligation needed
 by the executable scanner. Prior target births are retained only in the
 independent legality bookkeeping, never in implementation state. -/
theorem freshRanks_of_first_occurrence (rank : Event → Nat) (ps : List BirthDelete)
    (firstRanks : ∀ before p after, ps = before ++ p :: after →
      p.birth.time ∉ before.map (fun q => q.birth.time) →
      rank p.birth = 2 * p.deletion.time) : FreshRanks rank [] ps := by
  apply (freshRanks_iff rank [] ps).mpr
  intro before p after split fresh
  apply firstRanks before p after split
  intro mem
  obtain ⟨q,hq,same⟩ := List.mem_map.mp mem
  apply fresh
  simpa [same] using deadWord_birth_coverage [] before q hq

theorem deadWord_rank_lower (rank : Event → Nat) (pre : List Event)
    (ps : List BirthDelete) (bound : Nat)
    (freshRanks : FreshRanks rank pre ps)
    (deletionRanks : ∀ p ∈ ps, rank p.deletion = 2 * p.deletion.time + 1)
    (lower : ∀ p ∈ ps, bound ≤ 2 * p.deletion.time) :
    ∀ e ∈ deadWord pre ps, bound ≤ rank e := by
  induction ps generalizing pre with
  | nil => simp [deadWord]
  | cons p ps ih =>
    unfold deadWord
    split
    · rename_i born
      have rest : FreshRanks rank (pre ++ [p.deletion]) ps := by
        simpa [FreshRanks,born] using freshRanks
      intro e mem
      rcases List.mem_cons.mp mem with rfl | mem
      · rw [deletionRanks p List.mem_cons_self]
        exact Nat.le_trans (lower p List.mem_cons_self) (Nat.le_add_right _ _)
      · exact ih _ rest
          (fun p hp => deletionRanks p (List.mem_cons_of_mem _ hp))
          (fun p hp => lower p (List.mem_cons_of_mem _ hp)) e mem
    · rename_i fresh
      obtain ⟨rankBirth,rest⟩ : rank p.birth = 2 * p.deletion.time ∧
          FreshRanks rank (pre ++ [p.birth,p.deletion]) ps := by
        simpa [FreshRanks,fresh] using freshRanks
      intro e mem
      rcases List.mem_cons.mp mem with rfl | mem
      · rw [rankBirth]
        exact lower p List.mem_cons_self
      · rcases List.mem_cons.mp mem with rfl | mem
        · rw [deletionRanks p List.mem_cons_self]
          exact Nat.le_trans (lower p List.mem_cons_self) (Nat.le_add_right _ _)
        · exact ih _ rest
            (fun p hp => deletionRanks p (List.mem_cons_of_mem _ hp))
            (fun p hp => lower p (List.mem_cons_of_mem _ hp)) e mem

/-- Chronological deletions yield a word sorted by first-deletion rank. This
 is a syntactic theorem about the scheduling algorithm, separate from the
 issuance argument that specification conflicts increase those ranks. -/
theorem deadWord_rank_sorted (rank : Event → Nat) (pre : List Event)
    (ps : List BirthDelete)
    (freshRanks : FreshRanks rank pre ps)
    (deletionRanks : ∀ p ∈ ps, rank p.deletion = 2 * p.deletion.time + 1)
    (chronological : ps.Pairwise (fun p q => p.deletion.time < q.deletion.time)) :
    (deadWord pre ps).Pairwise (fun a b => rank a < rank b) := by
  induction ps generalizing pre with
  | nil => simp [deadWord]
  | cons p ps ih =>
    obtain ⟨later,chronological⟩ := List.pairwise_cons.mp chronological
    have lower : ∀ q ∈ ps, 2 * p.deletion.time + 2 ≤ 2 * q.deletion.time := by
      intro q hq
      have lt : p.deletion.time < q.deletion.time := later q hq
      exact Nat.mul_le_mul_left 2 lt
    unfold deadWord
    split
    · rename_i born
      have rest : FreshRanks rank (pre ++ [p.deletion]) ps := by
        simpa [FreshRanks,born] using freshRanks
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih _ rest
        (fun p hp => deletionRanks p (List.mem_cons_of_mem _ hp)) chronological⟩
      intro e he
      have bound := deadWord_rank_lower rank (pre ++ [p.deletion]) ps
        (2 * p.deletion.time + 2) rest
        (fun p hp => deletionRanks p (List.mem_cons_of_mem _ hp)) lower e he
      rw [deletionRanks p List.mem_cons_self]
      omega
    · rename_i fresh
      obtain ⟨rankBirth,rest⟩ : rank p.birth = 2 * p.deletion.time ∧
          FreshRanks rank (pre ++ [p.birth,p.deletion]) ps := by
        simpa [FreshRanks,fresh] using freshRanks
      have tail := ih _ rest
        (fun p hp => deletionRanks p (List.mem_cons_of_mem _ hp)) chronological
      have bounds := deadWord_rank_lower rank (pre ++ [p.birth,p.deletion]) ps
        (2 * p.deletion.time + 2) rest
        (fun p hp => deletionRanks p (List.mem_cons_of_mem _ hp)) lower
      apply List.pairwise_cons.mpr
      refine ⟨?_,List.pairwise_cons.mpr ⟨?_,tail⟩⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rw [rankBirth,deletionRanks p List.mem_cons_self]
          omega
        · have bound := bounds e he
          rw [rankBirth]
          omega
      · intro e he
        have bound := bounds e he
        rw [deletionRanks p List.mem_cons_self]
        omega

/-- Rank-increasing edges are respected by the very same generated FIFO word. -/
theorem deadWord_respects (rank : Event → Nat) (pre : List Event)
    (ps : List BirthDelete) (R : Event → Event → Prop)
    (freshRanks : FreshRanks rank pre ps)
    (deletionRanks : ∀ p ∈ ps, rank p.deletion = 2 * p.deletion.time + 1)
    (chronological : ps.Pairwise (fun p q => p.deletion.time < q.deletion.time))
    (increases : ∀ a ∈ deadWord pre ps, ∀ b ∈ deadWord pre ps,
      R a b → rank a < rank b) : respects (deadWord pre ps) R := by
  apply (deadWord_rank_sorted rank pre ps freshRanks deletionRanks chronological).imp_of_mem
  intro a b ha hb ranks backward
  have contradict := increases b hb a ha backward
  omega

def birthTag (e : Event) : Nat × Nat :=
  (e.time,match e.op with | .ins value _ _ => value | .del _ => 0)

theorem survivingBirths_fold (s : List (Nat × Nat)) (live : List Event)
    (insertions : ∀ e ∈ live, eIsIns e = true) :
    live.foldl fifoStep s = s ++ live.map birthTag := by
  induction live generalizing s with
  | nil => simp
  | cons e es ih =>
    have insertion := insertions e List.mem_cons_self
    rcases e with ⟨ts,rep,op⟩
    cases op with
    | del target => simp [eIsIns] at insertion
    | ins value coordinate anchor =>
      simp only [List.foldl_cons,fifoStep,Op.op,Op.time]
      rw [ih (s ++ [(ts,value)]) (fun e he => insertions e (List.mem_cons_of_mem _ he))]
      simp [birthTag,Op.op,Op.time,List.append_assoc]

theorem schedule_fold (ps : List BirthDelete) (live : List Event)
    (insertions : ∀ e ∈ live, eIsIns e = true) :
    fifoFold (deadWord [] ps ++ live) = live.map birthTag := by
  rw [fifoFold_append]
  have empty := (deadWord_checked_empty [] ps rfl).2
  simp only [List.nil_append] at empty
  rw [empty,survivingBirths_fold [] live insertions,List.nil_append]

#print axioms deadWord_legal
end Sal.MRDTs.Paper1.AnchoredQueue.History
