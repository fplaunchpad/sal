import Sal.MRDTs.Paper1.AnchoredQueueSchedule

namespace Sal.MRDTs.Paper1.AnchoredQueue.History
open Foundation Instances.EmbedRGA

def pairSupport (U : Set Event) (ps : List BirthDelete) : Prop :=
  ∀ p ∈ ps, p.birth ∈ U ∧ p.deletion ∈ U

theorem born_mem_prefix {U : Set Event} (unique : ∀ a ∈ U, ∀ b ∈ U, a.time = b.time → a = b)
    {pre : List Event} (support : ∀ e ∈ pre, e ∈ U) {birth : Event}
    (member : birth ∈ U) (born : birth.time ∈ eInsIds pre) : birth ∈ pre := by
  obtain ⟨e,he,_,time⟩ := mem_eInsIds.mp born
  exact (unique e (support e he) birth member time) ▸ he

/-- Scheduling omits only births already emitted in the prefix; its total
support is exactly that of the supplied original birth/deletion pairs. -/
theorem deadWord_support {U : Set Event}
    (unique : ∀ a ∈ U, ∀ b ∈ U, a.time = b.time → a = b)
    (pre : List Event) (ps : List BirthDelete)
    (support : ∀ e ∈ pre, e ∈ U) (pairs : pairSupport U ps) (e : Event) :
    e ∈ pre ++ deadWord pre ps ↔ e ∈ pre ∨ ∃ p ∈ ps, e = p.birth ∨ e = p.deletion := by
  induction ps generalizing pre with
  | nil => simp [deadWord]
  | cons p ps ih =>
      have hp := pairs p List.mem_cons_self
      have remaining : pairSupport U ps := fun q hq => pairs q (List.mem_cons_of_mem p hq)
      by_cases born : p.birth.time ∈ eInsIds pre
      · have already := born_mem_prefix unique support hp.1 born
        have step := ih (pre ++ [p.deletion])
          (by intro x hx; rcases List.mem_append.mp hx with hx | hx
              · exact support x hx
              · simpa using (List.mem_singleton.mp hx) ▸ hp.2) remaining
        simp only [deadWord,if_pos born]
        have rearrange : pre ++ p.deletion :: deadWord (pre ++ [p.deletion]) ps =
            (pre ++ [p.deletion]) ++ deadWord (pre ++ [p.deletion]) ps := by
          simp [List.append_assoc]
        rw [rearrange,step]
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        clear ih support pairs unique step rearrange remaining hp born
        have includeBirth : e = p.birth → e ∈ pre := fun eq => eq.symm ▸ already
        simp only [or_and_right,exists_or,exists_eq_left]
        constructor
        · rintro ((old | del) | rest)
          · exact Or.inl old
          · exact Or.inr (Or.inl (Or.inr del))
          · exact Or.inr (Or.inr rest)
        · rintro (old | (birth | del) | rest)
          · exact Or.inl (Or.inl old)
          · exact Or.inl (Or.inl (includeBirth birth))
          · exact Or.inl (Or.inr del)
          · exact Or.inr rest
      · have step := ih (pre ++ [p.birth,p.deletion])
          (by intro x hx; rcases List.mem_append.mp hx with hx | hx
              · exact support x hx
              · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
                rcases hx with rfl | rfl
                · exact hp.1
                · exact hp.2) remaining
        simp only [deadWord,if_neg born]
        have rearrange : pre ++ p.birth :: p.deletion :: deadWord (pre ++ [p.birth,p.deletion]) ps =
            (pre ++ [p.birth,p.deletion]) ++ deadWord (pre ++ [p.birth,p.deletion]) ps := by
          simp [List.append_assoc]
        rw [rearrange,step]
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        simp only [or_and_right,exists_or,exists_eq_left]
        simp only [or_assoc]


private theorem birth_ne_deletion (p q : BirthDelete) : p.birth ≠ q.deletion := by
  intro eq
  have insert := p.insertion
  rw [eq] at insert
  have target := q.target
  simp only [eIsIns,Op.op] at insert target
  rw [target] at insert
  contradiction

/-- Duplicate dequeue identities are allowed, but each dequeue event is
listed once; duplicate birth events are eliminated by the birth-prefix test. -/
theorem deadWord_nodup (pre : List Event) (ps : List BirthDelete)
    (preNodup : pre.Nodup) (deletions : (ps.map BirthDelete.deletion).Nodup)
    (absent : ∀ p ∈ ps, p.deletion ∉ pre) : (pre ++ deadWord pre ps).Nodup := by
  induction ps generalizing pre with
  | nil => simpa [deadWord] using preNodup
  | cons p ps ih =>
      obtain ⟨noDuplicate,deletions⟩ := List.nodup_cons.mp deletions
      have missing := absent p List.mem_cons_self
      have later : ∀ q ∈ ps, q.deletion ≠ p.deletion := by
        intro q hq eq
        exact noDuplicate (List.mem_map.mpr ⟨q,hq,eq⟩)
      by_cases born : p.birth.time ∈ eInsIds pre
      · have prefix' : (pre ++ [p.deletion]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨preNodup,by simp,?_⟩
          intro x hx y hy eq
          have same := List.mem_singleton.mp hy
          exact missing ((eq.trans same) ▸ hx)
        have absent' : ∀ q ∈ ps, q.deletion ∉ pre ++ [p.deletion] := by
          intro q hq mem
          rcases List.mem_append.mp mem with old | current
          · exact absent q (List.mem_cons_of_mem p hq) old
          · exact later q hq (List.mem_singleton.mp current)
        have out := ih (pre ++ [p.deletion]) prefix' deletions absent'
        simpa [deadWord,born,List.append_assoc] using out
      · have birthMissing : p.birth ∉ pre := by
          intro mem
          exact born (mem_eInsIds.mpr ⟨p.birth,mem,p.insertion,rfl⟩)
        have prefix' : (pre ++ [p.birth,p.deletion]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨preNodup,by simp [birth_ne_deletion p p],?_⟩
          intro x hx y hy eq
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
          rcases hy with birth | deletion
          · exact birthMissing ((eq.trans birth) ▸ hx)
          · exact missing ((eq.trans deletion) ▸ hx)
        have absent' : ∀ q ∈ ps, q.deletion ∉ pre ++ [p.birth,p.deletion] := by
          intro q hq mem
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mem
          rcases mem with old | birth | current
          · exact absent q (List.mem_cons_of_mem p hq) old
          · exact birth_ne_deletion p q birth.symm
          · exact later q hq current
        have out := ih (pre ++ [p.birth,p.deletion]) prefix' deletions absent'
        simpa [deadWord,born,List.append_assoc] using out

/-- The scheduler enumerates the original event set exactly once. Coverage
and survivor separation refer to original labels, not to its computed word. -/
theorem schedule_listPermOf {U E : Set Event}
    (unique : ∀ a ∈ U, ∀ b ∈ U, a.time = b.time → a = b)
    (ps : List BirthDelete) (live : List Event)
    (pairs : pairSupport U ps)
    (deletions : (ps.map BirthDelete.deletion).Nodup)
    (liveNodup : live.Nodup)
    (separated : ∀ e ∈ live, ∀ p ∈ ps, e ≠ p.birth ∧ e ≠ p.deletion)
    (coverage : ∀ e, e ∈ E ↔ (∃ p ∈ ps, e = p.birth ∨ e = p.deletion) ∨ e ∈ live) :
    listPermOf (deadWord [] ps ++ live) E := by
  have support : ∀ e, e ∈ deadWord [] ps ↔ ∃ p ∈ ps, e = p.birth ∨ e = p.deletion := by
    intro e
    simpa using deadWord_support unique [] ps (by simp) pairs e
  refine ⟨List.nodup_append.mpr ⟨?_,liveNodup,?_⟩,?_⟩
  · simpa using deadWord_nodup [] ps List.nodup_nil deletions (by simp)
  · intro x hx y hy eq
    obtain ⟨p,hp,h⟩ := (support x).mp hx
    subst y
    rcases h with birth | deletion
    · exact (separated x hy p hp).1 birth
    · exact (separated x hy p hp).2 deletion
  · intro e
    rw [List.mem_append,support,← coverage e]

/-- Survivor freshness follows from original-label separation and timestamp
uniqueness, rather than from the dead-word construction's answer. -/
theorem surviving_fresh {U : Set Event}
    (unique : ∀ a ∈ U, ∀ b ∈ U, a.time = b.time → a = b)
    (ps : List BirthDelete) (live : List Event)
    (pairs : pairSupport U ps) (liveSupport : ∀ e ∈ live, e ∈ U)
    (separated : ∀ e ∈ live, ∀ p ∈ ps, e ≠ p.birth ∧ e ≠ p.deletion) :
    ∀ e ∈ live, e.time ∉ eInsIds (deadWord [] ps) := by
  intro e he born
  obtain ⟨old,hold,_,time⟩ := mem_eInsIds.mp born
  have source := deadWord_support unique [] ps (by simp) pairs old
  have member : ∃ p ∈ ps, old = p.birth ∨ old = p.deletion := by simpa using source.mp hold
  obtain ⟨p,hp,h⟩ := member
  have oldSupport : old ∈ U := by
    rcases h with eq | eq
    · exact eq ▸ (pairs p hp).1
    · exact eq ▸ (pairs p hp).2
  have same := unique old oldSupport e (liveSupport e he) time
  rcases h with birth | deletion
  · exact (separated e he p hp).1 (same.symm.trans birth)
  · exact (separated e he p hp).2 (same.symm.trans deletion)

def birthEntry (e : Event) : Option (Nat × Nat) :=
  match e.op with
  | .ins value _ _ => some (e.time,value)
  | .del _ => none

/-- An insertion-only suffix has the independent FIFO order supplied by its
list, irrespective of coordinates. -/
theorem insertion_suffix_fold (births : List Event)
    (insertions : ∀ e ∈ births, eIsIns e = true) (initial : List (Nat × Nat)) :
    births.foldl fifoStep initial = initial ++ births.filterMap birthEntry := by
  induction births generalizing initial with
  | nil => simp
  | cons e rest ih =>
      have first := insertions e List.mem_cons_self
      have remaining : ∀ e ∈ rest, eIsIns e = true :=
        fun e he => insertions e (List.mem_cons_of_mem _ he)
      rcases e with ⟨time,rep,op⟩
      cases op with
      | del target => simp [eIsIns] at first
      | ins value pref anchor =>
          simp only [List.foldl_cons,fifoStep,Op.op,Op.time,List.filterMap_cons,birthEntry]
          rw [ih remaining]
          simp [List.append_assoc]

theorem schedule_fifo_result (ps : List BirthDelete) (live : List Event)
    (insertions : ∀ e ∈ live, eIsIns e = true) :
    fifoFold (deadWord [] ps ++ live) = live.filterMap birthEntry := by
  rw [fifoFold_append]
  have empty : fifoFold (deadWord [] ps) = [] := by
    simpa using (deadWord_checked_empty [] ps rfl).2
  rw [empty,insertion_suffix_fold live insertions]
  rfl

/-- Independent scheduling theorem: original-label coverage, one copy of each
dequeue event, and survivor separation suffice for a full legal FIFO replay. -/
theorem schedule_correct {U E : Set Event}
    (unique : ∀ a ∈ U, ∀ b ∈ U, a.time = b.time → a = b)
    (ps : List BirthDelete) (live : List Event)
    (pairs : pairSupport U ps) (liveSupport : ∀ e ∈ live, e ∈ U)
    (deletions : (ps.map BirthDelete.deletion).Nodup)
    (insertions : ∀ e ∈ live, eIsIns e = true)
    (distinct : live.Pairwise (fun a b => a.time ≠ b.time))
    (separated : ∀ e ∈ live, ∀ p ∈ ps, e ≠ p.birth ∧ e ≠ p.deletion)
    (coverage : ∀ e, e ∈ E ↔ (∃ p ∈ ps, e = p.birth ∨ e = p.deletion) ∨ e ∈ live) :
    listPermOf (deadWord [] ps ++ live) E ∧
    fifoLegal (deadWord [] ps ++ live) ∧
    fifoFold (deadWord [] ps ++ live) = live.filterMap birthEntry := by
  have nodup : live.Nodup := distinct.imp fun {a b} ne eq => ne (congrArg Op.time eq)
  exact ⟨schedule_listPermOf unique ps live pairs deletions nodup separated coverage,
    schedule_legal ps live insertions distinct
      (surviving_fresh unique ps live pairs liveSupport separated),
    schedule_fifo_result ps live insertions⟩

#print axioms schedule_listPermOf

end Sal.MRDTs.Paper1.AnchoredQueue.History
