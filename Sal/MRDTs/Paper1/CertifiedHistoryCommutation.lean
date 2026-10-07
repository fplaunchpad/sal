import Sal.MRDTs.Paper1.GuardedHistory
import Sal.MRDTs.Paper1.SpecificationVisibility

/-! Contextual commutation for independent sequential specifications whose
history machine remembers a legality prefix. Equivalent future legality is
sufficient even when the two remembered prefixes are different lists. -/
namespace Sal.MRDTs.Paper1.GuardedHistory
open Foundation
variable {D : MRDTSig}

def FutureLegal (S : SequentialSpec D) (p q : List (Op D.AppOp)) : Prop :=
  ∀ suffix, S.Legal (p ++ suffix) ↔ S.Legal (q ++ suffix)

private theorem run_transport (S : SequentialSpec D)
    {start finish : (machine S).State} {labels}
    (run : Runs (machine S).transition start labels finish) :
    ∀ other : (machine S).State, other.2 = start.2 → FutureLegal S start.1 other.1 →
      ∃ result, Runs (machine S).transition other labels result := by
  induction run with
  | nil start =>
    intro other _ _
    exact ⟨other,.nil _⟩
  | @cons start mid finish label labels step rest ih =>
    intro other same future
    cases label with
    | update e =>
      obtain ⟨legal,rfl⟩ := step
      have future' : FutureLegal S (start.1 ++ [e]) (other.1 ++ [e]) := by
        intro suffix
        simpa only [List.append_assoc] using future ([e] ++ suffix)
      obtain ⟨result,run'⟩ := ih (other.1 ++ [e],S.step other.2 e)
        (by simp only [same]) future'
      exact ⟨result,.cons ⟨(future [e]).mp legal,rfl⟩ run'⟩
    | query q answer =>
      obtain ⟨answerEq,rfl⟩ := step
      obtain ⟨result,run'⟩ := ih other same future
      exact ⟨result,.cons ⟨by simpa only [same] using answerEq,rfl⟩ run'⟩

/-- Legality swaps include all future update suffixes, so the result covers
arbitrary later updates and queries, not only an immediate observation. -/
theorem language_commutes_of_legal_swap (S : SequentialSpec D)
    (prefixClosed : ∀ pre suf, S.Legal (pre ++ suf) → S.Legal pre)
    (a b : Op D.AppOp)
    (steps : ∀ s, S.step (S.step s a) b = S.step (S.step s b) a)
    (legalSwap : ∀ pre suf,
      S.Legal (pre ++ [a,b] ++ suf) ↔ S.Legal (pre ++ [b,a] ++ suf)) :
    (language S).Commutes a b := by
  have exchange : ∀ x y : Op D.AppOp,
      (∀ s, S.step (S.step s x) y = S.step (S.step s y) x) →
      (∀ pre suf, S.Legal (pre ++ [x,y] ++ suf) ↔ S.Legal (pre ++ [y,x] ++ suf)) →
      ∀ pre suf, (language S).admits (pre ++ [.update x,.update y] ++ suf) →
        (language S).admits (pre ++ [.update y,.update x] ++ suf) := by
    intro x y stepSwap swap pre suf accepted
    obtain ⟨finish,run⟩ := accepted
    have grouped : Runs (machine S).transition (machine S).initial
        (pre ++ ([.update x,.update y] ++ suf)) finish := by
      simpa only [List.append_assoc] using run
    obtain ⟨start,before,tail⟩ := grouped.split pre _
    obtain ⟨mid,pair,after⟩ := tail.split [.update x,.update y] suf
    cases pair with
    | cons first rest =>
      obtain ⟨legalX,rfl⟩ := first
      cases rest with
      | cons second rest =>
        obtain ⟨legalXY,rfl⟩ := second
        cases rest
        have legalYX : S.Legal (start.1 ++ [y,x]) := by
          have legalXY' : S.Legal (start.1 ++ [x,y] ++ []) := by
            simpa only [List.append_nil,List.append_assoc,List.cons_append,List.nil_append,Prod.fst] using legalXY
          simpa only [List.append_nil] using (swap start.1 []).mp legalXY'
        have legalY : S.Legal (start.1 ++ [y]) := by
          apply prefixClosed _ [x]
          simpa only [List.append_assoc,List.cons_append,List.nil_append] using legalYX
        have future : FutureLegal S ((start.1 ++ [x]) ++ [y]) ((start.1 ++ [y]) ++ [x]) := by
          intro suffix
          simpa only [List.append_assoc,List.cons_append,List.nil_append] using swap start.1 suffix
        obtain ⟨result,after'⟩ := run_transport S after
          ((start.1 ++ [y]) ++ [x],S.step (S.step start.2 y) x)
          (stepSwap start.2).symm future
        have swapped : Runs (machine S).transition start
            ([.update y,.update x] ++ suf) result :=
          .cons ⟨legalY,rfl⟩ (.cons ⟨by
            simpa only [List.append_assoc,List.cons_append,List.nil_append] using legalYX,rfl⟩ after')
        exact ⟨result,by simpa only [List.append_assoc] using before.append swapped⟩
  intro pre suf
  exact ⟨exchange a b steps legalSwap pre suf,
    exchange b a (fun s => (steps s).symm) (fun pre suf => (legalSwap pre suf).symm) pre suf⟩

end Sal.MRDTs.Paper1.GuardedHistory
