import Sal.MRDTs.Paper1.AnchoredQueue

/-! Independent FIFO witness infrastructure. The recursive checker is equivalent
 to the public legality predicate, without inspecting representation state.
 The scheduling and certified-execution bridge are completed in
 AnchoredQueueSchedule and AnchoredQueueCertificate. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue.History
open Foundation Instances.EmbedRGA

/-- Legality at the next position uses only independent FIFO replay and the
 abstract birth prefix. In particular no representation coordinate is read. -/
def NextLegal (pre : List Event) (e : Event) : Prop :=
  fifoApplicable (fifoFold pre) e ∧
  (eIsIns e = true → e.time ∉ eInsIds pre) ∧
  (∀ target, e.op = .del target → target ∈ eInsIds pre)

instance (pre : List Event) (e : Event) : Decidable (NextLegal pre e) := by
  unfold NextLegal fifoApplicable
  cases e with
  | mk t rest =>
    rcases rest with ⟨r,op⟩
    cases op with
    | ins value coordinate anchor =>
      exact decidable_of_iff
        (t ∉ (fifoFold pre).map Prod.fst ∧ t ∉ eInsIds pre)
        (by simp only [Op.op, Op.time, eIsIns, reduceCtorEq, false_implies,
          implies_true, and_true, true_implies])
    | del target =>
      exact decidable_of_iff
        ((target ∉ (fifoFold pre).map Prod.fst ∨
          (fifoFold pre).head?.map Prod.fst = some target) ∧ target ∈ eInsIds pre)
        (by simp only [Op.op, Op.time, eIsIns, reduceCtorEq, false_implies,
          true_and, EOp.del.injEq, forall_eq'])

/-- An executable legality checker over an independent abstract prefix. -/
def CheckFrom (pre : List Event) : List Event → Prop
  | [] => True
  | e :: es => NextLegal pre e ∧ CheckFrom (pre ++ [e]) es

instance (pre es : List Event) : Decidable (CheckFrom pre es) := by
  induction es generalizing pre with
  | nil => exact isTrue trivial
  | cons e es ih => unfold CheckFrom; exact instDecidableAnd

theorem checkFrom_iff (pre es : List Event) : CheckFrom pre es ↔
    ∀ before e after, es = before ++ e :: after → NextLegal (pre ++ before) e := by
  induction es generalizing pre with
  | nil => simp [CheckFrom]
  | cons first es ih =>
    constructor
    · rintro ⟨next,rest⟩ before e after split
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl,_⟩ := split
        simpa using next
      | cons x before =>
        simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl,split⟩ := split
        have h := (ih (pre ++ [first])).mp rest before e after split
        simpa [List.append_assoc] using h
    · intro all
      refine ⟨?_, (ih (pre ++ [first])).mpr ?_⟩
      · simpa using all [] first es rfl
      · intro before e after split
        have h := all (first :: before) e after (by simp [split])
        simpa [List.append_assoc] using h

theorem checkFrom_append (pre xs ys : List Event) :
    CheckFrom pre (xs ++ ys) ↔ CheckFrom pre xs ∧ CheckFrom (pre ++ xs) ys := by
  induction xs generalizing pre with
  | nil => simp [CheckFrom]
  | cons x xs ih => simp [CheckFrom,ih,List.append_assoc,and_assoc]

theorem check_iff_legal (es : List Event) : CheckFrom [] es ↔ fifoLegal es := by
  simpa [fifoLegal, NextLegal] using checkFrom_iff [] es

/-- A proposed schedule can be checked without computing its expected query
 from the implementation being tested. -/
theorem legal_of_check {es : List Event} (checked : CheckFrom [] es) : fifoLegal es :=
  (check_iff_legal es).mp checked

/-- One concrete independent word, with all three required obligations. The
 representation equality is stronger than a query equality and supports any
 later public projection of the tagged live list. -/
structure Witness (C : Configuration Q) (s : State) (E : Set Event) where
  word : List Event
  perm : listPermOf word E
  invariantOrder : respects word (InvariantOrder.order (Valid C)
    CertifiedRGAInvariantReplay.policy C.replayContext E)
  specificationVisibility : respects word (projectedSpecVisibility id language C.replayContext)
  legal : fifoLegal word
  representation : s.map (fun r => (r.1,r.2.1)) = fifoFold word

theorem Witness.admitted {C : Configuration Q} {s : State} {E : Set Event}
    (w : Witness C s E) (q : Q.Query) :
    language.admits (projectedLabels id w.word ++ [.query q (Q.query s q)]) := by
  have query : Q.query s q = fifoSpec.query (fifoSpec.run w.word) q := by
    change s.map (fun r => r.2.1) = (fifoFold w.word).map Prod.snd
    rw [← w.representation]
    simp [List.map_map, Function.comp_def]
  rw [query]
  exact GuardedHistory.admits_updates_query fifoSpec
    (fun _ _ h => fifoLegal_prefix h) w.word w.legal q

/-- The same independent FIFO word witnesses invariant-order RA and independent
 specification visibility. This theorem does not assume a second history. -/
theorem versions_of_witnesses {C : Configuration Q}
    (witnesses : ∀ v s E, C.ver v = some (s,E) → Nonempty (Witness C s E)) :
    InvariantOrder.VersionsRA Q (Valid C)
      CertifiedRGAInvariantReplay.policy language C := by
  intro v s E stored q
  obtain ⟨w⟩ := witnesses v s E stored
  exact ⟨w.word,w.perm,w.invariantOrder,w.specificationVisibility,w.admitted q⟩

#print axioms check_iff_legal
#print axioms versions_of_witnesses
end Sal.MRDTs.Paper1.AnchoredQueue.History
