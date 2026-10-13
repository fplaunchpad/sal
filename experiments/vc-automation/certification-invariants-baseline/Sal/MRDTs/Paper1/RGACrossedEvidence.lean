import Sal.MRDTs.Paper1.RGACrossedExecution
import Sal.MRDTs.Paper1.RGAStrictInvestigation

/-!
# Honest issuance and observed result of the crossed RGA execution

The finite store graph is defined in `RGACrossedExecution`. This module proves
issuance at the actual issuer heads, exact causal-past mint honesty, and the
hand-derived final query [5,4,8,7], without changing the RGA implementation.
-/
namespace Sal.MRDTs.Paper1.RGA.CrossedExecution.Evidence
open Sal.MRDTs.Foundation
open Sal.MRDTs.Instances.RGA
open Sal.MRDTs.Paper1.RGA.CrossedExecution

/-- An independently listed mint-time past, in causal order. -/
def pastIndices (i : I) : List I := match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [0,1]
  | 3 => [0,1,2]
  | 4 => [0,1,2,3]
  | 5 => [0,1]
  | 6 => [0,1,5]
  | _ => [0,1,5,6]

def pastOps (i : I) : List Event := (pastIndices i).map event

private theorem pastIndices_mem : ∀ i j : I,
    j ∈ pastIndices i ↔ j ∈ past i := by decide

private theorem event_injective : Function.Injective event := by
  intro i j h
  have times : ∀ i : I, (event i).1 = i.val + 1 := by
    intro i; fin_cases i <;> rfl
  have ht := congrArg Prod.fst h
  rw [times, times] at ht
  exact Fin.ext (Nat.add_right_cancel ht)

/-- The mint past replays to the state actually held at the issuing head. -/
theorem past_fold_issuer (i : I) :
    applySeq RGAM.toUpdateSig RGAM.init (pastOps i) = (records (issuer i)).1 := by
  fin_cases i <;> apply Prod.ext <;> funext x <;> apply Bool.eq_iff_iff.mpr <;>
    simp [pastOps, pastIndices, issuer, event, applySeq, RGAM, rgaUpdate,
      records, stateFor, data, Bool.or_eq_true, or_assoc]

/-- Every actual head satisfies the existing production issuance guard. -/
theorem issuer_guard (i : I) :
    applicable (event i) (records (issuer i)).1 := by
  fin_cases i <;>
    simp [applicable, event, issuer, records, stateFor, data]

/-- The same guard holds at an exact causal enumeration of the mint past. -/
theorem mint_guard (i : I) :
    applicable (event i) (applySeq RGAM.toUpdateSig RGAM.init (pastOps i)) := by
  rw [past_fold_issuer]
  exact issuer_guard i

private theorem past_nodup : ∀ i : I, (pastOps i).Nodup := by decide
private theorem past_respects : ∀ k : V, ∀ i : I,
    respects (pastOps i) (vis k) := by
  unfold respects
  decide +kernel

/-- Timestamp projection provides an exact causal-past event enumeration. -/
theorem past_enum (k : V) (i : I) (hi : issued k i) :
    listPermOf (pastOps i) {e ∈ (config k).events | (config k).vis e (event i)} := by
  refine ⟨past_nodup i, ?_⟩
  intro e
  constructor
  · intro he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hvis : (config k).vis (event j) (event i) :=
      ⟨j, i, rfl, rfl, hi, (pastIndices_mem i j).mp hj⟩
    exact ⟨(config k).vis_src hvis, hvis⟩
  · rintro ⟨_, j, ii, he, hiEq, hvis⟩
    have hieq : ii = i := event_injective hiEq.symm
    subst ii
    exact List.mem_map.mpr ⟨j, (pastIndices_mem i j).mpr hvis.2, he.symm⟩

/-- Every observed event has its exact mint past and honest guard at every
prefix where it is supported. This is stronger than checking only the endpoint. -/
theorem mint_honest (k : V) : MintHonest RGAM generation.CanIssue (config k) := by
  intro e he
  obtain ⟨i, rfl, hi⟩ := event_supported_issued he
  exact ⟨pastOps i, past_enum k i hi, past_respects k i, mint_guard i⟩

/-- A timestamp-fresh raw apply also carries its actual issuer-head guard. -/
theorem issued_apply (i : I) :
    IssuedStep RGAM generation (config (before i))
      (.apply (event i).time (event i).2.1 (event i).op) (config (newVersion i)) := by
  apply IssuedStep.apply (v := (issuer i).val) (s := (records (issuer i)).1)
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · exact issuer_guard i
  · exact apply_step i

theorem issued_fork : IssuedStep RGAM generation (config 2) (.fork 1 0) (config 3) := by
  exact .nonApply fork_step (by intro t r o h; cases h)

theorem issued_merge : IssuedStep RGAM generation (config 9) (.merge 0 1) (config 10) := by
  exact .nonApply merge_step (by intro t r o h; cases h)

/-- A genuine honestly issued execution reaches the final merged configuration.
The certificate records honest issuance before and after every raw store step. -/
theorem mint_certified : MintCertifiedReach RGAM generation (config 10) := by
  have h0 : MintCertifiedReach RGAM generation (config 0) := by
    rw [config_zero]
    exact .init
  have h1 := MintCertifiedReach.step h0 (mint_honest 0) (issued_apply 0) (mint_honest 1)
  have h2 := MintCertifiedReach.step h1 (mint_honest 1) (issued_apply 1) (mint_honest 2)
  have h3 := MintCertifiedReach.step h2 (mint_honest 2) issued_fork (mint_honest 3)
  have h4 := MintCertifiedReach.step h3 (mint_honest 3) (issued_apply 2) (mint_honest 4)
  have h5 := MintCertifiedReach.step h4 (mint_honest 4) (issued_apply 3) (mint_honest 5)
  have h6 := MintCertifiedReach.step h5 (mint_honest 5) (issued_apply 4) (mint_honest 6)
  have h7 := MintCertifiedReach.step h6 (mint_honest 6) (issued_apply 5) (mint_honest 7)
  have h8 := MintCertifiedReach.step h7 (mint_honest 7) (issued_apply 6) (mint_honest 8)
  have h9 := MintCertifiedReach.step h8 (mint_honest 8) (issued_apply 7) (mint_honest 9)
  exact .step h9 (mint_honest 9) issued_merge (mint_honest 10)

theorem certified_execution : CertifiedExecution RGAM generation (config 10) :=
  .ordinary mint_certified

private def ordered : List Event := [event 0, event 1, event 3, event 4,
  event 6, event 7, event 2, event 5]

private theorem ordered_fold :
    applySeq RGAM.toUpdateSig RGAM.init ordered = (records 10).1 := by
  apply Prod.ext <;> funext x <;> apply Bool.eq_iff_iff.mpr <;>
    simp [ordered, event, applySeq, RGAM, rgaUpdate, records, stateFor, data,
      Bool.or_eq_true, or_assoc]

private theorem ordered_wellFormed : VersionWellFormed {e | e ∈ ordered} := by
  constructor
  · intro a b ha hb ht
    simp only [Set.mem_setOf_eq, ordered, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [event]
  · intro ts r anchor he
    simp [ordered, event] at he
    rcases he with h | h | h | h | h | h
    · exact Or.inl h.2.2
    · exact Or.inl h.2.2
    all_goals
      right
      refine ⟨0, 0, ?_, ?_⟩ <;> simp_all [ordered, event]
  · intro ts r id he
    simp [ordered, event] at he
    rcases he with h | h
    all_goals
      refine ⟨0, 0, ?_⟩
      simp_all [ordered, event]

/-- The final visible sequence is hand-derived: later sibling 5 precedes 4
under root 2, and later sibling 8 precedes 7 under root 1; both roots are deleted. -/
theorem final_read : RGAM.query (records 10).1 () = [5, 4, 8, 7] := by
  have hperm : listPermOf ordered {e | e ∈ ordered} := ⟨by decide, fun _ => Iff.rfl⟩
  have hsorted : canonical ordered = ordered :=
    List.mergeSort_of_pairwise (by decide)
  have href := canonical_refines_list hperm ordered_wellFormed
  change read (applySeq RGAM.toUpdateSig RGAM.init (canonical ordered)) =
    listSpec.run (canonical ordered) at href
  rw [hsorted, ordered_fold] at href
  change read (records 10).1 = _
  rw [href]
  rfl

theorem final_head_state : (config 10).headState 0 = some (records 10).1 := by
  simp [Configuration.headState, headStateFrom, config, head, heads, ver, Option.bind]

/-- The observation itself is an unchanged store query transition. -/
theorem final_query : Step RGAM (config 10) (.query 0 () [5, 4, 8, 7]) (config 10) := by
  apply Step.query (s := (records 10).1)
  · exact final_head_state
  · exact final_read.symm

/-- The raw execution records the actual final query label. -/
def observedTrace : List (Label RGAM × Configuration RGAM) :=
  trace ++ [(.query 0 () [5, 4, 8, 7], config 10)]

theorem observed_execution : (labeledTS RGAM).Execution (initConfig RGAM) observedTrace := by
  rw [← config_zero]
  exact .cons (apply_step 0) (.cons (apply_step 1) (.cons fork_step
    (.cons (apply_step 2) (.cons (apply_step 3) (.cons (apply_step 4)
      (.cons (apply_step 5) (.cons (apply_step 6) (.cons (apply_step 7)
        (.cons merge_step (.cons final_query (.nil _)))))))))))

/-- The reachable eight-event head fails the stronger strict allocating-list
criterion. The imported refutation excludes every ordering and allocation. -/
theorem strict_failure :
    ¬ SpecificationRALinearizable RGAM emptyPolicy Strict.spec (config 10) := by
  apply Strict.Investigation.crossed_not_specificationRA emptyPolicy (config 10)
    0 10 (records 10).1 (↑((records 10).2.image event) : Set Event)
    (event 6) (event 2) (event 3) (event 5) 1 2 [5, 4, 8, 7]
  · rfl
  · rfl
  · exact final_read
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rfl
  · rfl
  · rfl
  · intro d hd hop
    change d ∈ ((records 10).2.image event) at hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    fin_cases i <;> first | rfl | (simp [event, Op.op] at hop)
  · intro d hd hop
    change d ∈ ((records 10).2.image event) at hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    fin_cases i <;> first | rfl | (simp [event, Op.op] at hop)
  · decide
  · decide
  · change vis 10 (event 2) (event 3)
    decide
  · change vis 10 (event 5) (event 6)
    decide

/-- The strict candidate fails on an actually reachable, honestly issued
configuration, rather than merely on an abstract store or a fixed prefix. -/
theorem certified_strict_counterexample :
    ∃ C : Configuration RGAM, MintCertifiedReach RGAM generation C ∧
      ¬ SpecificationRALinearizable RGAM emptyPolicy Strict.spec C :=
  ⟨config 10, mint_certified, strict_failure⟩

theorem not_every_certified_strict :
    ¬ ∀ C : Configuration RGAM, MintCertifiedReach RGAM generation C →
      SpecificationRALinearizable RGAM emptyPolicy Strict.spec C := by
  intro guarantee
  exact strict_failure (guarantee (config 10) mint_certified)

/-- PASS+FAIL: the endpoint displays all four children, excludes the removed
anchors, and cannot be explained by the strict specification-visible criterion. -/
example : read (records 10).1 = [5, 4, 8, 7] ∧
    read (records 10).1 ≠ [] ∧
    1 ∉ read (records 10).1 ∧ 2 ∉ read (records 10).1 ∧
    ¬ SpecificationRALinearizable RGAM emptyPolicy Strict.spec (config 10) := by
  have hread : read (records 10).1 = [5, 4, 8, 7] := final_read
  rw [hread]
  exact ⟨rfl, by decide, by decide, by decide, strict_failure⟩

#print axioms issuer_guard
#print axioms mint_honest
#print axioms mint_certified
#print axioms final_read
#print axioms final_query
#print axioms strict_failure
#print axioms certified_strict_counterexample
end Sal.MRDTs.Paper1.RGA.CrossedExecution.Evidence
