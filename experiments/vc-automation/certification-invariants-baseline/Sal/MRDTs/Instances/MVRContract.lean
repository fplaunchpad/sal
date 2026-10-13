import Sal.MRDTs.Instances.MVR

/-! Shared MVR sequential specification and historical grow-only refinement.
Production is certified by `MVRLiveContract.verified`, reusing the live-set
machine and legality below with a compact concrete state. -/
namespace Sal.MRDTs.Instances.MVR

open Sal.MRDTs.Foundation
open Classical
attribute [local instance] rc

def writeValue (e : Op MVROp) : ℕ :=
  match e.2.2 with | .write v _ => v

def clientStep (s : Finset (ℕ × ℕ)) (e : Op MVROp) : Finset (ℕ × ℕ) :=
  insert (e.1, writeValue e) (s.filter (fun p => p.1 ∉ overwrites e))

/-- Overwrite targets must have been born, but need not still be live:
two concurrent writes can supersede the same previously visible write. -/
def clientLegal (ops : List (Op MVROp)) : Prop :=
  (ops.map Prod.fst).Nodup ∧
  ∀ pre e post, ops = pre ++ e :: post →
    ∀ n ∈ overwrites e, n ∈ pre.map Prod.fst

def queryValues (s : Finset (ℕ × ℕ)) : Set ℕ := {v | ∃ n, (n, v) ∈ s}

def clientSpec : SequentialSpec MVR where
  State := Finset (ℕ × ℕ)
  init := ∅
  step := clientStep
  Legal := clientLegal
  query := fun s _ => queryValues s

def stateRel (s : MVR.State) (q : Finset (ℕ × ℕ)) : Prop :=
  ∀ p, p ∈ q ↔ s.1 p = true ∧ s.2 p.1 = false

theorem fold_write_iff (ops : List (Op MVROp)) (p : ℕ × ℕ) :
    (applySeq MVR.toUpdateSig MVR.init ops).1 p = true ↔
      ∃ e ∈ ops, e.1 = p.1 ∧ writeValue e = p.2 := by
  constructor
  · intro h
    obtain ⟨e, he, O, hop, ht⟩ := MVR_fold_bound₁ h
    exact ⟨e, he, ht, by simp [writeValue, hop]⟩
  · rintro ⟨⟨t, r, ⟨v, O⟩⟩, he, ht, hv⟩
    have h := MVR_contrib₁ he
    simpa [writeValue] using (show
      (applySeq MVR.toUpdateSig MVR.init ops).1 p = true from by
        have hp : p = (t, v) := Prod.ext ht.symm hv.symm
        simpa [hp] using h)

theorem fold_overwrite_iff (ops : List (Op MVROp)) (n : ℕ) :
    (applySeq MVR.toUpdateSig MVR.init ops).2 n = true ↔
      ∃ e ∈ ops, n ∈ overwrites e := by
  constructor
  · intro h
    obtain ⟨e, he, v, O, hop, hn⟩ := MVR_fold_bound₂ h
    exact ⟨e, he, by simpa [overwrites, hop] using hn⟩
  · rintro ⟨⟨t, r, ⟨v, O⟩⟩, he, hn⟩
    exact MVR_contrib₂ he hn

/-- Every named overwrite is a birth visible to the issuer. -/
theorem issued_overwrite {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {b : Op MVROp}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ overwrites b) :
    ∃ a ∈ C.events, C.vis a b ∧ a.1 = n := by
  obtain ⟨ops, hp, _, hg⟩ := exec.mintHonest b hb
  obtain ⟨t, r, ⟨v, O⟩⟩ := b
  obtain ⟨⟨w, hw⟩, _⟩ := (hg.2 v O rfl n).mp hn
  obtain ⟨a, ha, ht, _⟩ := (fold_write_iff ops (n, w)).mp hw
  exact ⟨a, ((hp.2 a).mp ha).1, ((hp.2 a).mp ha).2, ht⟩

theorem issued_overwrite_lt {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {b : Op MVROp}
    (hb : b ∈ C.events) {n : ℕ} (hn : n ∈ overwrites b) : n < b.1 := by
  obtain ⟨a, _, hv, ht⟩ := issued_overwrite exec hb hn
  simpa [ht] using C.causal_mono hv

/-- On an issued write, the timestamp guard is already implied by the
observed-overwrite payload. This is the client-facing form of rc. -/
theorem rc_iff_overwrite_of_execution {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {a b : Op MVROp}
    (hb : b ∈ C.events) :
    MVR.toUpdateSig.rc a b ↔ a.1 ∈ overwrites b := by
  rw [rc_before_iff]
  exact ⟨And.right, fun h => ⟨issued_overwrite_lt exec hb h, h⟩⟩

/-- The payload-based policy cannot orient concurrent issued writes. -/
theorem rc_implies_visibility {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {a b : Op MVROp}
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hrc : MVR.toUpdateSig.rc a b) : C.vis a b := by
  obtain ⟨birth, hm, hv, ht⟩ := issued_overwrite exec hb ((rc_before_iff a b).mp hrc).2
  have heq := C.replayContext.ts_unique hm ha ht
  simpa [heq] using hv

theorem overwrite_iff_successor {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {E : Set (Op MVROp)}
    (hin : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {a : Op MVROp} (ha : a ∈ E) :
    (∃ b ∈ E, a.1 ∈ overwrites b) ↔ ∃ b ∈ E, C.vis a b := by
  constructor
  · rintro ⟨b, hb, hn⟩
    obtain ⟨birth, hm, hv, ht⟩ := issued_overwrite exec (hin b hb) hn
    have heq := C.replayContext.ts_unique hm (hin a ha) ht
    exact ⟨b, hb, heq ▸ hv⟩
  · rintro ⟨b, hb, hv⟩
    obtain ⟨ops, hp, _, hg⟩ := exec.mintHonest b (hin b hb)
    have hai : a ∈ ops := (hp.2 a).mpr ⟨hin a ha, hv⟩
    have hwrite := (fold_write_iff ops (a.1, writeValue a)).mpr ⟨a, hai, rfl, rfl⟩
    cases hov : (applySeq MVR.toUpdateSig MVR.init ops).2 a.1 with
    | true =>
      obtain ⟨c, hc, hn⟩ := (fold_overwrite_iff ops a.1).mp hov
      exact ⟨c, hclosed c b ((hp.2 c).mp hc).2 hb, hn⟩
    | false =>
      obtain ⟨t, r, ⟨v, O⟩⟩ := b
      exact ⟨(t, r, .write v O), hb, (hg.2 v O rfl a.1).mpr
        ⟨⟨writeValue a, hwrite⟩, hov⟩⟩

/-- Every stored version exposes exactly its causally maximal writes. -/
theorem version_maximal {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C)
    {v : Version} {s : MVR.State} {E : Set (Op MVROp)}
    (hver : C.ver v = some (s, E)) (p : ℕ × ℕ) :
    (s.1 p = true ∧ s.2 p.1 = false) ↔
      ∃ a ∈ E, a.1 = p.1 ∧ writeValue a = p.2 ∧ ∀ b ∈ E, ¬ C.vis a b := by
  have hcfg := exec.canonicalConfig (fun C _ => mvrJoin C.replayContext)
  obtain ⟨ops, hp, _, hf⟩ := hcfg.canonical v s E hver
  have hin := hcfg.version_events_supported v s E hver
  have hc := hcfg.version_events_causal v s E hver
  rw [← hf]
  constructor
  · rintro ⟨hw, ho⟩
    obtain ⟨a, ha, ht, hv⟩ := (fold_write_iff ops p).mp hw
    refine ⟨a, (hp.2 a).mp ha, ht, hv, ?_⟩
    intro b hb hab
    obtain ⟨c, hce, hn⟩ := (overwrite_iff_successor exec hin hc ((hp.2 a).mp ha)).mpr ⟨b, hb, hab⟩
    have ht' := (fold_overwrite_iff ops p.1).mpr ⟨c, (hp.2 c).mpr hce, ht ▸ hn⟩
    rw [ho] at ht'
    contradiction
  · rintro ⟨a, ha, ht, hv, hmax⟩
    refine ⟨(fold_write_iff ops p).mpr ⟨a, (hp.2 a).mpr ha, ht, hv⟩, ?_⟩
    cases ho : (applySeq MVR.toUpdateSig MVR.init ops).2 p.1 with
    | false => rfl
    | true =>
      obtain ⟨c, hc', hn⟩ := (fold_overwrite_iff ops p.1).mp ho
      obtain ⟨b, hb, hab⟩ := (overwrite_iff_successor exec hin hc ha).mp
        ⟨c, (hp.2 c).mp hc', ht.symm ▸ hn⟩
      exact (hmax b hb hab).elim

#print axioms version_maximal

def chronological (ops : List (Op MVROp)) : List (Op MVROp) :=
  ops.mergeSort (fun a b => a.1 ≤ b.1)

theorem chronological_perm (ops : List (Op MVROp)) : (chronological ops).Perm ops :=
  List.mergeSort_perm _ _

theorem chronological_sorted (ops : List (Op MVROp)) :
    (chronological ops).Pairwise (fun a b => a.1 ≤ b.1) := by
  have htrans : ∀ a b c : Op MVROp, decide (a.1 ≤ b.1) = true →
      decide (b.1 ≤ c.1) = true → decide (a.1 ≤ c.1) = true := by
    intro a b c hab hbc
    exact decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have htotal : ∀ a b : Op MVROp,
      (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
    intro a b
    simpa using le_total a.1 b.1
  have h := List.pairwise_mergeSort htrans htotal ops
  simpa [chronological] using h

theorem chronological_respects (C : Configuration MVR) (E : Set (Op MVROp))
    (ops : List (Op MVROp)) : respects (chronological ops) (loOn C.replayContext E) := by
  apply (chronological_sorted ops).imp
  intro a b hab hlo
  rcases hlo with hvis | hrc
  · exact (not_lt_of_ge hab) (C.causal_mono hvis.1)
  · exact (not_lt_of_ge hab) ((rc_before_iff b a).mp hrc.2.2.1).1

/-- Sorted witnesses fold to precisely the live finite set, without keeping
births or overwrite logs in the abstract state. -/
theorem fold_refines : ∀ ops : List (Op MVROp),
    ops.Pairwise (fun a b => a.1 ≤ b.1) →
    (∀ e ∈ ops, ∀ n ∈ overwrites e, n < e.1) →
    stateRel (applySeq MVR.toUpdateSig MVR.init ops) (clientSpec.run ops) := by
  intro ops
  induction ops using List.reverseRecOn with
  | nil =>
    intro _ _ p
    simp [clientSpec, SequentialSpec.run, SequentialMachine.run,
      applySeq, MVR_init_eq]
  | append_singleton pre e ih =>
    intro hs hb
    have hpre := (List.pairwise_append.mp hs).1
    have hbound : ∀ a ∈ pre, ∀ n ∈ overwrites a, n < a.1 :=
      fun a ha => hb a (List.mem_append_left _ ha)
    have heBound := hb e (by simp)
    have hbefore : ∀ a ∈ pre, a.1 ≤ e.1 := by
      intro a ha
      exact (List.pairwise_append.mp hs).2.2 a ha e (by simp)
    have hfresh : (applySeq MVR.toUpdateSig MVR.init pre).2 e.1 = false := by
      cases h : (applySeq MVR.toUpdateSig MVR.init pre).2 e.1 with
      | false => rfl
      | true =>
        obtain ⟨a, ha, hn⟩ := (fold_overwrite_iff pre e.1).mp h
        exact ((not_lt_of_ge (hbefore a ha)) (hbound a ha e.1 hn)).elim
    have hself : e.1 ∉ overwrites e := fun h => (Nat.lt_irrefl _) (heBound e.1 h)
    have hi := ih hpre hbound
    intro p
    rw [SequentialSpec.run_append_single, applySeq_append_single]
    obtain ⟨t, r, ⟨v, O⟩⟩ := e
    change p ∈ clientStep (clientSpec.run pre) (t, r, .write v O) ↔
      (mvrUpdate (applySeq MVR.toUpdateSig MVR.init pre) (t, r, .write v O)).1 p = true ∧
      (mvrUpdate (applySeq MVR.toUpdateSig MVR.init pre) (t, r, .write v O)).2 p.1 = false
    by_cases hp : p = (t, v)
    · subst p
      simp [clientStep, writeValue, mvrUpdate, hfresh, show t ∉ O from hself]
    · simp [clientStep, writeValue, overwrites, mvrUpdate, hp, hi p, and_assoc]

theorem chronological_legal {C : Configuration MVR}
    (exec : CertifiedExecution MVR generation C) {E : Set (Op MVROp)}
    (hin : ∀ e ∈ E, e ∈ C.events)
    (hclosed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {ops : List (Op MVROp)} (hp : listPermOf ops E) :
    clientSpec.Legal (chronological ops) := by
  have hperm : listPermOf (chronological ops) E :=
    ⟨(chronological_perm ops).symm.nodup hp.1,
      fun a => (chronological_perm ops).mem_iff.trans (hp.2 a)⟩
  have hnd : ((chronological ops).map Prod.fst).Nodup := by
    apply hperm.1.map_on
    intro a ha b hb ht
    exact C.replayContext.ts_unique (hin a ((hperm.2 a).mp ha))
      (hin b ((hperm.2 b).mp hb)) ht
  refine ⟨hnd, ?_⟩
  intro pre e post hsplit n hn
  have he : e ∈ E := (hperm.2 e).mp (by rw [hsplit]; simp)
  obtain ⟨a, ha, hv, ht⟩ := issued_overwrite exec (hin e he) hn
  have hain : a ∈ chronological ops := (hperm.2 a).mpr (hclosed a e hv he)
  rw [hsplit, List.mem_append, List.mem_cons] at hain
  rcases hain with ha | rfl | ha
  · exact List.mem_map.mpr ⟨a, ha, ht⟩
  · exact ((Nat.lt_irrefl _) (C.causal_mono hv)).elim
  · have hsort := chronological_sorted ops
    rw [hsplit] at hsort
    have hle := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1 a ha
    exact ((not_lt_of_ge hle) (C.causal_mono hv)).elim

def clientSequentialCorrectness : SequentialCorrectnessCertificate MVR generation rc clientSpec stateRel where
  sound C exec replay := by
    intro v s E hver
    have hcfg := exec.canonicalConfig (fun C _ => mvrJoin C.replayContext)
    have hin := hcfg.version_events_supported v s E hver
    have hc := hcfg.version_events_causal v s E hver
    obtain ⟨ops, hp, _, hf⟩ := replay v s E hver
    have hperm : listPermOf (chronological ops) E :=
      ⟨(chronological_perm ops).symm.nodup hp.1,
        fun a => (chronological_perm ops).mem_iff.trans (hp.2 a)⟩
    have hfold : applySeq MVR.toUpdateSig MVR.init (chronological ops) = s :=
      (applySeq_perm_of_all_comm (D' := MVR.toUpdateSig) MVR_all_comm
        (chronological_perm ops) MVR.init).trans hf
    have hrel := fold_refines (chronological ops) (chronological_sorted ops)
      (fun e he n hn => issued_overwrite_lt exec (hin e ((hperm.2 e).mp he)) hn)
    rw [hfold] at hrel
    refine ⟨chronological ops, hperm, chronological_respects C E ops,
      chronological_legal exec hin hc hp, hrel, ?_⟩
    intro q
    apply Set.ext
    intro value
    change (∃ n, s.1 (n, value) = true ∧ s.2 n = false) ↔
      queryValues (clientSpec.run (chronological ops)) value
    unfold queryValues
    exact exists_congr (fun n => (hrel (n, value)).symm)

noncomputable def verified : VerifiedMRDT MVR where
  issuance := generation
  rc := rc
  replayAdequacy := replayAdequacy
  Spec := clientSpec
  Rel := stateRel
  sequentialCorrectness := clientSequentialCorrectness

theorem mvr_correct {C : Configuration MVR} (exec : CertifiedExecution MVR generation C) :
    IsSpecLinearizable MVR rc clientSpec stateRel C ∧
    (∀ v s E, C.ver v = some (s, E) → ∀ p : ℕ × ℕ,
      (s.1 p = true ∧ s.2 p.1 = false) ↔
        ∃ a ∈ E, a.1 = p.1 ∧ writeValue a = p.2 ∧ ∀ b ∈ E, ¬ C.vis a b) := by
  refine ⟨?_, fun _ _ _ hver p => version_maximal exec hver p⟩
  cases exec with
  | ordinary h => exact verified.correct h
  | virtual h => exact verified.correctV h

theorem linear_register {ops : List (Op MVROp)}
    (h : LinearMintHistory MVR generation.CanIssue ops) :
    MVR.query (applySeq MVR.toUpdateSig MVR.init ops) () =
      {v | mvrSpecFold ops = some v} := by
  apply Set.ext
  intro v
  apply mvr_seq_sound
  simpa [mvrOK, generation] using h.guarded

#print axioms verified
#print axioms mvr_correct
#print axioms linear_register

end Sal.MRDTs.Instances.MVR
